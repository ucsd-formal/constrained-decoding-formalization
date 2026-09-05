import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.RealizableSequence
import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.ParserWithEOS

/-!
# Grammar-constrained decoding algorithm

This module contains the executable constructions used by the proof:

* the finite control-state approximation used during preprocessing;
* `PreprocessParser`, which separates always-accepted and stack-dependent
  realizable sequences;
* `ComputeValidTokenMask`;
* the specialized GCD checker assembled from the detokenizing lexer and
  EOS-augmented parser.

Proofs about these definitions live in `GrammarConstrainedDecoding.lean`.
-/

universe u v w x y z
variable {Input : Type u} {V : Type x} {Γ : Type y} {StackSym : Type v} {Qp : Type w} {Qa : Type z}

variable
  [FinEnum Qp] [FinEnum Γ] [FinEnum Input] [FinEnum Qa] [FinEnum StackSym]
  [DecidableEq Qp] [DecidableEq V] [DecidableEq Γ] [DecidableEq Input] [DecidableEq StackSym]

/-- The preprocessing table indexed by parser state and automaton state.

For each pair of states it stores:

* accepted next tokens,
* dependent realizable sequences,
* all realizable sequences accepted from the parser state with empty stack.
-/
abbrev PPTable (Input Qp Qa Γ) := (Qp → Qa → (List Input × List (List Γ) × List (List Γ)))

/-! ### Finset-based NFA evaluation -/

namespace FinsetNFA

/-- One NFA-style step on the control-state projection of a PDA. -/
def stepSet (p: PDA Γ StackSym Qp) (q : Finset Qp) (s : Γ) : Finset Qp :=
  Finset.biUnion q (fun q' => (p.step q' s).image fun x => x.2.2)

/-- Fold `stepSet` over a word. This is the finite-set presentation of the
parser overapproximation. -/
def evalFrom (p : PDA Γ StackSym Qp) (q : Finset Qp) (s : List Γ) : Finset Qp :=
  List.foldl (stepSet p) q s

end FinsetNFA

/-! ### PreprocessParser -/

/-- Precompute the parser/FST interaction table for grammar-constrained
decoding.

For each parser state `qp` and automaton state `qa`, this separates realizable
output sequences into immediately accepted ones, immediately rejected ones, and
dependent ones whose acceptance depends on the current stack.
-/
def PreprocessParser (fst_comp : FST Input Γ Qa) (p : PDA Γ StackSym Qp) : PPTable Input Qp Qa Γ :=
  let (re, tist) := BuildInverseTokenSpannerTable fst_comp
  fun qp =>
    let accepted := re.filter (λ s => (p.evalFrom {(qp, [])} s) ≠  ∅)
    let rejected := re.filter (λ s => FinsetNFA.evalFrom p {qp} s = ∅)

    let dependent := List.diff (List.diff re accepted) rejected
    fun qa =>
      let accepted_a := (accepted.map (fun tok => (tist tok qa))).foldl List.append []
      let accepted_a := accepted_a.dedup
      let dependent_a := dependent.filter (fun tok => (tist tok qa) ≠ [])
      let dependent_a := dependent_a.dedup
      (accepted_a, dependent_a, accepted)

/-! ### ComputeValidTokenMask -/

/-- Compute the valid next-token mask for a given parser state, automaton state,
and current parser stack. -/
def ComputeValidTokenMask (P : PDA Γ StackSym Qp) (itst : List Γ → Qa → List Input)
  (table : PPTable Input Qp Qa Γ) (qa : Qa) (qp : Qp) (st : List StackSym) : List Input :=
  let accepted := (table qp qa).fst
  let dependent := (table qp qa).2.1
  let accepted :=
    dependent.foldl
      (fun acc d =>
        if (P.evalFrom {(qp, st)} d) ≠ ∅ then
          acc ++ (itst d qa)
        else
          acc)
      accepted
  accepted.dedup

/-! ### Full GCD checker assembly -/

/-- The combined detokenizing lexer FST used by grammar-constrained decoding. -/
abbrev GCDComb [Vocabulary Input V] (spec : LexerSpec Input Γ Qa) :
    FST (Ch V) (Ch Γ) (Unit × LexingState Qa) :=
  Detokenizing.BuildDetokLexer (V := Ch V) spec

/-- The EOS-augmented parser used by grammar-constrained decoding. -/
abbrev GCDParser (P : PDA Γ StackSym Qp) : PDA (Ch Γ) StackSym (Ch Qp) :=
  ParserWithEOS P

/-- The preprocessing table used by the full GCD checker. -/
abbrev GCDPPTable [Vocabulary Input V] [FinEnum V] (P : PDA Γ StackSym Qp) (spec : LexerSpec Input Γ Qa) :
    PPTable (Ch V) (Ch Qp) (Unit × LexingState Qa) (Ch Γ) :=
  PreprocessParser (GCDComb (Input := Input) (V := V) spec) (GCDParser P)

/-- The inverse token-spanner table specialized to the full GCD construction. -/
abbrev GCDItst [Vocabulary Input V] [FinEnum V] (spec : LexerSpec Input Γ Qa) :
    List (Ch Γ) → (Unit × LexingState Qa) → List (Ch V) :=
  (BuildInverseTokenSpannerTable (GCDComb (Input := Input) (V := V) spec)).snd

/-! ### MaskChecker -/

/-- The generic mask checker built from a lexer/parser combination together
with its preprocessing artifacts. -/
def MaskChecker
  [BEq V] [BEq Γ] [BEq Qa] [LawfulBEq Qa]
  (comb : FST (Ch V) (Ch Γ) Qa) (parser : PDA (Ch Γ) StackSym Qp)
  (pp_table : PPTable (Ch V) Qp Qa (Ch Γ))
  (itst : List (Ch Γ) → Qa → List (Ch V)) : List V → Ch V → Bool :=
  fun curr cand =>
    match comb.eval (curr.map ExtChar.char) with
    | none => false
    | some (q_fst, terms) =>
      let q_pda := parser.evalFrom {(parser.start, [])} terms
      let in_curr := q_pda.image
        (fun (q_parse, st) => (ComputeValidTokenMask parser itst pp_table q_fst q_parse st).contains cand)
      Finset.fold Bool.or false id in_curr

/-! ### GCDChecker -/

/-- The end-to-end grammar-constrained checker associated to a lexer
specification and a parser. -/
@[reducible] def GCDChecker
  [BEq Input] [BEq V] [BEq Γ] [BEq Qa] [LawfulBEq Qa] [Vocabulary Input V]
  [DecidableEq Qa]
  [FinEnum V] [FinEnum Qp] [FinEnum Qa] [FinEnum StackSym] [FinEnum Input]
  (spec: LexerSpec Input Γ Qa) (parser0: PDA Γ StackSym Qp) : List V → Ch V → Bool :=
  MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch V) spec)
    (ParserWithEOS parser0)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch V) spec) (ParserWithEOS parser0))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch V) spec)).snd

/-- Semantic viable-prefix predicate for the full GCD construction. -/
@[reducible] def GCDViablePrefix
  [BEq Input] [BEq V] [BEq Γ] [BEq Qa] [LawfulBEq Qa] [Vocabulary Input V]
  [DecidableEq Qa]
  [FinEnum V] [FinEnum Qp] [FinEnum Qa] [FinEnum StackSym] [FinEnum Input]
  (spec : LexerSpec Input Γ Qa) (P : PDA Γ StackSym Qp) (w : List V) : Prop :=
  ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch V) spec).eval
      (w.map ExtChar.char ++ suffix) = some (qa, gammas) ∧
    (ParserWithEOS P).evalFull gammas ≠ ∅
