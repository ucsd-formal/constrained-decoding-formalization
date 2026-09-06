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
variable {α : Type u} {β : Type x} {Γ : Type y} {π : Type v} {σp : Type w} {σa : Type z}

variable
  [FinEnum σp] [FinEnum Γ] [FinEnum α] [FinEnum σa] [FinEnum π]
  [DecidableEq σp] [DecidableEq β] [DecidableEq Γ] [DecidableEq α] [DecidableEq π]

/-- The preprocessing table indexed by parser state and automaton state.

For each pair of states it stores:

* accepted next tokens,
* dependent realizable sequences,
* all realizable sequences accepted from the parser state with empty stack.
-/
abbrev PPTable (α σp σa Γ) := (σp → σa → (List α × List (List Γ) × List (List Γ)))

/-! ### Finset-based NFA evaluation -/

namespace FinsetNFA

/-- One NFA-style step on the control-state projection of a PDA. -/
def stepSet (p: PDA Γ π σp) (q : Finset σp) (s : Γ) : Finset σp :=
  Finset.biUnion q (fun q' => (p.step q' s).image fun x => x.2.2)

/-- Fold `stepSet` over a word. This is the finite-set presentation of the
parser overapproximation. -/
def evalFrom (p : PDA Γ π σp) (q : Finset σp) (s : List Γ) : Finset σp :=
  List.foldl (stepSet p) q s

end FinsetNFA

/-! ### PreprocessParser -/

/-- Precompute the parser/FST interaction table for grammar-constrained
decoding.

For each parser state `qp` and automaton state `qa`, this separates realizable
output sequences into immediately accepted ones, immediately rejected ones, and
dependent ones whose acceptance depends on the current stack.
-/
def PreprocessParser (fst_comp : FST α Γ σa) (p : PDA Γ π σp) : PPTable α σp σa Γ :=
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
def ComputeValidTokenMask (P : PDA Γ π σp) (itst : List Γ → σa → List α)
  (table : PPTable α σp σa Γ) (qa : σa) (qp : σp) (st : List π) : List α :=
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
abbrev GCDComb [Vocabulary α β] (spec : LexerSpec α Γ σa) :
    FST (Ch β) (Ch Γ) (Unit × LexingState σa) :=
  Detokenizing.BuildDetokLexer (V := Ch β) spec

/-- The EOS-augmented parser used by grammar-constrained decoding. -/
abbrev GCDParser (P : PDA Γ π σp) : PDA (Ch Γ) π (Ch σp) :=
  ParserWithEOS P

/-- The preprocessing table used by the full GCD checker. -/
abbrev GCDPPTable [Vocabulary α β] [FinEnum β] (P : PDA Γ π σp) (spec : LexerSpec α Γ σa) :
    PPTable (Ch β) (Ch σp) (Unit × LexingState σa) (Ch Γ) :=
  PreprocessParser (GCDComb (α := α) (β := β) spec) (GCDParser P)

/-- The inverse token-spanner table specialized to the full GCD construction. -/
abbrev GCDItst [Vocabulary α β] [FinEnum β] (spec : LexerSpec α Γ σa) :
    List (Ch Γ) → (Unit × LexingState σa) → List (Ch β) :=
  (BuildInverseTokenSpannerTable (GCDComb (α := α) (β := β) spec)).snd

/-! ### MaskChecker -/

/-- The generic mask checker built from a lexer/parser combination together
with its preprocessing artifacts. -/
def MaskChecker
  [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa]
  (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
  (pp_table : PPTable (Ch β) σp σa (Ch Γ))
  (itst : List (Ch Γ) → σa → List (Ch β)) : List β → Ch β → Bool :=
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
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (spec: LexerSpec α Γ σa) (parser0: PDA Γ π σp) : List β → Ch β → Bool :=
  MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (ParserWithEOS parser0)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS parser0))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd

/-- Semantic viable-prefix predicate for the full GCD construction. -/
@[reducible] def GCDViablePrefix
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (w : List β) : Prop :=
  ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (w.map ExtChar.char ++ suffix) = some (qa, gammas) ∧
    (ParserWithEOS P).evalFull gammas ≠ ∅
