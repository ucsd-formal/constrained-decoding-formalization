import ConstrainedDecodingFormalization.PDA
import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.RealizableSequence
import ConstrainedDecodingFormalization.Vocabulary
-- Actual implementation of grammar constrained decoding

universe u v w x y z
variable { α : Type u } { β : Type x } { Γ : Type y } { π : Type v } { σp : Type w } { σa : Type z }

variable
  [ FinEnum σp ] [ FinEnum Γ ] [ FinEnum α ] [ FinEnum σa ] [ FinEnum π ]
  [ DecidableEq σp ] [DecidableEq β] [DecidableEq Γ ] [ DecidableEq α ] [ DecidableEq π ]

abbrev PPTable (α σp σa Γ) := (σp → σa → (List α × List (List Γ) × List (List Γ)))
-- todo use a better solution for extending the number of states by 1
def ParserWithEOS  (p: PDA Γ π σp) : PDA (Ch Γ) π (Ch σp) :=
  let start := ExtChar.char p.start
  let accept := ExtChar.eos
  let step := fun s c =>
    match s, c with
    | .char s, .char c =>
      (p.step s c).image (fun (spt, spr, s) => (spt, spr, ExtChar.char s))
    | .char s, .eos =>
      if s ∈ p.accept then
        { ([], [], accept) }
      else
        ∅
    | .eos, _ => {([], [], .eos)}

  ⟨start, step, {accept}⟩


-- TODO is there a better way to avoid this mess?
namespace FinsetNFA

def stepSet (p: PDA Γ π σp) (q : Finset σp) (s : Γ) : Finset σp :=
    Finset.biUnion q (fun q' => (p.step q' s).image fun x => x.2.2)

def evalFrom (p: PDA Γ π σp) (q : Finset σp) (s : List Γ) : Finset σp
  :=
   List.foldl (stepSet p) q s

omit [DecidableEq Γ] [DecidableEq π]
theorem finsetEvalFrom_iff_evalFrom (p: PDA Γ π σp) (q : Finset σp) (s : List Γ) :
  ∀ u, u ∈ FinsetNFA.evalFrom p q s ↔ u ∈ p.toNFA.evalFrom q s := by
  intro u
  simp[NFA.evalFrom, FinsetNFA.evalFrom]
  induction s generalizing q
  case nil => simp
  case cons h t ih =>
    simp[stepSet, NFA.stepSet]
    suffices
      (q.biUnion fun q' => Finset.image (fun x => x.2.2) (p.step q' h)) = (⋃ s ∈ q, p.toNFA.step s h) by
      rw[←this]
      apply ih
    exact Finset.coe_biUnion
end FinsetNFA

def PreprocessParser (fst_comp : FST α Γ σa) (p : PDA Γ π σp) : PPTable α σp σa Γ :=
  let (re, tist) := BuildInverseTokenSpannerTable fst_comp
  fun qp =>
    let accepted := re.filter (λ s => (p.evalFrom {(qp, [])} s) ≠  ∅)
    let rejected := re.filter (λ s => FinsetNFA.evalFrom p {qp} s ≠ ∅)

    let dependent := (re \ accepted) \ rejected
    fun qa =>
      let accepted_a := (accepted.map (fun tok => (tist tok qa))).foldl List.append []
      let accepted_a := accepted_a.dedup
      let dependent_a := dependent.filter (fun tok => (tist tok qa) ≠ [])
      let dependent_a := dependent_a.dedup
      (accepted_a, dependent_a, accepted)

def ComputeValidTokenMask (P : PDA Γ π σp) (itst : List Γ → σa → List α) (table : PPTable α σp σa Γ) (qa : σa) (qp : σp) (st : List π) : List α := Id.run do
  let mut accepted := (table qp qa).fst
  for d in (table qp qa).2.1 do
    if (P.evalFrom {(qp, st)} d) ≠ ∅ then
      accepted := accepted ++ (itst d qa)

  accepted.dedup


-- TODO use more consistent notions of variable names
/- lexer spec is the automata in terms of the characters
   we also have the actual tokens
   and then the parser
-/
def GCDChecker
   [FinEnum (Ch β)] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
   (spec: LexerSpec α Γ σa) (tokens: List (Token (Ch α) (Ch β))) (parser: PDA Γ π σp) : List β → Ch β → Bool :=
  let detok := Detokenizing.BuildDetokenizingFST tokens
  let fst := BuildLexingFST spec
  let comb := FST.compose detok fst

  let parser := ParserWithEOS parser

  let pp_table := PreprocessParser comb parser
  let ⟨_, itst⟩ := BuildInverseTokenSpannerTable comb

  fun curr cand =>
    match comb.eval curr with
    | none => false
    | some (q_fst, terms) =>
      let q_pda := parser.evalFrom {(parser.start, [])} terms
      let in_curr := q_pda.image
        (fun (q_parse, st) => (ComputeValidTokenMask parser itst pp_table q_fst q_parse st).contains cand)
      Finset.fold Bool.or false id in_curr

-- want to say that for any lexer state
-- any thing that starts with a realizable sequence is producible
-- and producible if and only if that's the case
theorem realizableSequencesComplete [Vocabulary α β] (spec: LexerSpec α Γ σa) :
  ∀ qa, ∃ := by
  sorry

-- a token is accepted if and only if in the current state
--
theorem accept_if_ComputedValidTokenMask
   [FinEnum (Ch β)] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
   (P : PDA Γ π σp) (spec: LexerSpec α Γ σa) (tokens: List (Token (Ch α) (Ch β))) :
  let detok := Detokenizing.BuildDetokenizingFST tokens
  let fst := BuildLexingFST spec
  let comb := FST.compose detok fst

  let parser := ParserWithEOS P

  let pp_table := PreprocessParser comb parser
  let ⟨_, itst⟩ := BuildInverseTokenSpannerTable comb
  ∀ qp st qa t,
    t ∈ (ComputeValidTokenMask parser itst pp_table qa qp st) ↔
    ∃ ts qa' gammas,
      comb.evalFrom qa (t :: ts) = some (qa', gammas) ∧
      gammas ∈ parser.acceptsFrom qp st := by sorry
