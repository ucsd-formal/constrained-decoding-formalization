import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.ParserWithEOS

/-!
# Assumptions for grammar-constrained decoding

This module packages the semantic assumptions used by the final checker
correctness theorem. The important whitespace condition has two parts:

* the lexer has a distinguished whitespace lexeme, supplied by
  `Detokenizing.WhitespaceAssumption`;
* the parser ignores the corresponding terminal at every state.

The old lexer restart condition is now derived from the whitespace package
instead of being exposed as a separate end-to-end assumption.
-/

universe u v w x y z
variable {α : Type u} {β : Type x} {Γ : Type y} {π : Type v} {σp : Type w} {σa : Type z}

variable
  [FinEnum σp] [FinEnum Γ] [FinEnum α] [FinEnum σa] [FinEnum π]
  [DecidableEq σp] [DecidableEq β] [DecidableEq Γ] [DecidableEq α] [DecidableEq π]

/-- A parser ignores a terminal if reading it from any parser state is exactly
the identity transition on both the parser state and stack. -/
def ParserIgnoresTerminal (P : PDA Γ π σp) (white : Γ) : Prop :=
  ∀ q : σp, P.step q white = {([], [], q)}

set_option linter.unusedSectionVars false in
/-- If the parser ignores `white`, then a one-symbol full step on `white` is the
identity on every singleton parser configuration. -/
lemma ParserIgnoresTerminal.fullStep_singleton
    (P : PDA Γ π σp) (white : Γ)
    (hignore : ParserIgnoresTerminal P white)
    (q : σp) (st : List π) :
    P.fullStep {(q, st)} white = {(q, st)} := by
  ext cfg
  constructor
  · intro hcfg
    simp only [PDA.fullStep, Finset.mem_biUnion, Finset.mem_singleton] at hcfg
    obtain ⟨⟨q₀, st₀⟩, hq₀, hstep⟩ := hcfg
    obtain ⟨rfl, rfl⟩ := hq₀
    rw [hignore q] at hstep
    simp only [Finset.mem_singleton] at hstep
    obtain ⟨⟨top, rep, dst⟩, htrans, hcfg'⟩ := hstep
    simp only [Prod.mk.injEq] at htrans
    obtain ⟨rfl, rfl, rfl⟩ := htrans
    simp [List.isPrefixOf?] at hcfg'
    exact Finset.mem_singleton.mpr hcfg'
  · intro hcfg
    have hcfg_eq : cfg = (q, st) := Finset.mem_singleton.mp hcfg
    subst cfg
    simp only [PDA.fullStep, Finset.mem_biUnion, Finset.mem_singleton]
    refine ⟨(q, st), rfl, ([], [], q), ?_, ?_⟩
    · rw [hignore q]
      simp
    · simp [List.isPrefixOf?]

set_option linter.unusedSectionVars false in
/-- If the parser ignores `white`, then a one-symbol full step on `white` is
the identity on every finite set of parser configurations. -/
lemma ParserIgnoresTerminal.fullStep_eq
    (P : PDA Γ π σp) (white : Γ)
    (hignore : ParserIgnoresTerminal P white)
    (S : Finset (σp × List π)) :
    P.fullStep S white = S := by
  rw [PDA.fullStep_biUnion]
  ext cfg
  constructor
  · intro hcfg
    rw [Finset.mem_biUnion] at hcfg
    obtain ⟨cfg₀, hcfg₀, hmem⟩ := hcfg
    rcases cfg₀ with ⟨q, st⟩
    have hstep := ParserIgnoresTerminal.fullStep_singleton P white hignore q st
    rw [hstep] at hmem
    have : cfg = (q, st) := Finset.mem_singleton.mp hmem
    simpa [this] using hcfg₀
  · intro hcfg
    rw [Finset.mem_biUnion]
    refine ⟨cfg, hcfg, ?_⟩
    rcases cfg with ⟨q, st⟩
    rw [ParserIgnoresTerminal.fullStep_singleton P white hignore q st]
    simp

section ParserIgnoresFilter

variable [BEq Γ] [LawfulBEq Γ]

set_option linter.unusedSectionVars false in
/-- Deleting a terminal ignored by the parser does not change PDA evaluation. -/
lemma ParserIgnoresTerminal.evalFrom_filter_ne
    (P : PDA Γ π σp) (white : Γ)
    (hignore : ParserIgnoresTerminal P white)
    (S : Finset (σp × List π)) (w : List Γ) :
    P.evalFrom S (w.filter (fun t => t != white)) = P.evalFrom S w := by
  induction w generalizing S with
  | nil =>
      simp [PDA.evalFrom]
  | cons h t ih =>
      by_cases hwhite : h = white
      · subst hwhite
        have hdrop :
            List.filter (fun t => t != h) (h :: t) =
              List.filter (fun t => t != h) t := by
          simp
        rw [hdrop]
        rw [PDA.evalFrom_cons, ParserIgnoresTerminal.fullStep_eq P h hignore S]
        exact ih S
      · simpa [hwhite, PDA.evalFrom_cons] using ih (P.fullStep S h)

set_option linter.unusedSectionVars false in
/-- Deleting a terminal ignored by the parser preserves acceptance from any
configuration. -/
lemma ParserIgnoresTerminal.acceptsFrom_filter_ne
    (P : PDA Γ π σp) (white : Γ)
    (hignore : ParserIgnoresTerminal P white)
    (q : σp) (st : List π) (w : List Γ) :
    w ∈ P.acceptsFrom q st →
      w.filter (fun t => t != white) ∈ P.acceptsFrom q st := by
  intro hacc
  simp only [PDA.acceptsFrom] at hacc ⊢
  obtain ⟨f, hfmem, hfacc⟩ := hacc
  refine ⟨f, ?_, hfacc⟩
  rw [ParserIgnoresTerminal.evalFrom_filter_ne P white hignore {(q, st)} w]
  exact hfmem

set_option linter.unusedSectionVars false in
/-- If a parser ignores `white`, then replacing a suffix by the same suffix
with ignored whitespace deleted preserves acceptance. -/
lemma ParserIgnoresTerminal.accepts_append_filter_ne
    (P : PDA Γ π σp) (white : Γ)
    (hignore : ParserIgnoresTerminal P white)
    (pre tail : List Γ) :
    pre ++ tail ∈ P.accepts →
      pre ++ tail.filter (fun t => t != white) ∈ P.accepts := by
  intro hacc
  simp only [PDA.accepts, PDA.acceptsFrom] at hacc ⊢
  obtain ⟨f, hfmem, hfacc⟩ := hacc
  refine ⟨f, ?_, hfacc⟩
  rw [PDA.evalFrom_append'] at hfmem
  rw [PDA.evalFrom_append']
  rw [ParserIgnoresTerminal.evalFrom_filter_ne P white hignore
    (P.evalFrom {(P.start, [])} pre) tail]
  exact hfmem

set_option linter.unusedSectionVars false in
/-- If a parser ignores `white`, then replacing a suffix by a version with
ignored whitespace inserted preserves acceptance. -/
lemma ParserIgnoresTerminal.accepts_append_of_filter_ne
    (P : PDA Γ π σp) (white : Γ)
    (hignore : ParserIgnoresTerminal P white)
    (pre tail filtered : List Γ)
    (hfilter : tail.filter (fun t => t != white) = filtered) :
    pre ++ filtered ∈ P.accepts →
      pre ++ tail ∈ P.accepts := by
  intro hacc
  simp only [PDA.accepts, PDA.acceptsFrom] at hacc ⊢
  obtain ⟨f, hfmem, hfacc⟩ := hacc
  refine ⟨f, ?_, hfacc⟩
  rw [PDA.evalFrom_append'] at hfmem
  rw [PDA.evalFrom_append']
  rw [← hfilter] at hfmem
  rw [ParserIgnoresTerminal.evalFrom_filter_ne P white hignore
    (P.evalFrom {(P.start, [])} pre) tail] at hfmem
  exact hfmem

end ParserIgnoresFilter

omit [DecidableEq Γ] in
/-- The EOS-augmented parser ignores the EOS-lifted whitespace terminal when
the original parser ignores the underlying whitespace terminal. -/
lemma ParserWithEOS_ignoresTerminal
    (P : PDA Γ π σp) (white : Γ)
    (hignore : ParserIgnoresTerminal P white) :
    ParserIgnoresTerminal (ParserWithEOS P) (ExtChar.char white) := by
  intro q
  cases q with
  | char s =>
      simp only [ParserWithEOS]
      rw [hignore s]
      ext tr
      constructor
      · intro htr
        simp only [Finset.mem_image, Finset.mem_singleton] at htr
        obtain ⟨⟨top, rep, dst⟩, hsrc, hdst⟩ := htr
        obtain ⟨rfl, rfl, rfl⟩ := hsrc
        simp [hdst]
      · intro htr
        simp only [Finset.mem_singleton] at htr
        subst htr
        simp
  | eos =>
      simp [ParserWithEOS]

/-- The full whitespace assumption used for productivity.

The lexer-side component is the existing `Detokenizing.WhitespaceAssumption`,
which isolates a distinguished whitespace terminal emitted by the lexer. The
parser-side component says that this terminal is ignored by the original parser:
from every parser state, reading the whitespace terminal has exactly the
identity transition on the parser state and stack. -/
def GCDWhitespaceAssumption
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  (tnonwhite twhite : α) (qnonwhite qwhite : σa) : Prop :=
  ∃ hlexer : Detokenizing.WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite,
    ParserIgnoresTerminal P
      (Detokenizing.whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hlexer)

/-- Assumptions used by the final GCD correctness and productivity interface. -/
structure GCDAssumptions
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  (tnonwhite twhite : α) (qnonwhite qwhite : σa) : Prop where
  hempty : [] ∉ spec.automaton.accepts
  lexer_pruned : spec.automaton.pruned
  parser_pruned : P.pruned
  whitespace : GCDWhitespaceAssumption spec P tnonwhite twhite qnonwhite qwhite

omit [FinEnum α] [DecidableEq σp] [DecidableEq α] [DecidableEq π]
  [DecidableEq β] [DecidableEq Γ] in
/-- The full whitespace assumption rederives the old lexer restart hypothesis. -/
lemma GCDWhitespaceAssumption.existsRestartChar
    {tnonwhite twhite : α} {qnonwhite qwhite : σa}
    (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
    (hempty : [] ∉ spec.automaton.accepts)
    (hws : GCDWhitespaceAssumption spec P tnonwhite twhite qnonwhite qwhite) :
    ∀ s ∈ spec.automaton.accept,
      ∃ c : α, spec.automaton.step s c = none ∧
        (spec.automaton.step spec.automaton.start c).isSome := by
  intro s hs
  obtain ⟨hlexer, _⟩ := hws
  obtain ⟨_, hwhite_step, hwhite_only, hnonwhite_no_white, _, hnonwhite_start, hdiff⟩ := hlexer
  by_cases hs_white : s = qwhite
  · subst hs_white
    refine ⟨tnonwhite, ?_, ?_⟩
    · exact hwhite_only tnonwhite (fun h => hdiff h.symm)
    · simp [hnonwhite_start]
  · refine ⟨twhite, ?_, ?_⟩
    · have hs_start : s ≠ spec.automaton.start := by
        intro h
        rw [h] at hs
        simp [FSA.accepts_iff] at hempty
        exact hempty hs
      exact hnonwhite_no_white s ⟨hs_start, hs_white⟩
    · have hstart_white : spec.automaton.step spec.automaton.start twhite = some qwhite := by
        exact (hwhite_step spec.automaton.start twhite).mpr (by simp)
      simp [hstart_white]
