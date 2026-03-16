import ConstrainedDecodingFormalization.GrammarConstrainedDecoding
import ConstrainedDecodingFormalization.Checker
import ConstrainedDecodingFormalization.RealizableSequence
import Mathlib.Tactic

/-!
# GCDTest

This file is a small worked example of the full grammar-constrained decoding
pipeline. It instantiates a lexer, parser, vocabulary, preprocessing table, and
checker on tiny finite types so the constructions in the main development can
be inspected with `#eval`.
-/

/-- Example token vocabulary. -/
abbrev Vocab := Fin 5
/-- Example character alphabet. -/
abbrev Chr := Fin 3
/-- Example terminal alphabet emitted by the lexer. -/
abbrev Digit := Fin 2
/-- States of the example lexer automaton. -/
abbrev LexerState := Fin 3
/-- States of the example parser. -/
abbrev ParserState := Fin 2
/-- Stack symbols of the example parser. -/
abbrev StackSym := Fin 2


/-- A toy character automaton recognizing runs of one of two digits. -/
def simpleFSA : FSA Chr LexerState :=
{
  start := 0,
  step := fun s c =>
    match s, c with
    | 0, 0 => some 1
    | 0, 1 => some 2
    | 1, 0 => some 1
    | 2, 1 => some 2
    | _, _ => none,
  accept := [1, 2]
}

/-- The token emitted by each accepting lexer state. -/
def termMap : LexerState → Option Digit
| 1 => some 0
| 2 => some 1
| _ => none

/-- `termMap` is defined exactly on the accepting states of `simpleFSA`. -/
def hterm_proof : ∀ s, s ∈ simpleFSA.accept ↔ (termMap s).isSome :=
  by
    intro s
    simp_all [simpleFSA, termMap]
    split <;> simp_all

/-- Distinct accepting states emit distinct tokens in the example lexer. -/
def term_inj_proof : ∀ s₁ s₂ t, termMap s₁ = some t ∧ termMap s₂ = some t → s₁ = s₂ :=
  by
    intros s₁ s₂ t h
    fin_cases s₁ <;> (fin_cases s₂ <;> first | simp_all [termMap])
    all_goals (have ⟨u, v⟩ := h; rw[←u] at v; contradiction)

/-- Every example token is emitted by some accepting lexer state. -/
def term_surj_proof : ∀ t, ∃ s, termMap s = some t :=
  by
    intro t
    fin_cases t
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩


/-- The example lexer specification used by the downstream constructions. -/
def simpleLexer : LexerSpec Chr Digit LexerState :=
{
  automaton := simpleFSA,
  term := termMap,
  hterm := hterm_proof,
  term_inj := term_inj_proof,
  term_surj := term_surj_proof
}

/-- A toy PDA that pushes on token `0` and pops on token `1`. -/
def simplePDA : PDA Digit StackSym ParserState :=
{
  start := 0,
  step := fun s g =>
    match s, g with
    | 0, 0 => { ([], [1], 0) }
    | 0, 1 => { ([1], [], 0) }
    | _, _ => {}
  accept := {0}
}

/-- Example vocabulary whose tokens flatten to short character strings. -/
instance : Vocabulary Chr Vocab where
  flatten
    | 0 => [0]
    | 1 => [1]
    | 2 => [1, 1]
    | 3 => [2]
    | 4 => [0, 0]
  embed
    | 0 => 0
    | 1 => 1
    | 2 => 3
  fe := by
    intro a
    fin_cases a <;> rfl
  empty := by
    intro b
    fin_cases b <;> simp

/-- The detokenizing lexer FST built from `simpleLexer`. -/
def full_fst : FST (Ch Vocab) (Ch Digit) (Unit × LexingState LexerState) :=
  Detokenizing.BuildDetokLexer (V := Ch Vocab) simpleLexer
/-- The full grammar-constrained checker for the example. -/
def checker : List Vocab → Ch Vocab → Bool := GCDChecker simpleLexer simplePDA
/-- The EOS-augmented parser used by the checker. -/
def parser := ParserWithEOS simplePDA
/-- The preprocessing table associated to the example FST and parser. -/
def pp := PreprocessParser full_fst parser

#eval [0, 1] ∈ simpleFSA.accepts
#eval [0, 0] ∈ simpleFSA.accepts
#eval [1, 0] ∈ simpleFSA.accepts
#eval [1, 1] ∈ simpleFSA.accepts

#eval simplePDA.evalFrom {(simplePDA.start, [])} [0]
#eval simplePDA.evalFrom {(simplePDA.start, [])} [1]
#eval simplePDA.evalFrom { (simplePDA.start, [])} [0, 0, 1, 1]
#eval simplePDA.step 1  (1)
#eval simplePDA.fullStep {(1, [0, 1])} (1)
#eval full_fst.eval [.char 0, .char 0, .char 1, .eos]
#eval (BuildInverseTokenSpannerTable full_fst).1
#eval (BuildInverseTokenSpannerTable full_fst).2 [.char 0, .char 1] (.unit, LexingState.id 1)
#eval checkerAllows checker []
#eval checkerAllows checker [0]
#eval checkerAllows checker [1]
#eval checker [0] (.char 1)
#eval checkerAllows checker [0, 1]
#eval checkerAllows checker [1, 1, 0, 0, 0, 1, 1]
#eval checkerAccepts checker [0, 1, 0]
#eval checker [0] .eos
#eval pp parser.start (.unit, LexingState.id 1)
#eval parser.step parser.start .eos
