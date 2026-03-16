import ConstrainedDecodingFormalization.GrammarConstrainedDecoding
import ConstrainedDecodingFormalization.Checker
import ConstrainedDecodingFormalization.RealizableSequence
import Mathlib.Tactic

-- Example finite types
abbrev Vocab := Fin 5
abbrev Chr := Fin 3
abbrev Digit := Fin 2
abbrev LexerState := Fin 3
abbrev ParserState := Fin 2
abbrev StackSym := Fin 2


-- Lexer automaton that reads single digit
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

def termMap : LexerState → Option Digit
| 1 => some 0
| 2 => some 1
| _ => none

def hterm_proof : ∀ s, s ∈ simpleFSA.accept ↔ (termMap s).isSome :=
  by
    intro s
    simp_all [simpleFSA, termMap]
    split <;> simp_all

def term_inj_proof : ∀ s₁ s₂ t, termMap s₁ = some t ∧ termMap s₂ = some t → s₁ = s₂ :=
  by
    intros s₁ s₂ t h
    fin_cases s₁ <;> (fin_cases s₂ <;> first | simp_all [termMap])
    all_goals (have ⟨u, v⟩ := h; rw[←u] at v; contradiction)

def term_surj_proof : ∀ t, ∃ s, termMap s = some t :=
  by
    intro t
    fin_cases t
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩


def simpleLexer : LexerSpec Chr Digit LexerState :=
{
  automaton := simpleFSA,
  term := termMap,
  hterm := hterm_proof,
  term_inj := term_inj_proof,
  term_surj := term_surj_proof
}

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

def full_fst : FST (Ch Vocab) (Ch Digit) (Unit × LexingState LexerState) :=
  Detokenizing.BuildDetokLexer (V := Ch Vocab) simpleLexer
def checker : List Vocab → Ch Vocab → Bool := GCDChecker simpleLexer simplePDA
def parser := ParserWithEOS simplePDA
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
