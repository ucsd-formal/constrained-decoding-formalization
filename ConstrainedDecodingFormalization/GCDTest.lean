import ConstrainedDecodingFormalization.GrammarConstrainedDecoding
import ConstrainedDecodingFormalization.Checker
import ConstrainedDecodingFormalization.RealizableSequence
import Mathlib.Tactic

/-!
# GCDTest

This file instantiates the full grammar-constrained decoding pipeline with a
small JSON-like language.  The example is intentionally finite: the lexer reads
an abstract character alphabet with one digit class and one string-content
class, and the parser recognizes a shallow JSON shape:

* values are strings, numbers, booleans, nulls, objects, or arrays;
* objects contain string keys, colons, values, and comma-separated members;
* arrays contain comma-separated values;
* newline is the distinguished universal separator token ignored by the parser.

Object and array elements are primitive values in this compact parser; full
recursive nesting would require a larger parser-prunedness proof.  This is not a
full JSON compliance suite, but it exercises the same lexer, parser, vocabulary,
preprocessing table, and GCD correctness theorem used by the main development.
-/

namespace JSONExample

/-- Abstract JSON character alphabet. -/
abbrev JChar := Fin 19

namespace JChar

abbrev nl : JChar := 0
abbrev lbrace : JChar := 1
abbrev rbrace : JChar := 2
abbrev lbracket : JChar := 3
abbrev rbracket : JChar := 4
abbrev colon : JChar := 5
abbrev comma : JChar := 6
abbrev quote : JChar := 7
abbrev str : JChar := 8
abbrev digit : JChar := 9
abbrev t : JChar := 10
abbrev r : JChar := 11
abbrev u : JChar := 12
abbrev e : JChar := 13
abbrev f : JChar := 14
abbrev a : JChar := 15
abbrev l : JChar := 16
abbrev s : JChar := 17
abbrev n : JChar := 18

end JChar

/-- Terminals emitted by the JSON lexer. -/
abbrev JTok := Fin 12

namespace JTok

abbrev lbrace : JTok := 0
abbrev rbrace : JTok := 1
abbrev lbracket : JTok := 2
abbrev rbracket : JTok := 3
abbrev colon : JTok := 4
abbrev comma : JTok := 5
abbrev string : JTok := 6
abbrev number : JTok := 7
abbrev trueLit : JTok := 8
abbrev falseLit : JTok := 9
abbrev nullLit : JTok := 10
abbrev ws : JTok := 11

end JTok

/-- States of the JSON lexer DFA. -/
abbrev JLexState := Fin 24

namespace JLexState

abbrev start : JLexState := 0
abbrev white : JLexState := 1
abbrev lbrace : JLexState := 2
abbrev rbrace : JLexState := 3
abbrev lbracket : JLexState := 4
abbrev rbracket : JLexState := 5
abbrev colon : JLexState := 6
abbrev comma : JLexState := 7
abbrev stringBody : JLexState := 8
abbrev stringDone : JLexState := 9
abbrev number : JLexState := 10
abbrev t : JLexState := 11
abbrev tr : JLexState := 12
abbrev tru : JLexState := 13
abbrev trueDone : JLexState := 14
abbrev f : JLexState := 15
abbrev fa : JLexState := 16
abbrev fal : JLexState := 17
abbrev fals : JLexState := 18
abbrev falseDone : JLexState := 19
abbrev n : JLexState := 20
abbrev nu : JLexState := 21
abbrev nul : JLexState := 22
abbrev nullDone : JLexState := 23

end JLexState

/-- A JSON-ish lexer DFA.

Newline is the one distinguished whitespace character.  Strings are modeled as
`"` followed by zero or more abstract string-content characters and a closing
`"`, and numbers are nonempty runs of the abstract digit character.
-/
def jsonFSA : FSA JChar JLexState where
  start := JLexState.start
  step := fun q c =>
    match q, c with
    | 0, 0 => some JLexState.white
    | 1, 0 => some JLexState.white
    | 0, 1 => some JLexState.lbrace
    | 0, 2 => some JLexState.rbrace
    | 0, 3 => some JLexState.lbracket
    | 0, 4 => some JLexState.rbracket
    | 0, 5 => some JLexState.colon
    | 0, 6 => some JLexState.comma
    | 0, 7 => some JLexState.stringBody
    | 8, 8 => some JLexState.stringBody
    | 8, 7 => some JLexState.stringDone
    | 0, 9 => some JLexState.number
    | 10, 9 => some JLexState.number
    | 0, 10 => some JLexState.t
    | 11, 11 => some JLexState.tr
    | 12, 12 => some JLexState.tru
    | 13, 13 => some JLexState.trueDone
    | 0, 14 => some JLexState.f
    | 15, 15 => some JLexState.fa
    | 16, 16 => some JLexState.fal
    | 17, 17 => some JLexState.fals
    | 18, 13 => some JLexState.falseDone
    | 0, 18 => some JLexState.n
    | 20, 12 => some JLexState.nu
    | 21, 16 => some JLexState.nul
    | 22, 16 => some JLexState.nullDone
    | _, _ => none
  accept := [
    JLexState.white,
    JLexState.lbrace,
    JLexState.rbrace,
    JLexState.lbracket,
    JLexState.rbracket,
    JLexState.colon,
    JLexState.comma,
    JLexState.stringDone,
    JLexState.number,
    JLexState.trueDone,
    JLexState.falseDone,
    JLexState.nullDone
  ]

/-- Terminal labels for accepting lexer states. -/
def jsonTerm : JLexState → Option JTok
  | 1 => some JTok.ws
  | 2 => some JTok.lbrace
  | 3 => some JTok.rbrace
  | 4 => some JTok.lbracket
  | 5 => some JTok.rbracket
  | 6 => some JTok.colon
  | 7 => some JTok.comma
  | 9 => some JTok.string
  | 10 => some JTok.number
  | 14 => some JTok.trueLit
  | 19 => some JTok.falseLit
  | 23 => some JTok.nullLit
  | _ => none

def jsonTerm_hterm : ∀ q, q ∈ jsonFSA.accept ↔ (jsonTerm q).isSome := by
  native_decide

def jsonTerm_inj :
    ∀ q₁ q₂ t, jsonTerm q₁ = some t ∧ jsonTerm q₂ = some t → q₁ = q₂ := by
  native_decide

def jsonTerm_surj : ∀ t, ∃ q, jsonTerm q = some t := by
  native_decide

/-- JSON lexer specification. -/
def jsonLexer : LexerSpec JChar JTok JLexState where
  automaton := jsonFSA
  term := jsonTerm
  hterm := jsonTerm_hterm
  term_inj := jsonTerm_inj
  term_surj := jsonTerm_surj

/-- Parser control states for the JSON PDA. -/
abbrev JParserState := Fin 8

namespace JParserState

abbrev topValue : JParserState := 0
abbrev done : JParserState := 1
abbrev arrayValueOrEnd : JParserState := 2
abbrev arrayAfterValue : JParserState := 3
abbrev objectKeyOrEnd : JParserState := 4
abbrev objectColon : JParserState := 5
abbrev objectValue : JParserState := 6
abbrev objectAfterValue : JParserState := 7

end JParserState

/-- The shallow JSON parser does not need stack symbols; the PDA stack is
kept as a singleton type to instantiate the generic parser interface. -/
abbrev JStack := Fin 1

namespace JStack

abbrev unit : JStack := 0

end JStack

def jsonPrimitive (t : JTok) : Bool :=
  t = JTok.string || t = JTok.number || t = JTok.trueLit ||
    t = JTok.falseLit || t = JTok.nullLit

/-- A PDA for a shallow JSON subset over the lexer terminals.

The grammar includes primitive top-level values, arrays of primitive values,
and objects whose keys are strings and whose values are primitive values.  This
keeps the example compact while still exercising the JSON lexer, object/array
structure, separators, and parser-side whitespace identity assumption.

The transition on `JTok.ws` is exactly the identity transition required by the
GCD whitespace assumption.  All structural states therefore ignore newline
tokens.
-/
def jsonPDA : PDA JTok JStack JParserState where
  start := JParserState.topValue
  step := fun q t =>
    if t = JTok.ws then
      {([], [], q)}
    else
      match q, t with
      | 0, 0 => {([], [], JParserState.objectKeyOrEnd)}
      | 0, 2 => {([], [], JParserState.arrayValueOrEnd)}
      | 0, 6 => {([], [], JParserState.done)}
      | 0, 7 => {([], [], JParserState.done)}
      | 0, 8 => {([], [], JParserState.done)}
      | 0, 9 => {([], [], JParserState.done)}
      | 0, 10 => {([], [], JParserState.done)}
      | 2, 3 => {([], [], JParserState.done)}
      | 2, 6 => {([], [], JParserState.arrayAfterValue)}
      | 2, 7 => {([], [], JParserState.arrayAfterValue)}
      | 2, 8 => {([], [], JParserState.arrayAfterValue)}
      | 2, 9 => {([], [], JParserState.arrayAfterValue)}
      | 2, 10 => {([], [], JParserState.arrayAfterValue)}
      | 3, 3 => {([], [], JParserState.done)}
      | 3, 5 => {([], [], JParserState.arrayValueOrEnd)}
      | 4, 1 => {([], [], JParserState.done)}
      | 4, 6 => {([], [], JParserState.objectColon)}
      | 5, 4 => {([], [], JParserState.objectValue)}
      | 6, 6 => {([], [], JParserState.objectAfterValue)}
      | 6, 7 => {([], [], JParserState.objectAfterValue)}
      | 6, 8 => {([], [], JParserState.objectAfterValue)}
      | 6, 9 => {([], [], JParserState.objectAfterValue)}
      | 6, 10 => {([], [], JParserState.objectAfterValue)}
      | 7, 1 => {([], [], JParserState.done)}
      | 7, 5 => {([], [], JParserState.objectKeyOrEnd)}
      | _, _ => {}
  accept := {JParserState.done}

/-- Composite vocabulary tokens in addition to singleton character tokens. -/
abbrev JCompositeVocab := Fin 7

namespace JCompositeVocab

abbrev emptyString : JCompositeVocab := 0
abbrev sampleString : JCompositeVocab := 1
abbrev twoDigits : JCompositeVocab := 2
abbrev trueText : JCompositeVocab := 3
abbrev falseText : JCompositeVocab := 4
abbrev nullText : JCompositeVocab := 5
abbrev blankLine : JCompositeVocab := 6

end JCompositeVocab

/-- Example token vocabulary.  Singleton character tokens are available through
`Sum.inl`, while the right summand supplies a few realistic multi-character LLM
tokens such as `"x"`, `true`, `false`, and `null`.
-/
abbrev JVocab := JChar ⊕ JCompositeVocab

local instance (priority := 1001) : BEq JVocab := instBEqOfDecidableEq

instance : Vocabulary JChar JVocab where
  flatten
    | Sum.inl c => [c]
    | Sum.inr 0 => [JChar.quote, JChar.quote]
    | Sum.inr 1 => [JChar.quote, JChar.str, JChar.quote]
    | Sum.inr 2 => [JChar.digit, JChar.digit]
    | Sum.inr 3 => [JChar.t, JChar.r, JChar.u, JChar.e]
    | Sum.inr 4 => [JChar.f, JChar.a, JChar.l, JChar.s, JChar.e]
    | Sum.inr 5 => [JChar.n, JChar.u, JChar.l, JChar.l]
    | Sum.inr 6 => [JChar.nl, JChar.nl]
  embed := Sum.inl
  fe := by
    intro a
    rfl
  empty := by
    intro b
    cases b with
    | inl c =>
        simp
    | inr c =>
        fin_cases c <;> simp

/-- A completion word from each parser state to an accepting state. -/
def parserFinish : JParserState → List JTok
  | 0 => [JTok.nullLit]
  | 1 => []
  | 2 => [JTok.rbracket]
  | 3 => [JTok.rbracket]
  | 4 => [JTok.rbrace]
  | 5 => [JTok.colon, JTok.nullLit, JTok.rbrace]
  | 6 => [JTok.nullLit, JTok.rbrace]
  | 7 => [JTok.rbrace]

lemma parserFinish_acceptsFrom (q : JParserState) (st : List JStack) :
    parserFinish q ∈ jsonPDA.acceptsFrom q st := by
  simp only [PDA.acceptsFrom]
  refine ⟨JParserState.done, ?_, by simp [jsonPDA, JParserState.done]⟩
  simp only [Finset.mem_image]
  refine ⟨(JParserState.done, st), ?_, rfl⟩
  fin_cases q <;>
    simp [parserFinish, jsonPDA, PDA.evalFrom, PDA.fullStep,
      JTok.nullLit, JTok.rbracket, JTok.rbrace, JTok.colon,
      JTok.ws,
      JParserState.done, JParserState.arrayValueOrEnd,
      JParserState.arrayAfterValue, JParserState.objectKeyOrEnd,
      JParserState.objectColon, JParserState.objectValue,
      JParserState.objectAfterValue, List.isPrefixOf?]

def jsonPDA_pruned : jsonPDA.pruned := by
  intro q st _hreach
  exact ⟨parserFinish q, parserFinish_acceptsFrom q st⟩

def jsonLexer_hempty : [] ∉ jsonLexer.automaton.accepts := by
  native_decide

def jsonLexSuffix : JLexState → List JChar
  | 0 => [JChar.nl]
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => [JChar.quote]
  | 9 => []
  | 10 => []
  | 11 => [JChar.r, JChar.u, JChar.e]
  | 12 => [JChar.u, JChar.e]
  | 13 => [JChar.e]
  | 14 => []
  | 15 => [JChar.a, JChar.l, JChar.s, JChar.e]
  | 16 => [JChar.l, JChar.s, JChar.e]
  | 17 => [JChar.s, JChar.e]
  | 18 => [JChar.e]
  | 19 => []
  | 20 => [JChar.u, JChar.l, JChar.l]
  | 21 => [JChar.l, JChar.l]
  | 22 => [JChar.l]
  | 23 => []
  | _ => []

def jsonLexTarget : JLexState → JLexState
  | 0 => JLexState.white
  | 1 => JLexState.white
  | 2 => JLexState.lbrace
  | 3 => JLexState.rbrace
  | 4 => JLexState.lbracket
  | 5 => JLexState.rbracket
  | 6 => JLexState.colon
  | 7 => JLexState.comma
  | 8 => JLexState.stringDone
  | 9 => JLexState.stringDone
  | 10 => JLexState.number
  | 11 => JLexState.trueDone
  | 12 => JLexState.trueDone
  | 13 => JLexState.trueDone
  | 14 => JLexState.trueDone
  | 15 => JLexState.falseDone
  | 16 => JLexState.falseDone
  | 17 => JLexState.falseDone
  | 18 => JLexState.falseDone
  | 19 => JLexState.falseDone
  | 20 => JLexState.nullDone
  | 21 => JLexState.nullDone
  | 22 => JLexState.nullDone
  | 23 => JLexState.nullDone
  | _ => JLexState.white

def jsonLexPrefix : JLexState → List JChar
  | 0 => []
  | 1 => [JChar.nl]
  | 2 => [JChar.lbrace]
  | 3 => [JChar.rbrace]
  | 4 => [JChar.lbracket]
  | 5 => [JChar.rbracket]
  | 6 => [JChar.colon]
  | 7 => [JChar.comma]
  | 8 => [JChar.quote]
  | 9 => [JChar.quote, JChar.quote]
  | 10 => [JChar.digit]
  | 11 => [JChar.t]
  | 12 => [JChar.t, JChar.r]
  | 13 => [JChar.t, JChar.r, JChar.u]
  | 14 => [JChar.t, JChar.r, JChar.u, JChar.e]
  | 15 => [JChar.f]
  | 16 => [JChar.f, JChar.a]
  | 17 => [JChar.f, JChar.a, JChar.l]
  | 18 => [JChar.f, JChar.a, JChar.l, JChar.s]
  | 19 => [JChar.f, JChar.a, JChar.l, JChar.s, JChar.e]
  | 20 => [JChar.n]
  | 21 => [JChar.n, JChar.u]
  | 22 => [JChar.n, JChar.u, JChar.l]
  | 23 => [JChar.n, JChar.u, JChar.l, JChar.l]
  | _ => []

def jsonLexer_pruned : jsonLexer.automaton.pruned := by
  intro q
  constructor
  · refine ⟨jsonLexSuffix q, jsonLexTarget q, ?_, ?_⟩
    · fin_cases q <;> native_decide
    · fin_cases q <;> native_decide
  · refine ⟨jsonLexPrefix q, ?_⟩
    fin_cases q <;> native_decide

def jsonLexer_whitespace :
    Detokenizing.WhitespaceAssumption jsonLexer
      JChar.lbrace JChar.nl JLexState.lbrace JLexState.white := by
  unfold Detokenizing.WhitespaceAssumption
  constructor
  · native_decide
  constructor
  · intro s t
    fin_cases s <;> fin_cases t <;> native_decide
  constructor
  · intro t ht
    fin_cases t
    · exact (ht rfl).elim
    all_goals native_decide
  constructor
  · intro q hq
    fin_cases q
    · exact (hq.1 rfl).elim
    · exact (hq.2 rfl).elim
    all_goals native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

def jsonParser_ignores_ws : ParserIgnoresTerminal jsonPDA JTok.ws := by
  intro q
  fin_cases q <;> simp [jsonPDA, JTok.ws]

def jsonGCDWhitespaceAssumption :
    GCDWhitespaceAssumption jsonLexer jsonPDA
      JChar.lbrace JChar.nl JLexState.lbrace JLexState.white := by
  refine ⟨jsonLexer_whitespace, ?_⟩
  simpa [Detokenizing.whitespaceTerminal, jsonLexer, jsonTerm, JLexState.white,
    JTok.ws] using jsonParser_ignores_ws

/-- The full assumptions needed by the GCD productivity and correctness
theorems for the JSON lexer/parser. -/
def jsonGCDAssumptions :
    GCDAssumptions jsonLexer jsonPDA
      JChar.lbrace JChar.nl JLexState.lbrace JLexState.white where
  hempty := jsonLexer_hempty
  lexer_pruned := jsonLexer_pruned
  parser_pruned := jsonPDA_pruned
  whitespace := jsonGCDWhitespaceAssumption

/-- The detokenizing lexer FST built from the JSON lexer. -/
def jsonFullFST : FST (Ch JVocab) (Ch JTok) (Unit × LexingState JLexState) :=
  Detokenizing.BuildDetokLexer (V := Ch JVocab) jsonLexer

/-- The full grammar-constrained checker for the JSON example. -/
def jsonChecker : List JVocab → Ch JVocab → Bool := GCDChecker jsonLexer jsonPDA

/-- The EOS-augmented parser used by the checker. -/
def jsonParserWithEOS := ParserWithEOS jsonPDA

/-- The preprocessing table associated to the JSON FST and parser. -/
def jsonPP := PreprocessParser jsonFullFST jsonParserWithEOS

/-- The final correctness theorem instantiated for the JSON lexer/parser. -/
theorem jsonChecker_correct :
    checkerCorrect (β := JVocab) jsonChecker (TargetLanguage jsonLexer jsonPDA) :=
  by
    simpa [jsonChecker] using
      (GCDChecker_correct (α := JChar) (β := JVocab) (Γ := JTok)
        (π := JStack) (σp := JParserState) (σa := JLexState)
        jsonLexer jsonPDA jsonGCDAssumptions)

/-- Path independence also specializes to the JSON checker. -/
theorem jsonChecker_pathIndependent :
    checkerPathIndependent (α := JChar) (β := JVocab)
      jsonChecker (Vocabulary.flatten (α := JChar)) :=
  by
    simpa [jsonChecker] using
      (GCDChecker_pathIndependent (α := JChar) (β := JVocab) (Γ := JTok)
        (π := JStack) (σp := JParserState) (σa := JLexState)
        jsonLexer jsonPDA jsonGCDAssumptions)

#eval JChar.nl :: [JChar.nl] ∈ jsonFSA.accepts
#eval [JChar.quote, JChar.str, JChar.quote] ∈ jsonFSA.accepts
#eval [JChar.digit, JChar.digit] ∈ jsonFSA.accepts
#eval [JChar.t, JChar.r, JChar.u, JChar.e] ∈ jsonFSA.accepts
#eval [JChar.f, JChar.a, JChar.l, JChar.s, JChar.e] ∈ jsonFSA.accepts
#eval [JChar.n, JChar.u, JChar.l, JChar.l] ∈ jsonFSA.accepts

#eval jsonPDA.evalFrom {(jsonPDA.start, [])} [JTok.nullLit]
#eval jsonPDA.evalFrom {(jsonPDA.start, [])}
  [JTok.lbrace, JTok.string, JTok.colon, JTok.number,
   JTok.comma, JTok.string, JTok.colon, JTok.falseLit, JTok.rbrace]

#eval jsonFullFST.eval
  ([Sum.inr JCompositeVocab.sampleString,
    Sum.inl JChar.nl,
    Sum.inr JCompositeVocab.trueText].map ExtChar.char ++ [.eos])

#eval checkerAllows jsonChecker []
#eval checkerAllows jsonChecker [Sum.inr JCompositeVocab.nullText]
#eval checkerAccepts jsonChecker [Sum.inr JCompositeVocab.nullText]
#eval checkerAccepts jsonChecker
  [Sum.inl JChar.lbracket,
   Sum.inr JCompositeVocab.sampleString,
   Sum.inl JChar.comma,
   Sum.inr JCompositeVocab.twoDigits,
   Sum.inl JChar.rbracket]

end JSONExample
