import ConstrainedDecodingFormalization.Language
import ConstrainedDecodingFormalization.Lexing
import Mathlib.Computability.Language

/-!
# Checker semantics

This file packages the executable interface expected of a token-level checker
and relates it to the language-theoretic notions used by the rest of the
development. The concrete checker built in
`GrammarConstrainedDecoding.lean` is shown to satisfy these interfaces.
-/
universe u v

variable {α : Type u} {β : Type v} [BEq α] [BEq β]

/-- A token-level checker.

Given a token prefix and a next symbol in the EOS-extended vocabulary, the
checker decides whether that extension is allowed.
-/
abbrev Checker (β) [BEq β] := List β → Ch β → Bool

/-- Auxiliary recursion implementing `checkerAllows` from left to right. -/
private def checkerAllowsHelper (c : Checker β) (w : List β) : Bool :=
  match w with
  | [] => true
  | v :: ts =>
    c ts.reverse v && checkerAllowsHelper c ts

/-- Whether every token in `w` is accepted incrementally by the checker. -/
def checkerAllows (c : Checker β) (w : List β) : Bool :=
  checkerAllowsHelper c w.reverse

/-- The empty token sequence is always allowed. -/
@[simp] theorem checkerAllows_nil (c : Checker β) : checkerAllows c [] = true := by
  simp [checkerAllows, checkerAllowsHelper]

/-- Unfolding `checkerAllows` on a snoc: the last token must be allowed and the prefix must itself be allowed. -/
theorem checkerAllows_snoc (c : Checker β) (w : List β) (v : β) :
    checkerAllows c (w ++ [v]) = (c w v && checkerAllows c w) := by
  simp only [checkerAllows, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append]
  simp [checkerAllowsHelper, List.reverse_reverse]

/-- Propositional form of `checkerAllows_snoc`. -/
theorem checkerAllows_snoc_iff (c : Checker β) (w : List β) (v : β) :
    checkerAllows c (w ++ [v]) ↔ checkerAllows c w ∧ c w v = true := by
  rw [checkerAllows_snoc]
  simp [Bool.and_eq_true, and_comm]

/-- Whether `w` is fully accepted: every token is allowed incrementally and the sequence may be terminated by EOS. -/
def checkerAccepts (c : Checker β) (w : List β) : Bool :=
  checkerAllows c w && c w .eos = true

/-- The language of prefixes that the checker permits incrementally. -/
def checkerIntermediateLanguage (c : Checker β) : Language β :=
  {bs | checkerAllows c bs}

/-- The language of complete token sequences accepted by the checker. -/
def checkerLanguage (c : Checker β) : Language β :=
  {bs | checkerAccepts c bs}

/-- Every allowed prefix can be extended to some accepted word. -/
def checkerAllowsTermination (c : Checker β) : Prop :=
  ∀ w, checkerAllows c w →
    ∃ w' : List β, checkerAccepts c w' ∧ w.isPrefixOf w'

/-- Checker decisions depend only on the flattened character content of a
prefix, not on the particular tokenization witnessing it. -/
def checkerPathIndependent (c : Checker β) (flatten : β → List α) : Prop :=
  ∀ w₁ w₂, w₁.flatMap flatten = w₂.flatMap flatten →
    checkerAllows c w₁ = checkerAllows c w₂

/-- Soundness package for executable checkers.

This says that the checker never gets stuck on an allowed prefix and that its
decisions respect tokenizations with the same underlying character string.
-/
def checkerSound (c : Checker β) (flatten : β → List α) : Prop :=
  checkerAllowsTermination c ∧ checkerPathIndependent c flatten

/-- Completeness package for executable checkers.

The checker recognizes exactly the target language, and its intermediate
language coincides with the prefix closure of that language.
-/
def checkerComplete (c : Checker β) (l : Language β) : Prop :=
  checkerLanguage c = l ∧ checkerIntermediateLanguage c = l.prefixes
