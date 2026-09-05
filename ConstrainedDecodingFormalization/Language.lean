import Mathlib.Computability.Language

/-!
# Language helpers

At the moment this file only adds the prefix-closure operation, which is used
to relate executable checkers to their intermediate-language semantics.
-/
universe u
variable {Input : Type u}

/-- The prefix closure of a language.

A word lies in `l.prefixes` if it can be extended to some word of `l`. This is
the language-level notion matched by the checker-side "intermediate language"
used later in the grammar-constrained decoding pipeline.
-/
def Language.prefixes (l : Language Input) : Language Input :=
  {w | ∃ v ∈ l, w <+: v}
