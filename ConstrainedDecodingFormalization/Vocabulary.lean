import ConstrainedDecodingFormalization.Char

/-!
# Vocabularies

This file provides the interface that lets higher-level constructions move
between token sequences and character sequences. It is used most heavily in the
detokenization layer of `Lexing` and in the final GCD checker assembly.
-/

/-- A vocabulary of tokens `β` over characters `α`.

`flatten` interprets a token as the character sequence it expands to, while
`embed` names the distinguished singleton tokens corresponding to individual
characters. The axioms express the singleton-token assumption used throughout
the constrained decoding formalization.
-/
class Vocabulary (α : Type u) (β : Type v) [BEq α] where
  flatten : β → List α
  embed : α → β

  -- singleton assumption
  fe : ∀ a, flatten (embed a) = [a]
  empty : ∀ b, flatten b ≠ []

/-- Extend a vocabulary to EOS-extended alphabets and tokens.

Plain tokens are mapped pointwise through `ExtChar.char`, while EOS is sent to
the singleton token `[eos]`. This is the instance used by the detokenizing FST
and checker constructions over `Ch α`.
-/
instance {α β} [DecidableEq α] [BEq α] [b : Vocabulary α β] : Vocabulary (Ch α) (Ch β) where
  flatten := fun x => match x with
    | ExtChar.char c => List.map ExtChar.char (b.flatten c)
    | ExtChar.eos    => [ExtChar.eos]
  embed := fun x => match x with
    | ExtChar.char c => ExtChar.char (b.embed c)
    | ExtChar.eos    => ExtChar.eos
  fe := by
    intro a
    cases a <;> simp [Vocabulary.fe]
  empty := by
    intro b
    cases b <;> simp [Vocabulary.empty]
