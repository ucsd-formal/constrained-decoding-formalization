import ConstrainedDecodingFormalization.Char

class Vocabulary ( α: Type u ) ( β: Type v ) [ BEq α ] where
  flatten : β → List α
  embed: α → β

  -- singleton assumption
  fe: ∀ a, flatten (embed a) = [a]
  empty: ∀ b, flatten b ≠ []

instance { α β } [BEq α] [b: Vocabulary α β] : Vocabulary (Ch α) (Ch β) where
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
