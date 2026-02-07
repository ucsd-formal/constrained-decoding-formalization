class Vocabulary ( α: Type u ) ( β: Type v ) [ BEq α ] where
  flatten : β → List α
  embed: α → β

  -- singleton assumption
  fe: ∀ a, flatten (embed a) = [a]
  empty: ∀ b, flatten b ≠ []
