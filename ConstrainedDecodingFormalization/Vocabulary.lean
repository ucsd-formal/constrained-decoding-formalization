class Vocabulary ( α: Type u ) ( β: Type v ) [ BEq α ] [ BEq β ] where
  flatten : β → List α
  embed: α → β
  eos: β

  fe: ∀ a, flatten (embed a) = [a]
  empty: ∀ b, flatten b = [] ↔ b = eos
