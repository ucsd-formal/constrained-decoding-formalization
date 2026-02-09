import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FinEnum
import Mathlib.Tactic.Linarith

/-- Extend character alphabet with EOS symbol-/
inductive ExtChar (α : Type u)
| char : α → ExtChar α
| eos  : ExtChar α
deriving BEq, DecidableEq, Repr

instance {α} : Coe (α) (ExtChar α) := ⟨fun a => ExtChar.char a⟩
instance {α} [e: FinEnum α] : FinEnum (ExtChar α) where
  card := FinEnum.card α + 1
  equiv :=
    let e := e.equiv
    { toFun := fun x =>
        match x with
        | ExtChar.eos     => ⟨FinEnum.card α, Nat.lt_succ_self _⟩
        | ExtChar.char a  => ⟨e a, Nat.lt_succ_of_lt (Fin.is_lt (e a))⟩
      invFun := fun i =>
        if h : i.val < FinEnum.card α then ExtChar.char (e.symm ⟨i.val, h⟩)
        else ExtChar.eos
      left_inv := by
        intro x
        cases x with
        | eos =>
          simp
        | char a =>
          simp
      right_inv := by
        intro ⟨i, hi⟩
        by_cases h : i < FinEnum.card α
        · simp [h]
        · have : i = FinEnum.card α := by
            linarith
          subst this
          simp
      }
  decEq := by infer_instance

abbrev Ch := ExtChar
