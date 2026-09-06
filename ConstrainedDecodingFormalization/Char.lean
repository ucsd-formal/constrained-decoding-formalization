import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FinEnum
import Mathlib.Tactic.Linarith

/-- Extend an alphabet with an explicit end-of-sequence symbol.

This is the ambient character type used throughout the development to model
inputs and outputs that may be terminated by `eos`. Higher-level lexer and
checker constructions work over `Ch α` rather than bare `α` for exactly this
reason.
-/
inductive ExtChar (α : Type u)
| char : α → ExtChar α
| eos  : ExtChar α
deriving DecidableEq, Repr

/-- `ExtChar α` is inhabited by the EOS symbol. -/
instance {α} : Inhabited (ExtChar α) := ⟨ExtChar.eos⟩

/-- Coerce a plain symbol into the corresponding non-EOS extended symbol. -/
instance {α} : Coe (α) (ExtChar α) := ⟨fun a => ExtChar.char a⟩

/-- If `α` is finite and enumerable, then so is `ExtChar α`, with one extra
element representing EOS. -/
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

/-- Notation for the EOS-extended version of an alphabet. -/
abbrev Ch := ExtChar
