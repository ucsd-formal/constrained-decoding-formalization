import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FinEnum
import Mathlib.Tactic.Linarith

/-- Extend an alphabet with an explicit end-of-sequence symbol.

This is the ambient character type used throughout the development to model
inputs and outputs that may be terminated by `eos`. Higher-level lexer and
checker constructions work over `Ch Input` rather than bare `Input` for exactly this
reason.
-/
inductive ExtChar (Input : Type u)
| char : Input → ExtChar Input
| eos  : ExtChar Input
deriving DecidableEq, Repr

/-- `ExtChar Input` is inhabited by the EOS symbol. -/
instance {Input} : Inhabited (ExtChar Input) := ⟨ExtChar.eos⟩

/-- Coerce a plain symbol into the corresponding non-EOS extended symbol. -/
instance {Input} : Coe (Input) (ExtChar Input) := ⟨fun a => ExtChar.char a⟩

/-- If `Input` is finite and enumerable, then so is `ExtChar Input`, with one extra
element representing EOS. -/
instance {Input} [e: FinEnum Input] : FinEnum (ExtChar Input) where
  card := FinEnum.card Input + 1
  equiv :=
    let e := e.equiv
    { toFun := fun x =>
        match x with
        | ExtChar.eos     => ⟨FinEnum.card Input, Nat.lt_succ_self _⟩
        | ExtChar.char a  => ⟨e a, Nat.lt_succ_of_lt (Fin.is_lt (e a))⟩
      invFun := fun i =>
        if h : i.val < FinEnum.card Input then ExtChar.char (e.symm ⟨i.val, h⟩)
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
        by_cases h : i < FinEnum.card Input
        · simp [h]
        · have : i = FinEnum.card Input := by
            linarith
          subst this
          simp
      }
  decEq := by infer_instance

/-- Notation for the EOS-extended version of an alphabet. -/
abbrev Ch := ExtChar
