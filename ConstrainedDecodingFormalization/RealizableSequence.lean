import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.RegularExpressionsToEpsilonNFA
import Mathlib.Data.FinEnum
import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Range

open Classical List RegularExpression


universe u v w x
variable {α : Type u} {Γ : Type v} { V : Type x } { σ0 σ1 σ2 : Type w}

abbrev State (α : Type u) := List α
abbrev Next (α : Type u) := List (State α)
abbrev Output (α : Type u):= List (List α)

abbrev Re (Γ : Type v) := List (List Γ)


section Symbols

variable
  [DecidableEq α] [DecidableEq σ0] [DecidableEq σ1] [DecidableEq σ2]
  [DecidableEq Γ] [BEq α] [BEq Γ]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ]

#check Language (Ch α)

def RealizableSequences (fst_comp : FST α Γ σ2) : Set (List Γ) :=
  -- all possible transitions, adjoined with singleton transitions afterwards
  { Ts' | ∃ q_0 t Ts q_1 T,
          fst_comp.step q_0 t = some (q_1, Ts) ∧
          T ∈ fst_comp.singleProducible q_1 ∧
          Ts' = Ts ++ [T] }

def InverseTokenSpannerTable (fst_comp : FST α Γ σ2) : List Γ → σ2 → (Set α) :=
  fun rs st =>
    if h : rs ≠ [] then
      let Ts := rs.dropLast
      let T := rs.getLast h
      { t | ∃ q_1,
            fst_comp.step st t = (some (q_1, Ts)) ∧
            T ∈ fst_comp.singleProducible q_1 }
    else ∅


variable [ q: FinEnum σ2 ] [ a: FinEnum α ] [ t: FinEnum Γ ]

def BuildInverseTokenSpannerTable
  (fst_comp : FST α Γ σ2) : Re Γ × (List Γ → σ2 → (List α)) := Id.run do
  let Q := q.toList
  let A := a.toList

  let re :=
    Q.flatMap (fun q =>
      A.flatMap ( fun c =>
        match fst_comp.step q c with
        | none => []
        | some (q', Ts) =>
          (fst_comp.computeSingleProducible q')
          |>.map (fun t => Ts ++ [t])
      )
    )
    |>.eraseDups

  let tinv := fun rs s =>
    if h : rs ≠ [] then
      let Ts := rs.dropLast
      let T := rs.getLast h
      A.filter (fun c =>
        match fst_comp.step s c with
        | none => false
        | some (q', Ts') => (fst_comp.computeSingleProducible q').contains T && Ts' = Ts
      )
    else []

  (re, tinv)

def itst_fst_eq_rs (fst_comp : FST α Γ σ2) : (BuildInverseTokenSpannerTable fst_comp).fst.toFinset = RealizableSequences fst_comp := by
  sorry

def itst_snd_eq_itst (fst_comp : FST α Γ σ2) :
    ∀ rs s, ((BuildInverseTokenSpannerTable fst_comp).snd rs s).toFinset = InverseTokenSpannerTable fst_comp rs s := by sorry

end Symbols

theorem rs_ne_empty (fst_comp : FST α Γ σ2) : [] ∉ RealizableSequences fst_comp := by
  simp_all[RealizableSequences]
