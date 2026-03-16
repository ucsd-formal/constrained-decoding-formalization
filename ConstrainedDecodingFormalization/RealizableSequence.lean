import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Producible
import ConstrainedDecodingFormalization.Lexing
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

omit [BEq α] [Inhabited α] [Inhabited Γ] [Fintype α] t in
lemma mem_computeSingleProducible_iff_singleProducible
  [LawfulBEq Γ] (fst_comp : FST α Γ σ2) (q0 : σ2) (T : Γ) :
  T ∈ fst_comp.computeSingleProducible q0 ↔ T ∈ fst_comp.singleProducible q0 := by
  have h :
      T ∈ (↑((fst_comp.computeSingleProducible q0).toFinset) : Set Γ) ↔
        T ∈ fst_comp.singleProducible q0 := by
    rw [fst_comp.computeSingleProducible_correct q0]
    simp [FST.singleProducible]
  simpa using h

def itst_fst_eq_rs [LawfulBEq Γ]
  (fst_comp : FST α Γ σ2) : (BuildInverseTokenSpannerTable fst_comp).fst.toFinset = RealizableSequences fst_comp := by
  ext rs
  change rs ∈ (BuildInverseTokenSpannerTable fst_comp).fst.toFinset ↔ rs ∈ RealizableSequences fst_comp
  constructor
  · intro hrs
    rw [List.mem_toFinset] at hrs
    simp only [BuildInverseTokenSpannerTable, Id.run] at hrs
    have hrsRaw := List.mem_eraseDups.mp hrs
    simp only [List.mem_flatMap] at hrsRaw
    rcases hrsRaw with ⟨q0, hq0, c, hc, hrs⟩
    simp only [FinEnum.mem_toList] at hq0 hc
    cases hstep : fst_comp.step q0 c with
    | none => simp [hstep] at hrs
    | some stepData =>
        rcases stepData with ⟨q1, Ts⟩
        simp only [hstep, List.mem_map] at hrs
        rcases hrs with ⟨T, hT, hrsEq⟩
        refine ⟨q0, c, Ts, q1, T, hstep, ?_, hrsEq.symm⟩
        exact (mem_computeSingleProducible_iff_singleProducible (fst_comp := fst_comp) q1 T).1 hT
  · rintro ⟨q0, c, Ts, q1, T, hstep, hT, rfl⟩
    rw [List.mem_toFinset]
    apply List.mem_eraseDups.2
    apply List.mem_flatMap.mpr
    refine ⟨q0, by simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨c, by simp, ?_⟩
    simp only [hstep, List.mem_map]
    exact ⟨T, (mem_computeSingleProducible_iff_singleProducible (fst_comp := fst_comp) q1 T).2 hT, rfl⟩

omit [BEq α] [Inhabited α] [Inhabited Γ] [Fintype α] t in
lemma mem_re_iff [LawfulBEq Γ]
  (fst_comp : FST α Γ σ2) (d : List Γ) :
  d ∈ (BuildInverseTokenSpannerTable fst_comp).fst ↔ d ∈ RealizableSequences fst_comp := by
  rw [← List.mem_toFinset]
  simpa using congrArg (fun s => d ∈ s) (itst_fst_eq_rs (fst_comp := fst_comp))

omit [BEq α] [Inhabited α] [Inhabited Γ] [Fintype α] t in
lemma BuildInverseTokenSpannerTable_snd
  (fst_comp : FST α Γ σ2) (rs : List Γ) (s : σ2) :
  (BuildInverseTokenSpannerTable fst_comp).snd rs s =
    if h : rs ≠ [] then
      let Ts := rs.dropLast
      let T := rs.getLast h
      (a.toList).filter (fun c =>
        match fst_comp.step s c with
        | none => false
        | some (q', Ts') => (fst_comp.computeSingleProducible q').contains T && Ts' = Ts)
    else [] := by
  rfl

omit [BEq α] [Inhabited α] [Inhabited Γ] [Fintype α] t in
def itst_snd_eq_itst [LawfulBEq Γ] (fst_comp : FST α Γ σ2) :
    ∀ rs s, ((BuildInverseTokenSpannerTable fst_comp).snd rs s).toFinset = InverseTokenSpannerTable fst_comp rs s := by
  intro rs s
  ext tok
  change tok ∈ ((BuildInverseTokenSpannerTable fst_comp).snd rs s).toFinset ↔ tok ∈ InverseTokenSpannerTable fst_comp rs s
  by_cases hnil : rs = []
  · subst hnil
    rw [BuildInverseTokenSpannerTable_snd, List.mem_toFinset]
    simp [InverseTokenSpannerTable]
  · have hne : rs ≠ [] := hnil
    rw [BuildInverseTokenSpannerTable_snd, List.mem_toFinset]
    simp [InverseTokenSpannerTable, hne, List.mem_filter]
    cases hstep : fst_comp.step s tok with
    | none => simp
    | some val =>
        rcases val with ⟨q1, Ts'⟩
        constructor
        · intro h
          have h' : rs.getLast hne ∈ fst_comp.computeSingleProducible q1 ∧ Ts' = rs.dropLast := by
            simpa using h
          rcases h' with ⟨hmem, hTs⟩
          refine ⟨q1, ?_, ?_⟩
          · simp [hTs]
          · exact (mem_computeSingleProducible_iff_singleProducible (fst_comp := fst_comp) q1 (rs.getLast hne)).1 hmem
        · rintro ⟨q1', hp, hprod⟩
          have hpair : q1 = q1' ∧ Ts' = rs.dropLast := by
            simpa [Prod.mk.injEq] using Option.some.inj hp
          rcases hpair with ⟨hq, hTs⟩
          subst q1'
          have hmem : rs.getLast hne ∈ fst_comp.computeSingleProducible q1 :=
            (mem_computeSingleProducible_iff_singleProducible (fst_comp := fst_comp) q1 (rs.getLast hne)).2 hprod
          simpa [hstep, hTs] using And.intro hmem hTs

omit [BEq α] [Inhabited α] [Inhabited Γ] [Fintype α] t in
lemma mem_itst_iff [LawfulBEq Γ]
  (fst_comp : FST α Γ σ2) (d : List Γ) (qa : σ2) (tok : α) :
  tok ∈ (BuildInverseTokenSpannerTable fst_comp).snd d qa ↔ tok ∈ InverseTokenSpannerTable fst_comp d qa := by
  rw [← List.mem_toFinset]
  simpa using congrArg (fun s => tok ∈ s) (itst_snd_eq_itst (fst_comp := fst_comp) d qa)

end Symbols

theorem rs_ne_empty (fst_comp : FST α Γ σ2) : [] ∉ RealizableSequences fst_comp := by
  simp_all[RealizableSequences]
