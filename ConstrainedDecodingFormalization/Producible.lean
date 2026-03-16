import ConstrainedDecodingFormalization.Automata

universe u v w

namespace FST

variable {α : Type u} {Γ : Type v} {σ : Type w}
variable (M : FST α Γ σ)

def producible (q : σ) : Language Γ :=
    { t | ∃ w, (∃ r ∈ M.evalFrom q w, r.2 = t) }

def singleProducible (q : σ) : Set Γ :=
    { t | ∃ w, (∃ r ∈ M.evalFrom q w, r.2 = [t]) }

lemma compl_card_lt_of_insert
  [Fintype σ] [DecidableEq σ]
  {vis : Finset σ} {s : σ} (h : s ∉ vis) :
  ((vis ∪ {s})ᶜ).card < (visᶜ).card := by
  observe h_sub : visᶜ ∩ {s}ᶜ ⊆ visᶜ
  have h_neq : visᶜ ∩ {s}ᶜ ≠ visᶜ := by simp [h]
  observe h_proper_sub : visᶜ ∩ {s}ᶜ ⊂ visᶜ
  observe h_goal : (visᶜ ∩ {s}ᶜ).card < (visᶜ).card
  simp only[Finset.compl_union]
  exact h_goal

def dfs
  [ Fintype Γ ] [ Fintype σ ] [ a: FinEnum α ]
  [DecidableEq σ ] [DecidableEq α ] [DecidableEq Γ ]
  (curr : σ) (vis : Finset σ) (ret : List Γ) : Finset σ × List Γ :=
  let alph := a.toList
  if _h_vis : curr ∈ vis then (vis, ret)
  else
    let base := vis ∪ {curr}
    let stepAccum :
        (Finset σ × List Γ) → α → (Finset σ × List Γ) :=
      fun acc next =>
        let (visacc, retacc) := acc
        match M.step curr next with
        | none => (visacc, retacc)
        | some (nextState, output) =>
          match output with
          | [] =>
              let (v2, r2) := dfs nextState base retacc
              (visacc ∪ v2, retacc ∪ r2)
          | [γ] =>
              (visacc, γ :: retacc)
          | _::_::_ =>
              (visacc, retacc)
    let (v, r) := alph.foldl stepAccum (base, ret)
    (v, r)
  termination_by (visᶜ).card
  decreasing_by
    exact compl_card_lt_of_insert _h_vis

def computeSingleProducible
  [ Fintype Γ ] [ Fintype σ ] [ a: FinEnum α ]
  [DecidableEq σ ] [DecidableEq α ] [DecidableEq Γ ]
  (q : σ) : List Γ :=
  (dfs M q {} []).snd

section

variable [DecidableEq σ]

/-- `DfsEpsReach V q s` means that `s` is reachable from `q` by following only
epsilon-output transitions in a way compatible with `dfs`: each recursive step
visits a fresh state and grows the visited set exactly as `dfs` does. -/
inductive DfsEpsReach : Finset σ → σ → σ → Prop where
  | here {V : Finset σ} {q : σ}
      (hq : q ∉ V) :
      DfsEpsReach V q q
  | next {V : Finset σ} {q q₁ s : σ} {a : α}
      (hq : q ∉ V)
      (hstep : M.step q a = some (q₁, []))
      (hrest : DfsEpsReach (V ∪ {q}) q₁ s) :
      DfsEpsReach V q s

lemma mem_foldl_dfs_stepAccum_of_mem
  [Fintype Γ] [Fintype σ] [a : FinEnum α]
  [DecidableEq α] [DecidableEq Γ]
  {q : σ} {base : Finset σ} {t : Γ} :
  ∀ (L : List α) (acc : Finset σ × List Γ),
    t ∈ acc.2 →
    let stepAccum :
        (Finset σ × List Γ) → α → (Finset σ × List Γ) :=
      fun acc next =>
        let (visacc, retacc) := acc
        match M.step q next with
        | none => (visacc, retacc)
        | some (nextState, output) =>
          match output with
          | [] =>
              let (v2, r2) := M.dfs (a := a) nextState base retacc
              (visacc ∪ v2, retacc ∪ r2)
          | [γ] =>
              (visacc, γ :: retacc)
          | _::_::_ =>
              (visacc, retacc)
    t ∈ (L.foldl stepAccum acc).2 := by
  intro L
  induction L with
  | nil =>
      intro acc hmem
      simpa using hmem
  | cons x xs ih =>
      intro acc hmem
      cases acc with
      | mk visacc retacc =>
          dsimp
          cases hstep : M.step q x with
          | none =>
              exact ih (visacc, retacc) hmem
          | some p =>
              rcases p with ⟨nextState, output⟩
              cases output with
              | nil =>
                  have hmem' : t ∈ (retacc ∪ (M.dfs (a := a) nextState base retacc).2) := by
                    exact List.mem_union_iff.2 (Or.inl hmem)
                  exact ih (visacc ∪ (M.dfs (a := a) nextState base retacc).1,
                    retacc ∪ (M.dfs (a := a) nextState base retacc).2) hmem'
              | cons γ tail =>
                  cases tail with
                  | nil =>
                      have hmem' : t ∈ (γ :: retacc) := by
                        exact List.mem_cons.2 (Or.inr hmem)
                      exact ih (visacc, γ :: retacc) hmem'
                  | cons γ₂ tail₂ =>
                      exact ih (visacc, retacc) hmem

lemma mem_dfs_of_singleton_step
  [Fintype Γ] [Fintype σ] [a : FinEnum α]
  [DecidableEq α] [DecidableEq Γ]
  {V : Finset σ} {q q₁ : σ} {x : α} {t : Γ}
  (hq : q ∉ V)
  (hstep : M.step q x = some (q₁, [t])) :
  t ∈ (M.dfs (a := a) q V []).2 := by
  let base : Finset σ := insert q V
  let stepAccum :
      (Finset σ × List Γ) → α → (Finset σ × List Γ) :=
    fun acc next =>
      let (visacc, retacc) := acc
      match M.step q next with
      | none => (visacc, retacc)
      | some (nextState, output) =>
        match output with
        | [] =>
            let (v2, r2) := M.dfs (a := a) nextState base retacc
            (visacc ∪ v2, retacc ∪ r2)
        | [γ] =>
            (visacc, γ :: retacc)
        | _::_::_ =>
            (visacc, retacc)
  have hmem_in_fold :
      ∀ (L : List α) (acc : Finset σ × List Γ),
        x ∈ L →
        t ∈ (L.foldl stepAccum acc).2 := by
    intro L
    induction L with
    | nil =>
        intro acc hmem
        cases hmem
    | cons y ys ih =>
        intro acc hmem
        rcases List.mem_cons.1 hmem with rfl | htail
        ·
          have hnow : t ∈ (stepAccum acc x).2 := by
            cases acc with
            | mk visacc retacc =>
                dsimp [stepAccum]
                simp [hstep]
          exact mem_foldl_dfs_stepAccum_of_mem (M := M) (a := a) (q := q) (base := base) ys
            (stepAccum acc x) hnow
        ·
          exact ih (stepAccum acc y) htail
  have hx : x ∈ (a : FinEnum α).toList := FinEnum.mem_toList x
  have hfold : t ∈ (((a : FinEnum α).toList).foldl stepAccum (base, [])).2 :=
    hmem_in_fold ((a : FinEnum α).toList) (base, []) hx
  unfold dfs
  simp [hq]
  change t ∈ (((a : FinEnum α).toList).foldl stepAccum (base, [])).2
  exact hfold

omit [DecidableEq σ] in
lemma dfs_seed_subset
  [Fintype σ] [Fintype Γ] [FinEnum α]
  [DecidableEq σ] [DecidableEq α] [DecidableEq Γ]
  {q : σ} {vis : Finset σ} {ret₁ ret₂ : List Γ}
  (hsubset : ∀ {x : Γ}, x ∈ ret₁ → x ∈ ret₂) :
  ∀ {t : Γ},
    t ∈ (M.dfs (a := a) q vis ret₁).2 →
    t ∈ (M.dfs (a := a) q vis ret₂).2 := by
  let P : Nat → Prop := fun n =>
    ∀ q vis ret₁ ret₂,
      (visᶜ).card = n →
      (∀ {x : Γ}, x ∈ ret₁ → x ∈ ret₂) →
      ∀ {t : Γ},
        t ∈ (M.dfs (a := a) q vis ret₁).2 →
        t ∈ (M.dfs (a := a) q vis ret₂).2

  have step : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n IH q vis ret₁ ret₂ hcard hsubset t hmem
    unfold dfs at hmem ⊢
    by_cases h_vis : q ∈ vis
    · simp [h_vis] at hmem ⊢
      exact hsubset hmem
    ·
      let base : Finset σ := vis ∪ {q}
      let stepAccum₁ :
          (Finset σ × List Γ) → α → (Finset σ × List Γ) :=
        fun acc next =>
          let (visacc, retacc) := acc
          match M.step q next with
          | none => (visacc, retacc)
          | some (nextState, output) =>
            match output with
            | [] =>
                let (v2, r2) := M.dfs (a := a) nextState base retacc
                (visacc ∪ v2, retacc ∪ r2)
            | [γ] =>
                (visacc, γ :: retacc)
            | _::_::_ =>
                (visacc, retacc)
      let stepAccum₂ :
          (Finset σ × List Γ) → α → (Finset σ × List Γ) :=
        fun acc next =>
          let (visacc, retacc) := acc
          match M.step q next with
          | none => (visacc, retacc)
          | some (nextState, output) =>
            match output with
            | [] =>
                let (v2, r2) := M.dfs (a := a) nextState base retacc
                (visacc ∪ v2, retacc ∪ r2)
            | [γ] =>
                (visacc, γ :: retacc)
            | _::_::_ =>
                (visacc, retacc)
      let alph : List α := (a : FinEnum α).toList

      have fold_subset :
        ∀ (L : List α) (acc₁ acc₂ : Finset σ × List Γ),
          (∀ {x : Γ}, x ∈ acc₁.2 → x ∈ acc₂.2) →
          t ∈ (L.foldl stepAccum₁ acc₁).2 →
          t ∈ (L.foldl stepAccum₂ acc₂).2 := by
        intro L
        induction L with
        | nil =>
            intro acc₁ acc₂ hacc hmem
            simpa using hacc hmem
        | cons x xs ih =>
            intro acc₁ acc₂ hacc hmem
            simp only [List.foldl] at hmem ⊢
            cases hstep : M.step q x with
            | none =>
                have hacc_step :
                    ∀ {y : Γ},
                      y ∈ (stepAccum₁ acc₁ x).2 →
                      y ∈ (stepAccum₂ acc₂ x).2 := by
                  intro y hy
                  simpa [stepAccum₂, hstep] using
                    (hacc (by simpa [stepAccum₁, hstep] using hy))
                simpa [stepAccum₁, stepAccum₂, hstep] using
                  ih (stepAccum₁ acc₁ x) (stepAccum₂ acc₂ x) hacc_step hmem
            | some p =>
                rcases p with ⟨nextState, output⟩
                cases output with
                | nil =>
                    have hlt : (baseᶜ).card < (visᶜ).card :=
                      compl_card_lt_of_insert (σ := σ) (vis := vis) (s := q) h_vis
                    have IHbase : P (baseᶜ).card := IH _ (by simpa [hcard] using hlt)
                    have hacc' :
                        ∀ {y : Γ},
                          y ∈ (acc₁.2 ∪ (M.dfs (a := a) nextState base acc₁.2).2) →
                          y ∈ (acc₂.2 ∪ (M.dfs (a := a) nextState base acc₂.2).2) := by
                      intro y hy
                      rw [List.mem_union_iff] at hy ⊢
                      rcases hy with hy | hy
                      · exact Or.inl (hacc hy)
                      · exact Or.inr (IHbase nextState base acc₁.2 acc₂.2 rfl hacc hy)
                    have hacc_step :
                        ∀ {y : Γ},
                          y ∈ (stepAccum₁ acc₁ x).2 →
                          y ∈ (stepAccum₂ acc₂ x).2 := by
                      intro y hy
                      simpa [stepAccum₂, hstep] using
                        (hacc' (by simpa [stepAccum₁, hstep] using hy))
                    simpa [stepAccum₁, stepAccum₂, hstep] using
                      ih
                        (stepAccum₁ acc₁ x)
                        (stepAccum₂ acc₂ x)
                        hacc_step hmem
                | cons γ tail =>
                    cases tail with
                    | nil =>
                        have hacc' :
                            ∀ {y : Γ}, y ∈ (γ :: acc₁.2) → y ∈ (γ :: acc₂.2) := by
                          intro y hy
                          rcases List.mem_cons.1 hy with rfl | hy
                          · simp
                          · exact List.mem_cons_of_mem _ (hacc hy)
                        have hacc_step :
                            ∀ {y : Γ},
                              y ∈ (stepAccum₁ acc₁ x).2 →
                              y ∈ (stepAccum₂ acc₂ x).2 := by
                          intro y hy
                          simpa [stepAccum₂, hstep] using
                            (hacc' (by simpa [stepAccum₁, hstep] using hy))
                        simpa [stepAccum₁, stepAccum₂, hstep] using
                          ih (stepAccum₁ acc₁ x) (stepAccum₂ acc₂ x) hacc_step hmem
                    | cons γ₂ tail₂ =>
                        have hacc_step :
                            ∀ {y : Γ},
                              y ∈ (stepAccum₁ acc₁ x).2 →
                              y ∈ (stepAccum₂ acc₂ x).2 := by
                          intro y hy
                          simpa [stepAccum₂, hstep] using
                            (hacc (by simpa [stepAccum₁, hstep] using hy))
                        simpa [stepAccum₁, stepAccum₂, hstep] using
                          ih (stepAccum₁ acc₁ x) (stepAccum₂ acc₂ x) hacc_step hmem

      have hmem0 : t ∈ (alph.foldl stepAccum₁ (base, ret₁)).2 := by
        simpa [base, stepAccum₁, alph, h_vis] using hmem
      have hgoal0 : t ∈ (alph.foldl stepAccum₂ (base, ret₂)).2 :=
        fold_subset alph (base, ret₁) (base, ret₂) hsubset hmem0
      simpa [base, stepAccum₂, alph, h_vis] using hgoal0

  have H : P ((visᶜ).card) := Nat.strongRecOn (motive := P) ((visᶜ).card) step
  intro t ht
  exact H q vis ret₁ ret₂ rfl hsubset ht

lemma mem_dfs_of_eps_step
  [Fintype Γ] [Fintype σ] [a : FinEnum α]
  [DecidableEq α] [DecidableEq Γ]
  {V : Finset σ} {q q₁ : σ} {x : α} {t : Γ}
  (hq : q ∉ V)
  (hstep : M.step q x = some (q₁, []))
  (hrec : t ∈ (M.dfs (a := a) q₁ (insert q V) []).2) :
  t ∈ (M.dfs (a := a) q V []).2 := by
  let base : Finset σ := insert q V
  let stepAccum :
      (Finset σ × List Γ) → α → (Finset σ × List Γ) :=
    fun acc next =>
      let (visacc, retacc) := acc
      match M.step q next with
      | none => (visacc, retacc)
      | some (nextState, output) =>
        match output with
        | [] =>
            let (v2, r2) := M.dfs (a := a) nextState base retacc
            (visacc ∪ v2, retacc ∪ r2)
        | [γ] =>
            (visacc, γ :: retacc)
        | _::_::_ =>
            (visacc, retacc)
  have hmem_in_fold :
      ∀ (L : List α) (acc : Finset σ × List Γ),
        x ∈ L →
        t ∈ (L.foldl stepAccum acc).2 := by
    intro L
    induction L with
    | nil =>
        intro acc hmem
        cases hmem
    | cons y ys ih =>
        intro acc hmem
        rcases List.mem_cons.1 hmem with rfl | htail
        ·
          have hnow : t ∈ (stepAccum acc x).2 := by
            cases acc with
            | mk visacc retacc =>
                have hrec' : t ∈ (M.dfs (a := a) q₁ base retacc).2 := by
                  exact dfs_seed_subset (M := M) (a := a) (q := q₁) (vis := base)
                    (ret₁ := []) (ret₂ := retacc) (by intro z hz; cases hz) hrec
                dsimp [stepAccum]
                have : t ∈ (retacc ∪ (M.dfs (a := a) q₁ base retacc).2) := by
                  exact List.mem_union_iff.2 (Or.inr hrec')
                simpa [hstep] using this
          exact mem_foldl_dfs_stepAccum_of_mem (M := M) (a := a) (q := q) (base := base) ys
            (stepAccum acc x) hnow
        ·
          exact ih (stepAccum acc y) htail
  have hx : x ∈ (a : FinEnum α).toList := FinEnum.mem_toList x
  have hfold : t ∈ (((a : FinEnum α).toList).foldl stepAccum (base, [])).2 :=
    hmem_in_fold ((a : FinEnum α).toList) (base, []) hx
  unfold dfs
  simp [hq]
  change t ∈ (((a : FinEnum α).toList).foldl stepAccum (base, [])).2
  exact hfold

omit [DecidableEq σ] in
lemma dfs_complete_from_reach
  [Fintype Γ] [Fintype σ] [a : FinEnum α]
  [DecidableEq σ] [DecidableEq α] [DecidableEq Γ]
  {V : Finset σ} {q s : σ} {t : Γ}
  (hreach : DfsEpsReach (M := M) V q s)
  (hstep : ∃ x q₁, M.step s x = some (q₁, [t])) :
  t ∈ (M.dfs (a := a) q V []).2 := by
  induction hreach with
  | here hq =>
      rcases hstep with ⟨x, q₁, hstepx⟩
      exact mem_dfs_of_singleton_step (M := M) (a := a) hq hstepx
  | @next V q qnext s x hq hstep_eps hrest ih =>
      have hrec_insert : t ∈ (M.dfs (a := a) qnext (insert q V) []).2 := by
        have hinsert_eq_union : insert q V = V ∪ {q} := by
          ext y
          simp
        rw [hinsert_eq_union]
        exact ih hstep
      exact mem_dfs_of_eps_step (M := M) (a := a) hq hstep_eps hrec_insert

end

lemma evalFrom_cons_some_iff {s s'' : σ} {a : α} {as : List α} {U : List Γ} :
  M.evalFrom s (a :: as) = some (s'', U)
    ↔ ∃ s' S T,
        M.step s a = some (s', S) ∧
        M.evalFrom s' as = some (s'', T) ∧
        U = S ++ T := by
  unfold evalFrom
  cases h₀ : M.step s a with
  | none =>
      simp
  | some p =>
      rcases p with ⟨s', S⟩
      cases h₁ : M.evalFrom s' as with
      | none =>
          constructor
          .
            intro h
            simp [h₁] at h
          .
            rintro ⟨s1, S1, T, hstep, heval, hU⟩
            simp_all
            have : M.evalFrom s' [] = some (s', []) := rfl
            have : s' = s1 := by
              simp_all
            subst this
            simp_all
            cases h : as
            .
              subst h
              contradiction
            .
              repeat split at heval <;> repeat contradiction
              obtain ⟨l, r⟩ := h
              rename_i _ _ _ _ _ _ _ _ _ heq heq'
              unfold evalFrom at h₁
              simp [heq, heq'] at h₁
      | some q =>
          rcases q with ⟨s₁, T⟩
          constructor
          · intro h
            have : s₁ = s'' ∧ S ++ T = U := by
              simpa [h₀, h₁, Prod.mk.injEq] using h
            rcases this with ⟨hs, hU⟩
            refine ⟨s', S, T, rfl, ?_, ?_⟩
            ·
              subst hU hs
              simp_all only
              split
              next l => simp_all only [evalFrom_nil, Option.some.injEq, Prod.mk.injEq, List.nil_eq]
              next l a_1 as => exact h₁
            · simp [hU]
          · intro hex
            rcases hex with ⟨s'_, S_, T', hstep, heval, hU⟩
            have : s' = s' ∧ S = S := by exact And.intro rfl rfl
            have hsT : s₁ = s'' ∧ T = T' := by
              simp_all [Prod.mk.injEq]
              obtain ⟨l, r⟩ := hstep
              subst l r
              cases h : as
              .
                subst h
                simp at heval
                have heq : some (s₁, T) = some (s', []) := by exact id (Eq.symm h₁)
                simp_all
              .
                rename_i x xs
                subst h
                simp at heval
                repeat split at heval <;> repeat contradiction
                rename_i _ _ _ heq _ _ _ heq'
                unfold evalFrom at h₁
                simp [heq, heq'] at h₁
                obtain ⟨l, r⟩ := h₁
                subst hU l r
                simp_all only [Option.some.injEq, Prod.mk.injEq, and_self]
            rcases hsT with ⟨hs, hT⟩
            have : U = S ++ T := by
              simp_all
            simp [h₁, hs, this]

lemma evalFrom_cons_singleton_iff
  (M : FST α Γ σ) {s s'' : σ} {a : α} {as : List α} {t : Γ} :
  M.evalFrom s (a :: as) = some (s'', [t])
    ↔ (∃ s', M.step s a = some (s', [t]) ∧ M.evalFrom s' as = some (s'', []))
     ∨ (∃ s', M.step s a = some (s', []) ∧ M.evalFrom s' as = some (s'', [t])) := by
  constructor
  · intro h
    rcases (evalFrom_cons_some_iff (M := M)).mp h with ⟨s', S, T, hstep, heval, hU⟩
    have : S ++ T = [t] := symm hU
    cases S using List.rec with
    | nil =>
        simp at this
        right
        refine ⟨s', by simp [hstep], ?_⟩
        simpa [this] using heval
    | @cons γ S =>
        cases S using List.rec with
        | nil =>
            simp at this
            rcases this with ⟨hγ, hT⟩
            left
            refine ⟨s', ?_, ?_⟩
            · simp [hstep, hγ]
            · simpa [hT] using heval
        | @cons γ₂ S₂ =>
            cases this

  · intro h
    rcases h with ⟨s', hstep, heval⟩ | ⟨s', hstep, heval⟩
    ·
      exact
        (evalFrom_cons_some_iff (M := M) (s := s) (s'' := s'') (a := a) (as := as) (U := [t])).mpr
          ⟨s', [t], [], hstep, by simpa using heval, by simp⟩
    ·
      exact
        (evalFrom_cons_some_iff (M := M) (s := s) (s'' := s'') (a := a) (as := as) (U := [t])).mpr
          ⟨s', [], [t], hstep, by simpa using heval, by simp⟩

lemma evalFrom_singleton_decompose
  [DecidableEq σ] [DecidableEq α] [DecidableEq Γ]
  {q qf : σ} {w : List α} {t : Γ} :
  M.evalFrom q w = some (qf, [t]) →
  ∃ (u v : List α) (a₀ : α) (s s' : σ),
    w = u ++ (a₀ :: v) ∧
    M.evalFrom q u = some (s, []) ∧
    M.step s a₀ = some (s', [t]) ∧
    M.evalFrom s' v = some (qf, []) := by
  revert q qf
  induction w with
  | nil =>
      intro q qf h; cases h
  | cons a as ih =>
      intro q qf h
      rcases (evalFrom_cons_some_iff (M := M)
                (s := q) (a := a) (as := as) (U := [t])).1 h
        with ⟨s', S, T, hstep, heval, hU⟩
      have hST : S ++ T = [t] := by simpa using hU.symm
      cases S with
      | nil =>
          have hT : T = [t] := by simpa [List.nil_append] using hST
          have heval' : M.evalFrom s' as = some (qf, [t]) := by simpa [hT] using heval
          rcases ih (q := s') (qf := qf) heval' with
            ⟨u, v, a₀, s, s₁, hw, hu, h1, hv⟩
          refine ⟨a :: u, v, a₀, s, s₁, ?_, ?_, ?_, ?_⟩
          · simp [hw, List.cons_append]
          ·
            have hstep_nil : M.step q a = some (s', []) := by simpa using hstep
            have : M.evalFrom q (a :: u) = some (s, []) :=
              (evalFrom_cons_some_iff (M := M) (s := q) (a := a) (as := u) (U := ([] : List Γ))).mpr
                ⟨s', [], [], hstep_nil, hu, by simp⟩
            simpa using this
          · exact h1
          · exact hv
      | cons γ S' =>
          cases S' with
          | nil =>
              have hγT : γ = t ∧ T = [] := by
                have : γ :: T = [t] := by simpa using hST
                simpa using List.cons.inj this
              rcases hγT with ⟨hγ, hT⟩
              refine ⟨[], as, a, q, s', ?_, ?_, ?_, ?_⟩
              · simp
              · simp [FST.evalFrom]
              · simpa [hγ] using hstep
              · simpa [hT] using heval
          | cons _ _ =>
              rename_i head tail
              have hcons : γ = t ∧ head :: (tail ++ T) = ([] : List Γ) := by
                simpa using List.cons.inj hST
              rcases hcons with ⟨hγ, htail⟩
              have hne : (head :: (tail ++ T)) ≠ ([] : List Γ) := by simp
              contradiction

lemma dfs_sound_core_or
  (M : FST α Γ σ)
  [Fintype σ] [Fintype Γ] [FinEnum α]
  [DecidableEq σ] [DecidableEq α] [DecidableEq Γ]
  (s : σ) (vis : Finset σ) (ret : List Γ) {t : Γ}
  (h : t ∈ (M.dfs (a := a) s vis ret).2) :
  t ∈ ret ∨ ∃ w qf, M.evalFrom s w = some (qf, [t]) := by
  let P : Nat → Prop := fun n =>
    ∀ s vis ret {t : Γ},
      (visᶜ).card = n →
      t ∈ (M.dfs (a := a) s vis ret).2 →
      t ∈ ret ∨ ∃ w qf, M.evalFrom s w = some (qf, [t])

  have step : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n IH s vis ret t hcard hmem
    unfold dfs at hmem
    by_cases h_vis : s ∈ vis
    ·
      subst hcard
      simp_all [true_or, P]
    ·
      let base := vis ∪ {s}
      let stepAccum :
          (Finset σ × List Γ) → α → (Finset σ × List Γ) :=
        fun acc next =>
          let (visacc, retacc) := acc
          match M.step s next with
          | none => (visacc, retacc)
          | some (s', out) =>
            match out with
            | [] =>
                let (v2, r2) := M.dfs (a := a) s' base retacc
                (visacc ∪ v2, retacc ∪ r2)
            | [γ] =>
                (visacc, γ :: retacc)
            | _::_::_ =>
                (visacc, retacc)
      let alph : List α := (a : FinEnum α).toList

      have fold_ind :
        ∀ (L : List α) (acc : Finset σ × List Γ),
          t ∈ (L.foldl stepAccum acc).2 →
          t ∈ acc.2 ∨ ∃ w qf, M.evalFrom s w = some (qf, [t]) :=
      by
        intro L
        induction L with
        | nil =>
            intro acc ht
            simp [List.foldl] at ht
            exact Or.inl ht
        | cons x xs ih =>
            intro acc ht
            simp [List.foldl, stepAccum] at ht
            cases hstepx : M.step s x with
            | none =>
              simp_all [base, P, stepAccum]
              apply ih
              · exact ht
            | some p =>
                rcases p with ⟨s', out⟩
                cases h₀ : out with
                | nil =>
                  rcases acc with ⟨visacc, retacc⟩
                  set res := M.dfs (a := a) s' base retacc with hres
                  rcases res with ⟨v2, r2⟩
                  have hstep1 : stepAccum (visacc, retacc) x = (visacc ∪ v2, retacc ∪ r2) := by
                    dsimp [stepAccum]
                    simp [hstepx, h₀]
                    have : v2 = (M.dfs (a := a) s' base retacc).1 := congrArg Prod.fst hres
                    subst this
                    constructor
                    . rfl
                    . observe : r2 = (M.dfs (a := a) s' base retacc).2
                      subst this
                      rfl
                  have ht1 : t ∈ (xs.foldl stepAccum (stepAccum (visacc, retacc) x)).2 := by
                    simpa [List.foldl] using ht
                  have hxs : t ∈ (xs.foldl stepAccum (visacc ∪ v2, retacc ∪ r2)).2 := by
                    simpa [hstep1] using ht1
                  have h_tail : t ∈ (visacc ∪ v2, retacc ∪ r2).2 ∨ ∃ w qf, M.evalFrom s w = some (qf, [t]) :=
                    ih (visacc ∪ v2, retacc ∪ r2) hxs
                  rcases h_tail with h_in_union | ⟨w, qf, hw⟩
                  ·
                    have hsplit : t ∈ retacc ∨ t ∈ r2 := by
                      simp_all [base, P, stepAccum]
                    rcases hsplit with h_in_retacc | h_in_r2
                    .
                      exact Or.inl h_in_retacc
                    .
                      have h_in_dfs' : t ∈ (M.dfs (a := a) s' base retacc).2 := by
                        have : r2 = (M.dfs (a := a) s' (vis ∪ {s}) retacc).2 := congrArg Prod.snd hres
                        subst this
                        exact h_in_r2

                      have hlt : (baseᶜ).card < (visᶜ).card :=
                        compl_card_lt_of_insert (σ := σ) (vis := vis) (s := s) h_vis
                      subst hcard
                      have IHbase : P (baseᶜ).card := IH _ hlt
                      have res₂ := IHbase s' base retacc rfl h_in_dfs'
                      rcases res₂ with h_in_seed | ⟨w', qf', hw'⟩
                      . simp [h_in_seed]
                      .
                        refine Or.inr ?_
                        refine ⟨x :: w', qf', ?_⟩
                        have right : (∃ s0, M.step s x = some (s0, []) ∧ M.evalFrom s0 w' = some (qf', [t])) :=
                          ⟨s', by simpa [hstepx], hw'⟩
                        simpa [evalFrom_cons_singleton_iff (M := M)] using Or.inr right
                  ·
                    exact Or.inr ⟨w, qf, hw⟩
                | cons γ tail =>
                    cases tail with
                    | nil =>
                        rcases acc with ⟨visacc, retacc⟩
                        have ht1 : t ∈ (xs.foldl stepAccum (visacc, γ :: retacc)).2 := by
                          simpa [List.foldl, stepAccum, hstepx, h₀] using ht
                        have h_tail : t ∈ (visacc, γ :: retacc).2 ∨ ∃ w qf, M.evalFrom s w = some (qf, [t]) :=
                          ih (visacc, γ :: retacc) ht1
                        rcases h_tail with h_in | ⟨w, qf, hw⟩
                        ·
                          have : t = γ ∨ t ∈ retacc := by
                            simpa using (List.mem_cons.mp h_in)
                          rcases this with h_eq | h_in_retacc
                          ·
                            subst h_eq
                            refine Or.inr ?_
                            refine ⟨[x], s', ?_⟩
                            have left :
                              (∃ s0, M.step s x = some (s0, [t]) ∧
                                      M.evalFrom s0 [] = some (s', [])) :=
                              ⟨s', by simpa [hstepx], by simp [evalFrom]⟩
                            simp
                            subst h₀ hcard
                            simp_all [base, P, stepAccum]
                          ·
                            exact Or.inl h_in_retacc
                        ·
                          exact Or.inr ⟨w, qf, hw⟩
                    | cons _ _ =>
                        simp_all [base, P, stepAccum]
                        apply ih
                        · exact ht

      have : t ∈ (alph.foldl stepAccum (base, ret)).2 := by
        simp_all [base, P, stepAccum, alph]
      exact fold_ind alph (base, ret) this

  have H : P ((visᶜ).card) := Nat.strongRecOn (motive := P) ((visᶜ).card) step
  exact H s vis ret rfl h

lemma dfs_sound_core
  (M : FST α Γ σ) [Fintype σ] [Fintype Γ] [FinEnum α]
  [DecidableEq σ] [DecidableEq α] [DecidableEq Γ]
  (s : σ) (vis : Finset σ) {t : Γ}
  (h : t ∈ (M.dfs (a := a) s vis []).2) :
  ∃ w qf, M.evalFrom s w = some (qf, [t]) := by
  have h_or := dfs_sound_core_or (M := M) (a := a) s vis [] h
  rcases h_or with h_in_seed | hex
  · cases h_in_seed
  · exact hex

lemma dfs_sound {q : σ} {t : Γ}
  [ Fintype Γ ] [ Fintype σ ] [ a: FinEnum α ]
  [DecidableEq σ ] [DecidableEq α ] [DecidableEq Γ ]
  (ht : t ∈ (M.dfs q {} []).2) :
  ∃ w qf, M.evalFrom q w = some (qf, [t]) :=
  dfs_sound_core (M := M) (a := a) q ∅ ht

def EpsStep (q q' : σ) : Prop :=
  ∃ a, M.step q a = some (q', [])

lemma evalFrom_empty_to_epsReach
  {q s : σ} {u : List α}
  (hu : M.evalFrom q u = some (s, [])) :
  Relation.ReflTransGen (M.EpsStep) q s := by
  induction u generalizing q with
  | nil =>
      simp [FST.evalFrom] at hu
      subst s
      exact Relation.ReflTransGen.refl
  | cons a as ih =>
      rcases (evalFrom_cons_some_iff (M := M) (s := q) (a := a) (as := as) (U := ([] : List Γ))).1 hu with
        ⟨q₁, S, T, hstep, htail, hU⟩
      have hST : S = [] ∧ T = [] := by
        cases S with
        | nil =>
            simp at hU
            exact ⟨rfl, hU⟩
        | cons x xs =>
            cases hU
      have hstep_eps : M.step q a = some (q₁, []) := by
        simpa [hST.1] using hstep
      have htail_eps : M.evalFrom q₁ as = some (s, []) := by
        simpa [hST.2] using htail
      exact Relation.ReflTransGen.head ⟨a, hstep_eps⟩ (ih htail_eps)

lemma epsChain_to_dfsReach
  [DecidableEq σ]
  : ∀ {V : Finset σ} {q : σ} {l : List σ},
      List.IsChain (M.EpsStep) (q :: l) →
      List.Nodup (q :: l) →
      (∀ x ∈ q :: l, x ∉ V) →
      DfsEpsReach (M := M) V q ((q :: l).getLast (List.cons_ne_nil _ _)) := by
  intro V q l
  induction l generalizing V q with
  | nil =>
      intro hchain hnodup hdisj
      simpa using DfsEpsReach.here (M := M) (V := V) (q := q) (hdisj q (by simp))
  | cons q₁ rest ih =>
      intro hchain hnodup hdisj
      have hq_notV : q ∉ V := hdisj q (by simp)
      have hchain_split : M.EpsStep q q₁ ∧ List.IsChain (M.EpsStep) (q₁ :: rest) := by
        simpa [List.isChain_cons_cons] using hchain
      rcases hchain_split with ⟨hstep_rel, hchain_tail⟩
      have hnodup_split : q ∉ q₁ :: rest ∧ List.Nodup (q₁ :: rest) := by
        simpa using hnodup
      rcases hnodup_split with ⟨hq_not_mem_tail, hnodup_tail⟩
      have hdisj_tail : ∀ x ∈ q₁ :: rest, x ∉ V ∪ {q} := by
        intro x hx
        have hx_notV : x ∉ V := hdisj x (by simp [hx])
        have hx_ne_q : x ≠ q := by
          intro hEq
          subst hEq
          exact hq_not_mem_tail hx
        simp [hx_notV, hx_ne_q]
      rcases hstep_rel with ⟨a, hstep⟩
      have hrest :
          DfsEpsReach (M := M) (V ∪ {q}) q₁
            ((q₁ :: rest).getLast (List.cons_ne_nil _ _)) :=
        ih hchain_tail hnodup_tail hdisj_tail
      simpa using DfsEpsReach.next (M := M) (V := V) (q := q) (q₁ := q₁)
        (s := ((q₁ :: rest).getLast (List.cons_ne_nil _ _))) hq_notV hstep hrest

lemma mem_split
  [DecidableEq σ]
  {x : σ} {l : List σ}
  (h : x ∈ l) :
  ∃ pre post, l = pre ++ x :: post := by
  induction l with
  | nil =>
      cases h
  | cons y ys ih =>
      rcases List.mem_cons.1 h with rfl | htail
      · exact ⟨[], ys, rfl⟩
      · rcases ih htail with ⟨pre, post, hsplit⟩
        exact ⟨y :: pre, post, by simp [hsplit]⟩

lemma duplicate_decompose
  [DecidableEq σ]
  {x : σ} {l : List σ}
  (h : List.Duplicate x l) :
  ∃ pre mid post, l = pre ++ x :: mid ++ x :: post := by
  induction h with
  | cons_mem hmem =>
      rcases mem_split (x := x) hmem with ⟨mid, post, hsplit⟩
      exact ⟨[], mid, post, by simp [hsplit]⟩
  | @cons_duplicate y l h ih =>
      rcases ih with ⟨pre, mid, post, hsplit⟩
      exact ⟨y :: pre, mid, post, by simp [hsplit]⟩

lemma epsChain_remove_cycle
  {pre mid post : List σ} {x : σ}
  (hchain : List.IsChain (M.EpsStep) (pre ++ x :: mid ++ x :: post)) :
  List.IsChain (M.EpsStep) (pre ++ x :: post) := by
  have hleft : List.IsChain (M.EpsStep) (pre ++ [x]) := by
    have : List.IsChain (M.EpsStep) ((pre ++ [x]) ++ (mid ++ x :: post)) := by
      simpa [List.singleton_append, List.append_assoc] using hchain
    exact this.left_of_append
  have hright : List.IsChain (M.EpsStep) ([x] ++ post) := by
    have : List.IsChain (M.EpsStep) ((pre ++ x :: mid) ++ (x :: post)) := by
      simpa [List.append_assoc] using hchain
    exact this.right_of_append
  have : List.IsChain (M.EpsStep) (pre ++ [x] ++ post) :=
    hleft.append_overlap hright (by simp)
  simpa [List.singleton_append, List.append_assoc] using this

lemma head?_remove_cycle
  {pre mid post : List σ} {x : σ} :
  (pre ++ x :: mid ++ x :: post).head? = (pre ++ x :: post).head? := by
  cases pre <;> simp [List.append_assoc]

lemma getLast?_remove_cycle
  {pre mid post : List σ} {x : σ} :
  (pre ++ x :: mid ++ x :: post).getLast? = (pre ++ x :: post).getLast? := by
  cases post with
  | nil =>
      calc
        (pre ++ x :: mid ++ [x]).getLast?
            = (x :: mid ++ [x]).getLast? := by
                simpa [List.append_assoc] using List.getLast?_append_cons pre x (mid ++ [x])
        _ = [x].getLast? := by
              simpa [List.append_assoc] using
                (List.getLast?_append_of_ne_nil (x :: mid) (by simp : [x] ≠ []))
        _ = (pre ++ [x]).getLast? := by
              exact (List.getLast?_append_cons pre x []).symm
  | cons y ys =>
      have h1 :
          (pre ++ x :: mid ++ x :: y :: ys).getLast? = (y :: ys).getLast? := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (pre ++ x :: mid ++ [x]) (by simp : y :: ys ≠ []))
      have h2 :
          (pre ++ x :: y :: ys).getLast? = (y :: ys).getLast? := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (pre ++ [x]) (by simp : y :: ys ≠ []))
      exact h1.trans h2.symm

lemma epsReach_exists_nodup_chain
  [DecidableEq σ]
  {q s : σ}
  (hreach : Relation.ReflTransGen (M.EpsStep) q s) :
  ∃ l : List σ,
    List.IsChain (M.EpsStep) (q :: l) ∧
    (q :: l).getLast (List.cons_ne_nil _ _) = s ∧
    List.Nodup (q :: l) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ m : List σ,
      m.head? = some q ∧
      List.IsChain (M.EpsStep) m ∧
      m.getLast? = some s ∧
      m.length = n
  have hex : ∃ n, P n := by
    rcases List.exists_isChain_cons_of_relationReflTransGen hreach with ⟨l, hchain, hlast⟩
    refine ⟨(q :: l).length, q :: l, by simp, hchain, ?_, rfl⟩
    simpa [List.getLast?_eq_getLast_of_ne_nil] using congrArg some hlast
  let n := Nat.find hex
  have hn : P n := Nat.find_spec hex
  rcases hn with ⟨m, hhead, hchain, hlast, hlen⟩
  have hmin :
      ∀ {m' : List σ},
        m'.head? = some q →
        List.IsChain (M.EpsStep) m' →
        m'.getLast? = some s →
        n ≤ m'.length := by
    intro m' hhead' hchain' hlast'
    exact Nat.find_min' hex ⟨m', hhead', hchain', hlast', rfl⟩
  have hnodup : List.Nodup m := by
    by_contra hno
    obtain ⟨x, hdup⟩ := (List.exists_duplicate_iff_not_nodup).2 hno
    rcases duplicate_decompose (x := x) hdup with ⟨pre, mid, post, hsplit⟩
    let short : List σ := pre ++ x :: post
    have hchain_short : List.IsChain (M.EpsStep) short := by
      dsimp [short]
      apply epsChain_remove_cycle (M := M)
      simpa [hsplit] using hchain
    have hhead_short : short.head? = some q := by
      dsimp [short]
      have : (pre ++ x :: mid ++ x :: post).head? = some q := by
        simpa [hsplit] using hhead
      simpa [head?_remove_cycle] using this
    have hlast_short : short.getLast? = some s := by
      dsimp [short]
      have : (pre ++ x :: mid ++ x :: post).getLast? = some s := by
        simpa [hsplit] using hlast
      rw [getLast?_remove_cycle] at this
      exact this
    have hlen_split : m.length = short.length + (mid.length + 1) := by
      dsimp [short]
      rw [hsplit]
      simp [List.length_append, Nat.add_left_comm, Nat.add_comm]
    have hlt : short.length < m.length := by
      have : short.length < short.length + (mid.length + 1) := by
        exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
      rw [hlen_split]
      exact this
    have hn_eq : n = m.length := by simpa using hlen.symm
    have hlt' : short.length < n := by simpa [hn_eq] using hlt
    exact (not_lt_of_ge (hmin hhead_short hchain_short hlast_short)) hlt'
  cases m with
  | nil =>
      simp at hhead
  | cons q0 l =>
      have hq0 : q0 = q := by simpa using hhead
      subst q0
      refine ⟨l, hchain, ?_, hnodup⟩
      have : some ((q :: l).getLast (List.cons_ne_nil _ _)) = some s := by
        simpa [List.getLast?_eq_getLast_of_ne_nil] using hlast
      simpa using this

lemma epsReach_to_dfsReach_empty
  [DecidableEq σ]
  {q s : σ}
  (hreach : Relation.ReflTransGen (M.EpsStep) q s) :
  DfsEpsReach (M := M) ∅ q s := by
  rcases epsReach_exists_nodup_chain (M := M) hreach with ⟨l, hchain, hlast, hnodup⟩
  simpa [hlast] using
    epsChain_to_dfsReach (M := M) (V := ∅) (q := q) (l := l)
      hchain hnodup (by intro x hx; simp)

lemma dfs_complete
  [Fintype σ] [Fintype Γ] [FinEnum α]
  [DecidableEq σ] [DecidableEq α] [DecidableEq Γ]
  {q : σ} {t : Γ}
  (hex : ∃ w qf, M.evalFrom q w = some (qf, [t])) :
  t ∈ (M.dfs (a := a) q ∅ []).2 := by
  rcases hex with ⟨w, qf, hw⟩
  rcases (evalFrom_singleton_decompose (M := M) hw)
    with ⟨u, v, a₀, s, s', hw', hu, hstep, hv⟩
  have hreach_eps : Relation.ReflTransGen (M.EpsStep) q s :=
    evalFrom_empty_to_epsReach (M := M) hu
  have hreach_dfs : DfsEpsReach (M := M) ∅ q s :=
    epsReach_to_dfsReach_empty (M := M) hreach_eps
  exact dfs_complete_from_reach (M := M) (a := a) hreach_dfs ⟨a₀, s', hstep⟩

theorem computeSingleProducible_correct
  [ Fintype Γ ] [ Fintype σ ] [ a: FinEnum α ]
  [DecidableEq σ ] [DecidableEq α ] [DecidableEq Γ ] (q : σ) :
    (M.computeSingleProducible q).toFinset = { t | ∃ w qf, M.evalFrom q w = some (qf, [t])} := by
    ext t
    simp [computeSingleProducible]
    constructor
    · intro ht
      exact dfs_sound (M := M) (a := a) ht
    · intro ht
      exact dfs_complete (M := M) (a := a) ht

end FST
