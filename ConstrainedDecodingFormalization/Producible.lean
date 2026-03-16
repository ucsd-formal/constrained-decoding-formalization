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
  if h_vis : curr ∈ vis then (vis, ret)
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
    exact compl_card_lt_of_insert h_vis

def computeSingleProducible
  [ Fintype Γ ] [ Fintype σ ] [ a: FinEnum α ]
  [DecidableEq σ ] [DecidableEq α ] [DecidableEq Γ ]
  (q : σ) : List Γ :=
  (dfs M q {} []).snd

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

lemma trim_eps_into_V
  [DecidableEq σ] {V : Finset σ} {q₀ s s₁ : σ} {b : α} {u'' : List α}
  (hnotV : q₀ ∉ V)
  (hstep : M.step q₀ b = some (s₁, []))
  (hjump : s₁ ∈ V)
  (hu    : M.evalFrom q₀ (b :: u'') = some (s, [])) :
  ∃ u' : List α, u'.length < (b :: u'').length ∧
    M.evalFrom q₀ u' = some (s, []) := by
  sorry

lemma dfs_complete
  [Fintype σ] [Fintype Γ] [FinEnum α]
  [DecidableEq σ] [DecidableEq α] [DecidableEq Γ]
  {q : σ} {t : Γ}
  (hex : ∃ w qf, M.evalFrom q w = some (qf, [t])) :
  t ∈ (M.dfs (a := a) q ∅ []).2 := by
  rcases hex with ⟨w, qf, hw⟩
  rcases (evalFrom_singleton_decompose (M := M) hw)
    with ⟨u, v, a₀, s, s', hw', hu, hstep, hv⟩

  let P : ℕ → Prop := fun n =>
    ∀ V q₀, (Vᶜ).card = n → q₀ ∉ V →
    ∀ u : List α, M.evalFrom q₀ u = some (s, []) →
    t ∈ (M.dfs (a := a) q₀ V []).2

  have step : ∀ n, (∀ m, m < n → P m) → P n := by
    sorry
  sorry

theorem computeSingleProducible_correct
  [ Fintype Γ ] [ Fintype σ ] [ a: FinEnum α ]
  [DecidableEq σ ] [DecidableEq α ] [DecidableEq Γ ] (q : σ) :
    (M.computeSingleProducible q).toFinset = { t | ∃ w qf, M.evalFrom q w = some (qf, [t])} := by
    sorry

end FST
