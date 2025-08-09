import Mathlib.Computability.NFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.PFun
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Mathlib.Data.MLList.BestFirst
import Mathlib.Data.FinEnum
import Mathlib.Data.List.Nodup

universe u v w y

variable
  {α : Type u} {Γ : Type v} {σ : Type w}

structure FSA (α σ) where
  start : σ
  step : σ → α → Option σ
  accept : List σ

namespace FSA

variable (A : FSA α σ)

def evalFrom (s : σ) (l : List α) : Option σ :=
  match s, l with
  | s, [] => s
  | s, a :: as =>
    match (A.step s a) with
    | none => none
    | some s' => evalFrom s' as


@[simp]
theorem evalFrom_nil (s : σ) : A.evalFrom s [] = s := rfl

theorem evalFrom_cons (s : σ) (x : α) (xs : List α) (h : (A.step s x).isSome) :
    A.evalFrom s (x :: xs) = A.evalFrom ((A.step s x).get h) (xs) := by
  rw [Option.isSome_iff_exists] at h
  obtain ⟨a, h_s⟩ := h
  simp_all only [evalFrom, Option.get_some]



@[simp]
def eval : List α → Option σ :=
  A.evalFrom A.start

def acceptsFrom (s : σ) : Language α :=
  { w | ∃ f ∈ A.evalFrom s w, f ∈ A.accept }

def accepts : Language α := A.acceptsFrom A.start



def prefixLanguage : Language α :=
  {x | ∃ y, x ++ y ∈ A.accepts }

def isPrefix (w : List α) : Prop := w ∈ A.prefixLanguage

lemma reject_none {x : List α} (h : (A.eval x).isNone) : x ∉ A.accepts := by
  simp only [Option.isNone_iff_eq_none] at h
  by_contra h'
  simp only [accepts, acceptsFrom] at h'
  obtain ⟨f, hf₁, hf₂⟩ := h'
  unfold eval at h
  rw [h] at hf₁
  exact Option.not_mem_none f hf₁

theorem mem_accepts {x : List α} (h : (A.eval x).isSome) : x ∈ A.accepts ↔ (A.eval x).get h ∈ A.accept := by
  constructor
  ·
    intro h'
    obtain ⟨f, hf₁, hf₂⟩ := h'
    have : (A.eval x).get h = f := by
      exact Option.get_of_mem h hf₁
    rwa [this]
  ·
    intro ha
    exists (A.eval x).get h
    constructor
    · simp [eval, Option.coe_get]
    · exact ha

def adj (q : σ) [FinEnum α] [FinEnum σ] : Finset σ :=
    { p | ∃ a, (∃ s ∈ A.step q a, s = p) }

variable [DecidableEq σ]

instance (l : List α) : Decidable ( (A.eval l).isSome ) := inferInstance

instance [BEq σ] [LawfulBEq σ] (l : List α) {h : (A.eval l).isSome} :
  Decidable ((A.eval l).get h ∈ A.accept) :=
  List.instDecidableMemOfLawfulBEq ((A.eval l).get h) A.accept

instance [BEq σ] [LawfulBEq σ] (l : List α) : Decidable (l ∈ A.accepts) :=
  if h : (A.eval l).isSome then
    let s := (A.eval l).get h
    if h2 : s ∈ A.accept then
      isTrue ((mem_accepts A h).mpr h2)
    else
      isFalse ((mem_accepts A h).not.mpr h2)
  else
    isFalse (by
      intro h_contra
      simp [accepts, acceptsFrom, eval] at h_contra
      cases h_contra with
      | intro f hf =>
        have : (A.eval l).isSome := Option.isSome_iff_exists.mpr ⟨f, hf.1⟩
        contradiction
    )


--instance [BEq σ] [LawfulBEq σ] (l : List α) : Decidable (l ∈ A.prefixLanguage) :=
  --sorry

def toDFA : DFA α (Option σ) :=
  let step : Option σ → α → Option σ := fun s a =>
    match s, a with
    | none, _ => none
    | some x, a =>
      match (A.step x a) with
      | none => none
      | some s' => s'

  let accept := A.accept.map (fun s => some s)

  ⟨step, A.start, accept.toFinset.toSet⟩

lemma toDFA_none_not_accept : none ∉ A.toDFA.accept := by
  simp_all [toDFA]

@[simp]
lemma toDFA_iff_accept : some a ∈ A.toDFA.accept ↔ a ∈ A.accept := by
  simp_all [toDFA]

@[simp]
lemma toDFA_none_is_fail : ∀ (a : α), A.toDFA.step none a = none := by
  exact fun a => rfl

lemma toDFA_step_correct : ∀ (s : σ) (a : α), A.toDFA.step (some s) a = A.step s a := by
  refine fun s a => ?_
  simp [toDFA]
  split <;> rename_i heq <;> exact id (Eq.symm heq)

lemma toDFA_evalFrom_step_cons (s : σ) (x : α) (xs : List α) :
    A.toDFA.evalFrom (some s) (x :: xs) = A.toDFA.evalFrom (A.toDFA.step s x) (xs) := by
  simp [DFA.evalFrom]

@[simp]
theorem toDFA_evalFrom_correct : ∀ (s : σ) (l : List α), A.toDFA.evalFrom (some s) l = A.evalFrom s l := by
  refine fun s l => ?_
  simp [DFA.evalFrom]
  induction l generalizing s
  case nil =>
    unfold List.foldl
    simp
  case cons ih =>
    simp [List.foldl]
    expose_names
    cases h : A.step s head
    ·
      simp [evalFrom, h, toDFA_step_correct]
      exact List.foldl_fixed' (congrFun rfl) tail
    ·
      simp [evalFrom, h, toDFA_step_correct]
      apply ih

@[simp]
theorem toDFA_eval_correct : ∀ (l : List α), A.toDFA.eval l = A.eval l := by
  refine fun l => ?_
  simp [eval, DFA.eval]
  have : A.toDFA.start = some (A.start) := by exact rfl
  simp_all only [toDFA_evalFrom_correct]

theorem toDFA_correct : A.toDFA.accepts = A.accepts := by
  ext x
  simp only [DFA.mem_accepts, mem_accepts]
  cases h : A.eval x
  .
    have : A.toDFA.eval x = none := by simp_all only [toDFA_eval_correct]
    simp_all [acceptsFrom, h, eval, accepts]
    refine (iff_false_right ?_).mpr (by apply toDFA_none_not_accept)
    have : ¬(∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept) := by
      simp_all only [reduceCtorEq, false_and, exists_false, not_false_eq_true]
    exact fun a => this a
  .
    have : (A.eval x).isSome := by simp_all [h]
    rw [Option.isSome_iff_exists] at this
    obtain ⟨a, h'⟩ := this
    have : A.toDFA.eval x = a := by
      simp_all only [Option.some.injEq, toDFA_eval_correct]
    simp_all only [Option.some.injEq, DFA.eval, toDFA_iff_accept]
    constructor <;> rw [←h] at * <;> intro m
    .
      have : ∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept := by
        constructor <;> simp_all only [eval, Option.some.injEq]
        apply And.intro
        · exact rfl
        · simp_all only [toDFA, List.coe_toFinset, List.mem_map]
      exact this
    .
      have : ∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept := by exact m
      obtain ⟨f, h1, h2⟩ := this
      simp_all only [eval, Option.some.injEq]

variable
  [DecidableEq α]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ] [Fintype σ]

instance : DecidableEq (FSA α σ) := fun M N =>
  let toProd (fsa : FSA α σ) := (fsa.start, fsa.step, fsa.accept)

  have h₁ : Decidable (toProd M = toProd N) := by
    simp_all only [Prod.mk.injEq, toProd]
    exact instDecidableAnd

  have h_inj : ∀ a b : FSA α σ, toProd a = toProd b → a = b := by
    intro a b h_eq
    cases a
    cases b
    simp [toProd] at h_eq
    simp [mk.injEq]
    simp_all [Prod.mk.injEq, and_self, toProd]

  if h : toProd M = toProd N then
    isTrue (by exact h_inj M N h)
  else
    isFalse (by intro hMN; apply h; simp [toProd, hMN])

def stepList (S : List σ) (a : α) : List (Option σ) :=
  (S.map (fun s => A.step s a)).eraseDups

/-- A word ` w ` is accepted at ` q ` if there is ` q' ` such that ` evalFrom q w = q' `-/
def accepted (s : σ) (w : List α) : Prop := A.evalFrom s w ≠ none



def toNFA : NFA α σ where
  step s a := (A.step s a).elim ∅ (fun s => {s})
  start := {A.start}
  accept := A.accept.toFinset

#check Singleton
#check Subsingleton


omit [DecidableEq α] [Inhabited α] [Fintype α] [Fintype σ]
@[simp]
lemma toNFA_step_Subsingleton (A : FSA α σ) (s : σ) (a : α) :
    Subsingleton (A.toNFA.step s a) := by
  simp [toNFA, Option.elim]
  split
  simp_all
  exact Set.subsingleton_empty

lemma toNFA_evalFrom_step_cons (s : σ) (x : α) (xs : List α) :
    A.toNFA.evalFrom {s} (x :: xs) = A.toNFA.evalFrom (A.toNFA.step s x) (xs) := by
  simp [NFA.evalFrom, NFA.stepSet]

lemma toNFA_evalFrom_step_cons_empty (x : α) (xs : List α) :
    A.toNFA.evalFrom ∅ (x :: xs) = A.toNFA.evalFrom ∅ (xs) := by
  simp [NFA.evalFrom, NFA.stepSet]

lemma toNFA_evalFrom_empty (x : List α) :
    A.toNFA.evalFrom ∅ x = ∅ := by
  simp [NFA.evalFrom]
  rw [List.foldl.eq_def]
  split; rfl
  expose_names
  induction l
  case nil =>
    rw [←NFA.evalFrom]
    simp [NFA.evalFrom_nil]
  case cons ih =>
    rw [←NFA.evalFrom] at *
    simp_all [NFA.evalFrom_nil, toNFA_evalFrom_step_cons_empty]

lemma toNFA_evalFrom_Subsingleton (A : FSA α σ) (s : σ) (l : List α) :
    Subsingleton (A.toNFA.evalFrom {s} l) := by
  have h : ∀ (S : Set σ), A.toNFA.evalFrom S [] = S := by exact (fun S => rfl)
  induction l generalizing s
  case nil =>
    rw [h {s}]
    exact Unique.instSubsingleton
  case cons a as ih =>
    simp_all only [NFA.evalFrom_nil, implies_true]
    rw [toNFA_evalFrom_step_cons]
    have h₁ : ∀ (c : α) (s : σ), A.toNFA.step s c = (A.step s c).elim ∅ (fun s => {s}) := by intro c; exact fun s => rfl
    rw [h₁]
    simp only [Option.elim]
    split
    dsimp
    apply ih _
    simp only [NFA.evalFrom, NFA.stepSet, NFA.stepSet_empty]
    rw [List.foldl.eq_def]
    split
    exact IsEmpty.instSubsingleton
    rw [←NFA.evalFrom]
    simp [NFA.stepSet_empty, toNFA_evalFrom_empty]

end FSA

structure FST (α Γ σ) where
  start : σ
  step : σ → α → Option (σ × List Γ)
  accept : List σ

namespace FST

variable
  (M : FST α Γ σ)

/-- `M.evalFrom` evaluates the list of characters `l` starting at `s`, and returns the final state
  along with the contents of the output tape if all transitions are valid.
  If a transition doesn't exist at any character of `l`, return `(none, [])`.  -/
def evalFrom (s : σ) (l : List α) : Option (σ × List Γ) :=
  match l with
  | [] => some (s, [])
  | a :: as =>
    match (M.step s a) with
    | none => none
    | some (s', S) =>
      match evalFrom s' as with
      | none => none
      | some (s'', T) => (s'', S ++ T)

def eval (input : List α) : Option (σ × List Γ) :=
  M.evalFrom M.start input

@[simp]
theorem evalFrom_nil (s : σ) : M.evalFrom s [] = some (s, []) := rfl

@[simp]
private lemma evalFrom_cons_fst (s : σ) (x : α) (xs : List α)
    (h₀ : M.step s x = some (s', S)) (h₁ : M.evalFrom s (x :: xs) = some r) (h₂ : M.evalFrom s' xs = some t) :
    r.1 = t.1 := by
  simp_all only [evalFrom, Option.some.injEq]
  subst h₁
  simp_all only

@[simp]
private lemma evalFrom_cons_snd (s : σ) (x : α) (xs : List α)
    (h₀ : M.step s x = some (s', S)) (h₁ : M.evalFrom s (x :: xs) = some r) (h₂ : M.evalFrom s' xs = some t) :
    r.2 = S ++ t.2 := by
  simp_all only [evalFrom, Option.some.injEq]
  subst h₁
  simp_all only

@[simp]
theorem evalFrom_singleton (s : σ) (a : α) :
    M.evalFrom s [a] = M.step s a := by
  unfold evalFrom
  simp_all only [evalFrom_nil, List.append_nil]
  split <;> rename_i heq <;> exact id (Eq.symm heq)

@[simp]
theorem evalFrom_cons (s : σ) (x : α) (xs : List α)
    (h₀ : M.step s x = some (s', S)) (h₁ : M.evalFrom s' xs = some (s'', T)) :
      M.evalFrom s (x :: xs) = (s'', S ++ T) := by
  simp_all only [evalFrom]

theorem evalFrom_append (s : σ) (xs ys : List α) : M.evalFrom s (xs ++ ys) =
  match M.evalFrom s xs with
  | none => none
  | some t => (M.evalFrom t.1 ys).map (fun (s', ts) => (s', t.2 ++ ts)) := by
  induction xs generalizing s
  case nil => simp [evalFrom]
  case cons head tail ih =>
    cases h : M.step s head with
    | none => simp [evalFrom, h]
    | some sp =>
      simp[evalFrom, h, ih]
      cases h' : M.evalFrom sp.1 tail with
      | none => simp [h']
      | some sp2 =>
        simp [h']
        cases h2 : M.evalFrom sp2.1 ys <;> simp [h2]

def acceptsFrom (s : σ) : Language α :=
  { w | ∃ f ∈ M.evalFrom s w, f.1 ∈ M.accept }

def accepts : Language α := M.acceptsFrom M.start

def transducesTo (w : List α) (v : List Γ) : Prop :=
  if h : ((M.eval w).isSome) then
    ((M.eval w).get h).2 = v ∧ ((M.eval w).get h).1 ∈ M.accept
  else
    False



lemma reject_none {x : List α} (h : (M.eval x).isNone) : x ∉ M.accepts := by
  simp only [Option.isNone_iff_eq_none] at h
  by_contra h'
  simp only [accepts, acceptsFrom] at h'
  obtain ⟨f, hf₁, hf₂⟩ := h'
  unfold eval at h
  rw [h] at hf₁
  exact Option.not_mem_none f hf₁

theorem mem_accepts {x : List α} (h : (M.eval x).isSome) : x ∈ M.accepts ↔ ((M.eval x).get h).1 ∈ M.accept := by
  constructor
  ·
    intro h'
    obtain ⟨f, hf₁, hf₂⟩ := h'
    have : (M.eval x).get h = f := by
      exact Option.get_of_mem h hf₁
    rwa [this]
  ·
    intro ha
    exists (M.eval x).get h
    constructor
    · simp [eval, Option.coe_get]
    · exact ha

def mkStep [DecidableEq α] [DecidableEq σ] (transitions : List (σ × α × Option (σ × List Γ))) : σ → α → Option (σ × List Γ) :=
  fun s a =>
    transitions.find? (fun (s', a', _) => s = s' ∧ a = a')
    |>.map (fun (_, _, ts) => ts)
    |>.getD (none)

def adj (q : σ) [FinEnum α] [FinEnum σ] : Finset σ :=
    { p | ∃ a, (∃ s ∈ M.step q a, s.1 = p)}

def producible (q : σ) : Language Γ :=
    { t | ∃ w, (∃ r ∈ M.evalFrom q w, r.2 = t) }

def singleProducible (q : σ) : Set Γ :=
    { t | ∃ w, (∃ r ∈ M.evalFrom q w, r.2 = [t]) }

-- A small measure-decrease fact used for the recursive call on ε-edges.
lemma compl_card_lt_of_insert
  [Fintype σ] [DecidableEq σ]
  {vis : Finset σ} {s : σ} (h : s ∉ vis) :
  ((vis ∪ {s})ᶜ).card < (visᶜ).card := by
  simp
  observe h_sub : visᶜ ∩ {s}ᶜ ⊆ visᶜ
  have h_neq : visᶜ ∩ {s}ᶜ ≠ visᶜ := by simp [h]
  observe h_proper_sub : visᶜ ∩ {s}ᶜ ⊂ visᶜ
  observe h_goal : (visᶜ ∩ {s}ᶜ).card < (visᶜ).card
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
      simp [h₀]
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
            simp_all [evalFrom]
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
              simp_all [h₁, Prod.mk.injEq]
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
              simp_all [hT]
            simp [h₀, h₁, hs, this]

lemma evalFrom_cons_singleton_iff
  (M : FST α Γ σ) {s s'' : σ} {a : α} {as : List α} {t : Γ} :
  M.evalFrom s (a :: as) = some (s'', [t])
    ↔ (∃ s', M.step s a = some (s', [t]) ∧ M.evalFrom s' as = some (s'', []))
     ∨ (∃ s', M.step s a = some (s', []) ∧ M.evalFrom s' as = some (s'', [t])) := by
  constructor
  · intro h
    rcases (evalFrom_cons_some_iff (M := M)).mp h with ⟨s', S, T, hstep, heval, hU⟩
    have : S ++ T = [t] := symm hU
    -- Only two ways a concat can be a singleton
    cases S using List.rec with
    | nil =>
        simp at this
        right
        refine ⟨s', by simp [hstep], ?_⟩
        simpa [this] using heval
    | @cons γ S =>
        -- then S ++ T has length ≥ 2 unless S = [] and T = [t], so force S = [t] and T = []
        cases S using List.rec with
        | nil =>
            -- S = [γ], and [γ] ++ T = [t] ⇒ γ = t and T = []
            simp at this
            rcases this with ⟨hγ, hT⟩
            left
            refine ⟨s', ?_, ?_⟩
            · simp [hstep, hγ]
            · simpa [hT] using heval
        | @cons γ₂ S₂ =>
            -- length ≥ 2, impossible
            cases this

  · intro h
    rcases h with ⟨s', hstep, heval⟩ | ⟨s', hstep, heval⟩
    · -- head outputs [t], tail outputs []
      exact
        (evalFrom_cons_some_iff (M := M) (s := s) (s'' := s'') (a := a) (as := as) (U := [t])).mpr
          ⟨s', [t], [], hstep, by simpa using heval, by simp⟩
    · -- head outputs [], tail outputs [t]
      exact
        (evalFrom_cons_some_iff (M := M) (s := s) (s'' := s'') (a := a) (as := as) (U := [t])).mpr
          ⟨s', [], [t], hstep, by simpa using heval, by simp⟩

/-- If `t` appears in the second component of `dfs`, then either it was already
in `ret`, or there is a word from `s` producing exactly `[t]`. -/
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
                    simp [hstepx, hres, h₀]
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
                            simp [evalFrom_cons_singleton_iff (M := M)]
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


theorem computeSingleProducible_correct
  [ Fintype Γ ] [ Fintype σ ] [ a: FinEnum α ]
  [DecidableEq σ ] [DecidableEq α ] [DecidableEq Γ ] (q : σ) :
    (M.computeSingleProducible q).toFinset = { t | ∃ w qf, M.evalFrom q w = some (qf, [t])} := by
    sorry


universe u_1 u_2


def compose_fun_step { β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (s₁ : σ) (s₂ : τ) (x : α) : Option ((σ × τ) × List β) :=
  match M₁.step s₁ x with
  | none => none
  | some (s₁', S) =>
    match (M₂.evalFrom s₂ S) with
    | none => none
    | some (s₂', T) => ((s₁', s₂'), T)

/-- The composition of two FSTs `M₁`, `M₂` with `M₁.oalph = M₂.alph` gives a new FST `M'`, where
  `M'.alph = M₁.alph`, `M'.oalph = M₂.oalph` and `M'.eval w = M₂.eval (M₁.eval w)` -/
def compose {β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) : FST α β (σ × τ) :=
  let start : σ × τ := (M₁.start, M₂.start)
  let accept := M₁.accept.flatMap (fun s₁ =>
    M₂.accept.map (fun s₂ =>
      (s₁, s₂)
    )
  )
  let step : (σ × τ) → α → Option ((σ × τ) × List β) := fun s a =>
    match s, a with
    | (s₁, s₂), a => compose_fun_step M₁ M₂ s₁ s₂ a

  ⟨ start, step, accept⟩

def compose_fun_evalFrom { β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (s₁ : σ) (s₂ : τ) (w : List α) : Option ((σ × τ) × List β) :=
  match M₁.evalFrom s₁ w with
  | none => none
  | some (s₁', S) =>
    match (M₂.evalFrom s₂ S) with
    | none => none
    | some (s₂', T) => ((s₁', s₂'), T)

-- todo make this less casework, very bad right now
lemma compose_fun_step_cons { β : Type u_1 } { τ : Type u_2 }
  (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (s₁ : σ) (s₂ : τ) (w : α) (ws : List α) :
    compose_fun_evalFrom M₁ M₂ s₁ s₂ (w :: ws) =
      match compose_fun_step M₁ M₂ s₁ s₂ w with
      | none => none
      | some ((s₁', s₂'), T) =>
        (compose_fun_evalFrom M₁ M₂ s₁' s₂' ws).map (fun ((s₁'', s₂''), T') => ((s₁'', s₂''), T ++ T'))
  := by
  simp[compose_fun_evalFrom, compose_fun_step]
  simp[evalFrom]
  cases h₁ : M₁.step s₁ w with
  | none =>
    simp[evalFrom, h₁]
  | some sp =>
    simp
    cases h₃ : M₂.evalFrom s₂ sp.2 with
    | none =>
      split <;> simp_all[h₃]
      rename_i T' h_eq
      split at h_eq <;> simp_all
      rename_i T'' _
      have := M₂.evalFrom_append s₂ sp.2 T''
      simp_all
    | some sp2 =>
      split <;> simp_all[h₃]
      next h_eq =>
        split at h_eq <;> simp_all
      next h_eq =>
        split at h_eq <;> simp_all
        rename_i T'' _
        have := M₂.evalFrom_append s₂ sp.2 T''
        simp_all
        split <;> simp_all
        rename_i heq'
        cases h₄ : M₂.evalFrom sp2.1 T'' with
        | none => simp_all[h₄]
        | some dst =>
          simp_all[h₄]
          obtain ⟨a, ⟨b, hab⟩⟩ := heq'
          simp_all

def compose_fun_eval {β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (w : List α) : Option (List β) :=
  (compose_fun_evalFrom M₁ M₂ M₁.start M₂.start w).map Prod.snd

def compose_correct { β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (w : List α) :
  ((M₁.compose M₂).eval w).map Prod.snd = compose_fun_eval M₁ M₂ w := by
  simp[eval, compose_fun_eval]
  have lem :
    ∀ { s₁ s₂ },
      (M₁.compose M₂).evalFrom (s₁, s₂) w = compose_fun_evalFrom M₁ M₂ s₁ s₂ w  := by
    intro s₁ s₂
    induction w generalizing s₁ s₂
    simp_all[compose_fun_evalFrom]
    case cons head tail ih =>
      have := compose_fun_step_cons M₁ M₂ s₁ s₂ head tail
      simp[←ih] at this
      rw[this]
      simp[evalFrom]
      conv =>
        pattern M₁.compose M₂
        simp[compose]
      simp
      split <;> simp_all
      simp[Option.map]
      split <;> simp_all
  exact congrArg (Option.map Prod.snd) lem



variable {β τ}
  (M₁ : FST α Γ σ) (M₂ : FST Γ β τ)

@[simp]
lemma compose_fun_evalFrom_nil (s₁ : σ) (s₂ : τ) : compose_fun_evalFrom M₁ M₂ s₁ s₂ [] = some ((s₁, s₂), []) := by
  exact rfl


lemma compose_fun_exists_step (s₁ : σ) (s₂ : τ) (x : α)
    (h₁ : M₁.compose_fun_evalFrom M₂ s₁ s₂ [x] = some headOut) :
      ∃ step_x, M₁.evalFrom s₁ [x] = some step_x := by
  simp_all only [compose_fun_evalFrom, Prod.exists]
  split at h₁ <;> simp_all [Option.some.injEq, Prod.mk.injEq, exists_and_left, exists_eq', and_true]

lemma compose_fun_evalFrom_singleton (s₁ : σ) (s₂ : τ) (x : α)
    (h₀ : M₁.step s₁ x = some (s', S))
    (h₁ : M₂.evalFrom s₂ S = some (s'', T)) :
      compose_fun_evalFrom M₁ M₂ s₁ s₂ [x] = some ((s', s''), T) := by
  unfold compose_fun_evalFrom
  simp_all only [evalFrom_singleton]




variable (A : FSA α σ)

/-

def toFSA : FSA α σ :=
  let step := fun s a => (M.step s a).1
  ⟨M.alph, M.states, M.start, step, M.accept⟩

@[simp]
lemma toFSA_step_correct : ∀ (s : σ) (a : α), M.toFSA.step s a = (M.step s a).1 := by
  exact fun s a => rfl

@[simp]
lemma toFSA_evalFrom_correct : ∀ (s : σ) (l : List α), M.toFSA.evalFrom s l = (M.evalFrom s l).1 := by
  refine fun s l => ?_
  induction l generalizing s
  case nil =>
    simp [FSA.evalFrom, evalFrom]
  case cons head tail ih =>
    simp [FSA.evalFrom, evalFrom]
    cases h : M.step s head
    rename_i next output
    cases next
    ·
      simp [FSA.evalFrom, evalFrom, toFSA_step_correct, h]
    ·
      rename_i s'
      simp [FSA.evalFrom, evalFrom, toFSA_step_correct, h]
      exact ih s'

lemma toFSA_eval_correct : ∀ (l : List α), M.toFSA.eval l = (M.eval l).1 := by
  refine fun l => ?_
  simp [eval, FSA.eval]
  exact rfl

theorem toFSA_correct : M.toFSA.accepts = M.accepts := by
  ext x
  have h₀ : M.toFSA.eval x = (M.eval x).1 := by exact toFSA_eval_correct M x
  cases h : (M.eval x).1
  .
    have : M.toFSA.eval x = none := by simp_all only
    refine Eq.to_iff ?_
    have h₁ : x ∉ M.accepts := by
      refine reject_none M ?_
      exact Option.isNone_iff_eq_none.mpr h
    have h₂ : x ∉ M.toFSA.accepts := by
      refine FSA.reject_none M.toFSA ?_
      exact Option.isNone_iff_eq_none.mpr this
    simp_all only
  .
    have : ∃ a, (M.eval x).1 = some a := by simp [h]
    obtain ⟨a, ha⟩ := this
    have : (M.toFSA.eval x) = a := by
      simp [FSA.eval]
      exact ha
    constructor <;> rw [←h] at * <;> intro m
    .
      have : ∃ f ∈ M.toFSA.evalFrom M.toFSA.start x, f ∈ M.toFSA.accept := by exact m
      simp_all only [Option.isSome_some, mem_accepts, FSA.mem_accepts]
      exact m
    .
      have : ∃ f ∈ M.toFSA.evalFrom M.toFSA.start x, f ∈ M.toFSA.accept := by
        simp_all only [toFSA_evalFrom_correct, Option.mem_def]
        exact m
      exact this



variable
  [DecidableEq α] [DecidableEq σ]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ] [Fintype σ]

def transitions (fst : FST α Γ σ) : List (σ × α × (Option σ × List Γ)) :=
  fst.states.flatMap (fun q =>
    (fst.alph.map (fun c =>
        (q, c, fst.step q c)
      )
    )
  )

def mkStep (transitions : List (σ × α × (Option σ × List Γ))) : σ → α → (Option σ × List Γ) :=
  fun s a =>
    transitions.find? (fun (s', a', _) => s = s' && a = a')
    |>.map (fun (_, _, ts) => ts)
    |>.getD (none, [])

-/


end FST

-- same as FST, but Option α allows for ε-transitions
structure εFST (α Γ σ) where
  alph : List α
  oalph : List Γ
  states : List σ
  start : σ
  step : σ → Option α → (Option σ × List Γ)
  accept : List σ

namespace εFST


end εFST


instance [DecidableEq σ] : Coe (FSA α σ) (NFA α σ) := ⟨fun fsa => fsa.toNFA⟩

instance [DecidableEq σ] : Coe (FSA α σ) (DFA α (Option σ)) := ⟨fun fsa => fsa.toDFA⟩
