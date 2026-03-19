import Mathlib.Computability.NFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.PFun
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Mathlib.Data.FinEnum
import Mathlib.Data.List.Nodup

/-!
# Automata and transducers

This file contains the core state-machine semantics used throughout the
development.

* `FSA` models deterministic finite-state acceptors over an input alphabet.
* `FST` models deterministic finite-state transducers with list-valued outputs.

The later lexer, producibility, realizable-sequence, and grammar-constrained
decoding files all build on the execution semantics and language notions defined
here.
-/

universe u v w y

variable
  {α : Type u} {Γ : Type v} {σ : Type w}

/-- A deterministic finite-state acceptor over input alphabet `α`. -/
structure FSA (α σ) where
  start : σ
  step : σ → α → Option σ
  accept : List σ

/-! ### FSA: core structure and evaluation -/

namespace FSA

variable (A : FSA α σ)

/-- Evaluate an FSA from state `s` on input word `l`.

The result is the final state when every transition is defined, and `none`
otherwise. This is the basic operational semantics used to define the accepted
and intermediate languages of the automaton.
-/
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

theorem evalFrom_append (s : σ) (xs ys : List α) : A.evalFrom s (xs ++ ys) =
  match A.evalFrom s xs with
  | none => none
  | some t => (A.evalFrom t ys) := by
  induction xs generalizing s
  case nil => simp [evalFrom]
  case cons head tail ih =>
    cases h : A.step s head with
    | none => simp [evalFrom, h]
    | some sp =>
      simp[evalFrom, h, ih]

/-- Evaluate the automaton from its start state. -/
@[simp]
def eval : List α → Option σ :=
  A.evalFrom A.start

/-- The language accepted when the automaton starts in state `s`. -/
def acceptsFrom (s : σ) : Language α :=
  { w | ∃ f, A.evalFrom s w = some f ∧ f ∈ A.accept }

/-- The language accepted from the designated start state. -/
def accepts : Language α := A.acceptsFrom A.start

/-- Bidirectional characterization of acceptance. -/
def accepts_iff {w : List α} : w ∈ A.accepts ↔
  ∃ f, A.evalFrom A.start w = some f ∧ f ∈ A.accept := by
  simp [accepts, acceptsFrom]
  rfl

/-- The prefix closure of the accepted language.

This describes the words that have not yet been ruled out by the automaton, and
is later used to express incremental lexing properties.
-/
def prefixLanguage : Language α :=
  {x | ∃ y, x ++ y ∈ A.accepts }

/-- An automaton is `pruned` if every state is both reachable from the start
and can still reach an accepting state. -/
def pruned : Prop :=
  ∀ σ, (∃ w f, some f = A.evalFrom σ w ∧ f ∈ A.accept) ∧
      (∃ w, some σ = A.evalFrom A.start w)

/-- The language of inputs that have not yet failed from the start state. -/
def intermediateLanguage : Language α :=
  {w | A.eval w ≠ none }

/-- For a pruned automaton, "not yet rejected" coincides with being a prefix of
some accepted word. -/
def pruned_prefixLanguage (h : A.pruned) : A.intermediateLanguage = A.prefixLanguage := by
  ext w
  simp[intermediateLanguage, prefixLanguage]
  constructor
  . intro h1
    cases h3: A.evalFrom A.start w with
    | none =>
      have : ¬A.evalFrom A.start w = none := h1
      contradiction
    | some s =>
      simp[pruned] at h
      have ⟨u, f, hf1, hf2⟩ := (h s).left
      exists u
      exists f
      simp[h3, evalFrom_append, hf1, hf2]
  . intro h1
    let dst := A.eval w
    simp[accepts, acceptsFrom] at h1
    have ⟨f, hf1, hf2⟩ := h1
    simp[evalFrom_append] at hf2
    cases h3: A.evalFrom A.start w with
    | none => simp[h3] at hf2
    | some s =>
      have : ¬A.evalFrom A.start w = none := by simp[h3]
      exact this

/-! ### FSA: decidability and conversions -/

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
    rwa [Option.get_of_mem h hf₁]
  ·
    intro ha
    exact ⟨_, by simp [eval], ha⟩

/-- The set of states reachable from `q` in one input step. -/
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
      simp [accepts, acceptsFrom] at h_contra
      cases h_contra with
      | intro f hf =>
        have : (A.eval l).isSome := Option.isSome_iff_exists.mpr ⟨f, hf.1⟩
        contradiction
    )


--instance [BEq σ] [LawfulBEq σ] (l : List α) : Decidable (l ∈ A.prefixLanguage) :=
  --sorry

/-! ### FSA to DFA conversion -/

/-- View a deterministic FSA as a DFA whose extra `none` state represents
failure. This is the version used when relating the development to mathlib's
`DFA` interface. -/
def toDFA : DFA α (Option σ) :=
  let step : Option σ → α → Option σ := fun s a =>
    match s, a with
    | none, _ => none
    | some x, a =>
      match (A.step x a) with
      | none => none
      | some s' => s'

  let accept := A.accept.map (fun s => some s)

  ⟨step, A.start, SetLike.coe accept.toFinset⟩

lemma toDFA_none_not_accept : none ∉ A.toDFA.accept := by
  simp_all [toDFA]

@[simp]
lemma toDFA_iff_accept : some a ∈ A.toDFA.accept ↔ a ∈ A.accept := by
  simp_all [toDFA]

@[simp]
lemma toDFA_none_is_fail : ∀ (a : α), A.toDFA.step none a = none :=
  fun _ => rfl

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

/-- The DFA obtained from `toDFA` accepts exactly the same language as the
original FSA. -/
theorem toDFA_correct : A.toDFA.accepts = A.accepts := by
  ext x
  change A.toDFA.eval x ∈ A.toDFA.accept ↔ ∃ f, A.eval x = some f ∧ f ∈ A.accept
  rw [toDFA_eval_correct]
  cases A.eval x with
  | none =>
      simp [toDFA_none_not_accept]
  | some s =>
      simp [toDFA_iff_accept]

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
    simp_all [and_self]

  if h : toProd M = toProd N then
    isTrue (by exact h_inj M N h)
  else
    isFalse (by intro hMN; apply h; simp [toProd, hMN])

/-- Apply one input symbol to a list of states and deduplicate the resulting
optional successor states. -/
def stepList (S : List σ) (a : α) : List (Option σ) :=
  (S.map (fun s => A.step s a)).eraseDups

/-- A word is accepted from `s` when some run from `s` succeeds. This is the
`Prop`-valued counterpart to `acceptsFrom`. -/
def accepted (s : σ) (w : List α) : Prop := A.evalFrom s w ≠ none

/-! ### FSA to NFA conversion -/

/-- View a deterministic FSA as an NFA with singleton transition sets.

This lets later files reuse mathlib's NFA language and reachability interface
without changing the underlying automaton.
-/
def toNFA : NFA α σ where
  step s a := (A.step s a).elim ∅ (fun s => {s})
  start := {A.start}
  accept := A.accept.toFinset


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
    simp_all

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
    simp only [NFA.evalFrom]
    rw [List.foldl.eq_def]
    split
    exact IsEmpty.instSubsingleton
    rw [←NFA.evalFrom]
    simp [NFA.stepSet_empty, toNFA_evalFrom_empty]

end FSA

/-! ### FST: core structure and evaluation -/

/-- A deterministic finite-state transducer from inputs `α` to output words
over `Γ`. -/
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

/-- Evaluate `M` from `s` and prepend an existing output seed.

This is useful when comparing the recursive semantics of `evalFrom` with fold-
based or compositional formulations.
-/
def evalFrom_seed (s : σ) (l : List α) (seed: List Γ) :=
      match M.evalFrom s l with
      | none => none
      | some (s', S) => some (s', seed ++ S)

/-- One step of the fold-based evaluator for `FST`.

This version is retained because later lexer constructions are more naturally
expressed with `List.foldl`.
-/
def evalFrom_fold_step (acc: Option (σ × List Γ)) (a : α) : Option (σ × List Γ) :=
  match acc with
  | none => none
  | some (s', ts) =>
    match M.step s' a with
    | none => none
    | some (s'', S) => some (s'', ts ++ S)

@[simp]
lemma evalFrom_nil_seed (s : σ) (l : List α) :
    M.evalFrom_seed s l [] = M.evalFrom s l := by
  simp [evalFrom_seed]
  split <;> simp_all

/-- Fold-based evaluation with an explicit initial output seed. -/
def evalFrom_fold_seed (s: σ) (l: List α) (seed: List Γ) : Option (σ × List Γ) :=
  List.foldl M.evalFrom_fold_step (some (s, seed)) l

@[simp]
lemma evalFrom_fold_seed_nil (l : List α) :
  List.foldl M.evalFrom_fold_step none l = none :=
  List.foldl_fixed' (congrFun rfl) l

/-- Fold-based evaluation without an explicit initial output seed. -/
@[simp]
def evalFrom_fold (s : σ) (l : List α) : Option (σ × List Γ) :=
  M.evalFrom_fold_seed s l []

/-- Evaluate the transducer from its designated start state. -/
@[simp]
def eval (input : List α) : Option (σ × List Γ) :=
  M.evalFrom M.start input

/-- Fold-based evaluation from the designated start state. -/
@[simp]
def eval_fold (input : List α) : Option (σ × List Γ) :=
  M.evalFrom_fold M.start input

/-- The fold-based evaluator with a seed agrees with the seed-based `evalFrom_seed`. -/
def evalFrom_fold_seed_eq_evalFrom_seed (s : σ) (l : List α) (seed: List Γ) :
    M.evalFrom_fold_seed s l seed = M.evalFrom_seed s l seed := by
  induction l generalizing s seed
  case nil =>
    simp [evalFrom_seed, evalFrom, evalFrom_fold_seed]
  case cons head tail ih =>
    cases hc: M.evalFrom_fold_step (some (s, seed)) head
    simp_all[evalFrom_fold_step]
    .
      cases hs: M.step s head
      <;> simp[hs] at hc
      simp [evalFrom_seed, evalFrom, evalFrom_fold_seed, hs]
      simp[evalFrom_fold_step, hs]
    case some sp =>
      have ⟨q', seed'⟩ := sp
      simp[evalFrom_fold_seed, hc]
      have : M.evalFrom_seed s (head :: tail) seed = M.evalFrom_seed q' tail seed' := by
        simp[evalFrom_seed]
        rw[evalFrom]
        simp[evalFrom_fold_step] at hc
        cases hs: M.step s head
        <;> simp[hs] at hc
        rename_i step_contr
        simp[hc]
        cases M.evalFrom q' tail with
        | none => simp
        | some r =>
          simp
          rw[←List.append_assoc]
          simp[hc]
      simp[this]
      have ih' := ih q' seed'
      simp[evalFrom_fold_seed] at ih'
      exact ih'

/-- The fold-based evaluator agrees with the recursive `evalFrom`. -/
def evalFrom_fold_eq_evalFrom (s : σ) (l : List α) :
    M.evalFrom_fold s l = M.evalFrom s l := by
  have := evalFrom_fold_seed_eq_evalFrom_seed M s l []
  have g :  M.evalFrom_fold_seed s l [] = M.evalFrom_fold s l := by
    simp [evalFrom_fold]
  rw[←g]
  simp[this]

def eval_fold_eq_eval (l : List α) :
    M.eval_fold l = M.eval l :=
  evalFrom_fold_eq_evalFrom M M.start l

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

/-- Bidirectional characterization of a successful cons-step run. -/
theorem evalFrom_cons_some_iff {s s'' : σ} {a : α} {as : List α} {U : List Γ} :
    M.evalFrom s (a :: as) = some (s'', U)
      ↔ ∃ s' S T,
        M.step s a = some (s', S) ∧
        M.evalFrom s' as = some (s'', T) ∧
        U = S ++ T := by
  constructor
  · intro h
    simp only [evalFrom] at h
    cases hs : M.step s a with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨s₁, S⟩ := p
      simp [hs] at h
      cases he : M.evalFrom s₁ as with
      | none => simp [he] at h
      | some p2 =>
        obtain ⟨s₂, T⟩ := p2
        simp [he] at h
        obtain ⟨heq, hout⟩ := h
        subst heq
        exact ⟨s₁, S, T, rfl, he, hout.symm⟩
  · rintro ⟨s', S, T, hs, he, rfl⟩
    exact evalFrom_cons M s a as hs he

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
      | none => simp
      | some sp2 =>
        simp
        cases h2 : M.evalFrom sp2.1 ys <;> simp

/-! ### FST: transition traces -/

/-- Recover the concrete transition trace taken by a successful run.

This is mainly used in proof arguments that need to inspect runs step by step
rather than only through the aggregate output of `evalFrom`.
-/
def stepList (s : σ) (a : List α) : Option (List (σ × α × σ × List Γ)) :=
  match a with
  | [] => some ([])
  | x :: xs =>
    match M.step s x with
    | none => none
    | some s' =>
      match stepList s'.fst xs with
      | none => none
      | some next => some ( (s, x, s'.fst, s'.snd) :: next )

/-- The input symbols recorded by `stepList` match the original input word. -/
lemma stepList_w ( s: σ) (w: List α) :
  match M.stepList s w with
  | none => True
  | some lst => lst.map (fun (_, x, _, _) => x) = w := by
  induction w generalizing s
  case nil => simp [stepList]
  case cons head tail ih =>
    simp [stepList]
    cases h: M.step s head
    simp
    case some step =>
      simp at ih ⊢
      have ih' := ih step.1
      cases h' : M.stepList step.1 tail
      <;> simp[h'] at ih'
      simp
      simp[ih']

lemma stepList_mem_w ( s: σ) (w: List α) :
  match M.stepList s w with
  | none => True
  | some lst => ∀ l ∈ lst, l.2.1 ∈ w := by
  have := M.stepList_w s w
  cases h: M.stepList s w
  case none => simp [h] at this; exact this
  case some lst =>
    simp only [h] at this ⊢
    rw[←this]
    simp only [List.mem_map]
    intro l  hl
    exists l

/-- `stepList` produces a trace of the same length as the input word. -/
lemma stepList_len (s: σ) (w: List α) :
  match M.stepList s w with
  | none => True
  | some lst => lst.length = w.length := by
  induction w generalizing s
  case nil =>
    simp [stepList]
  case cons head tail ih =>
    simp [stepList]
    cases h: M.step s head
    simp
    case some step =>
      simp at ih
      simp
      have ih' := ih step.1
      cases h' : M.stepList step.1 tail
      <;> simp[h'] at ih'
      simp
      simp
      exact ih'

/-- A successful `evalFrom` run decomposes into a `stepList` trace with matching output. -/
lemma stepList_of_eval (s: σ) (w: List α) :
  match M.evalFrom s w with
  | none => M.stepList s w = none
  | some lst =>
    ∃ lst', M.stepList s w = some lst' ∧
            (lst'.flatMap (fun (_, _, _, g) => g)) = lst.2 ∧
            match lst'.getLast? with
            | none => lst.1 = s
            | some val => lst.1 = val.2.2.1 := by
  induction w generalizing s
  case nil =>
    simp [evalFrom, stepList]
  case cons head tail ih =>
    simp [evalFrom, stepList]
    cases h: M.step s head
    simp
    case some step =>
      simp at ih
      simp
      have ih' := ih step.1
      cases h' : M.evalFrom step.1 tail
      <;> simp[h'] at ih'
      simp[ih']
      simp
      have ⟨lst', h_step, h_eq⟩ := ih'
      simp[h_step ]
      simp[h_eq]
      cases h : lst'.getLast?
      simp[h] at h_eq ⊢
      simp[List.getLast?_cons, h]
      exact h_eq.right
      simp[h, List.getLast?_cons] at h_eq ⊢
      exact h_eq.right

lemma eval_of_stepList (s: σ) (w: List α) :
  match M.stepList s w with
  | none => M.evalFrom s w = none
  | some lst =>
    M.evalFrom s w = some (
      match lst.getLast? with
      | some val => val.2.2.1
      | none => s, lst.flatMap (fun (_, _, _, g) => g)) := by
  cases h : M.stepList s w
  case none =>
    simp
    cases h_eval: M.evalFrom s w with
    | none => simp
    | some sp =>
      have := M.stepList_of_eval s w
      simp[h_eval] at this
      have ⟨lst, hlst⟩ := this
      rw[h] at hlst
      simp at hlst
  case some lst =>
    cases h_eval: M.evalFrom s w with
    | none =>
      simp
      have := M.stepList_of_eval s w
      simp[h_eval] at this
      rw[h] at this
      simp at this
    | some sp =>
      have := M.stepList_of_eval s w
      simp[h_eval] at this
      have ⟨lst, hlst⟩ := this
      rw[h] at hlst
      simp at hlst
      simp[hlst]
      cases hl : lst.getLast?
      <;> (simp[hl] at hlst ⊢
           simp[←hlst.right.right])

lemma eval_of_stepList_opaque (s: σ) (w: List α) :
  match M.stepList s w with
  | none => M.evalFrom s w = none
  | some lst =>
    ∃ q', M.evalFrom s w = some (q', lst.flatMap (fun (_, _, _, g) => g)) := by
  have := eval_of_stepList M s w
  cases h : M.stepList s w
  case none =>
    simp[h] at this
    exact this
  case some lst =>
    simp[h] at this ⊢
    exists (match lst.getLast? with
            | some val => val.2.2.1
            | none => s)

-- this definition is a bit awkward with the none optional optionals
lemma stepList_eval_take (s: σ) (w: List α) (j: Fin w.length) :
  match M.stepList s w with
  | none => true
  | some lst =>
    Option.map Prod.fst (M.evalFrom s (w.take j)) = lst[j]?.map (fun x => x.1):= by
  induction w generalizing s
  case nil =>
    simp at j ⊢
    exact Fin.elim0 j
  case cons head tail ih =>
    simp at j ⊢
    simp[stepList]
    cases h: M.step s head
    simp_all
    case some val =>
    cases htail : M.stepList val.1 tail
    simp_all
    rename_i tail_prod
    simp_all
    by_cases hj0 : j = 0
    .
      simp_all; exact ⟨head, val.1, val.2, rfl⟩
    . let j' := j.pred hj0
      have : j = j'.succ := (Fin.pred_eq_iff_eq_succ hj0).mp rfl
      simp[this, evalFrom, h]
      have ih := ih val.1 j'
      simp[htail] at ih
      have : tail_prod.length = tail.length := by
        have := M.stepList_len val.1 tail
        simp[htail] at this
        exact this
      let j'' : Fin tail_prod.length := Fin.mk j' (by simp[j'.2, this])
      have : j''.toNat = j' := by simp[j'']
      simp[←this] at ih
      simp[←this]
      rcases ih with ⟨T, hT⟩
      rw [hT]
      rename_i h0
      have hrhs :
          Option.map (fun x => x.1) ((s, head, val) :: tail_prod)[j'.succ]? = some (tail_prod[j''].1) := by
        simp [j'', h0]
      exact hrhs.symm

lemma stepList_prefix_nil (s: σ) (p: List α) (a: List α) (h: p <+: a) :
  match M.stepList s p with
  | none => M.stepList s a = none
  | some _ => True := by
  induction a generalizing p s
  case nil =>
    simp at h
    simp[h]
    split <;> simp_all
  case cons head tail ih =>
    cases p
    case nil => simp_all[stepList]
    case cons head' tail' =>
      simp at h
      simp[h]
      simp[stepList]
      cases hh : M.step s head
      <;> simp_all
      split
      <;> try simp_all
      rename_i step _ heq
      split at heq
      <;> try simp at heq
      rename_i heq'
      have ih' := ih step.1 tail' h.right
      simp[heq'] at ih'
      simp[ih']

lemma stepList_prefix_w ( s: σ) (a: List α) :
  match M.stepList s a with
  | none => True
  | some lst => ∀ p, p <+: a → M.stepList s p = some (lst.take p.length) := by
  induction a generalizing s
  case nil =>
    simp [stepList]
  case cons head tail ih =>
    simp [stepList]
    cases h: M.step s head
    simp
    case some step =>
      simp at ih
      simp
      have ih' := ih step.1
      cases h' : M.stepList step.1 tail
      <;> simp[h'] at ih'
      simp
      simp
      intro pfx hpfx
      cases pfx with
      | nil => simp [stepList]
      | cons head' tail' =>
        simp at hpfx
        simp[stepList, h, hpfx]
        have ih' := ih step.1
        cases htail : M.stepList step.1 tail'
        <;> simp
        have := stepList_prefix_nil M step.1 tail' tail hpfx.right
        simp[htail] at this
        rw[this] at h'
        contradiction
        simp[h'] at ih'
        have ih' := ih' tail' hpfx.right
        rw[htail] at ih'
        simp at ih'
        exact ih'

lemma stepList_zip (s: σ) (a: List α) :
  match M.stepList s a with
  | none => True
  | some lst => ∀ trans ∈ lst, M.step trans.fst trans.snd.fst = some trans.snd.snd := by
  induction a generalizing s
  case nil =>
    simp [stepList]
  case cons head tail ih =>
    simp [stepList]
    cases h: M.step s head
    simp
    case some step =>
      simp at ih
      simp
      have ih' := ih step.1
      cases h' : M.stepList step.1 tail
      <;> simp[h'] at ih'
      simp
      simp
      intro src char dst tok ha
      cases ha
      <;> rename_i hl
      simp[h, hl]
      exact ih' src char dst tok hl

/-! ### FST: language and acceptance -/

/-- The language accepted when the transducer starts in state `s`, ignoring the
actual output word. -/
def acceptsFrom (s : σ) : Language α :=
  { w | ∃ f ∈ M.evalFrom s w, f.1 ∈ M.accept }

/-- The accepted input language of the transducer. -/
def accepts : Language α := M.acceptsFrom M.start

/-- `M.transducesTo w v` means that `M` reads `w`, emits `v`, and finishes in an
accepting state. This is the machine-level transduction relation used by later
semantic constructions. -/
def transducesTo (w : List α) (v : List Γ) : Prop :=
  if h : ((M.eval w).isSome) then
    ((M.eval w).get h).2 = v ∧ ((M.eval w).get h).1 ∈ M.accept
  else
    False

/-- The set of output sequences realizable from a given starting state. -/
def realizableSequences (q: σ) : Language Γ :=
  { v | ∃ q' w, M.evalFrom q w = some (q', v) }

-- a sequence is mod realizable if theres a realizable sequence
-- that "mods" to it. Here, mod means deleting all instances of a character
-- unless it starts with that character (usually whitespace)
-- this is a rather unnatural definition, but is crucial to the proof
/-- Realizable sequences modulo deletion of a distinguished symbol away from the
head position.

This is a whitespace-oriented normalization used later in the lexing proofs.
-/
def tailModdedRealizableSequences [BEq Γ] (q: σ) (mod: Γ) : Language Γ :=
  { v | ∃ v' ∈ M.realizableSequences q, ¬[mod] <+: v' ∧ v'.filter (fun x => x != mod) = v }

/-- Realizable sequences modulo deletion of all copies of a distinguished
symbol. -/
def moddedRealizableSequences [BEq Γ] (q: σ) (mod: Γ) : Language Γ :=
  { v | ∃ v' ∈ M.realizableSequences q, v'.filter (fun x => x != mod) = v }

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
    rwa [Option.get_of_mem h hf₁]
  ·
    intro ha
    exact ⟨_, by simp [eval], ha⟩

/-- Reconstruct a step function from an explicit transition table. -/
def mkStep [DecidableEq α] [DecidableEq σ] (transitions : List (σ × α × Option (σ × List Γ))) : σ → α → Option (σ × List Γ) :=
  fun s a =>
    transitions.find? (fun (s', a', _) => s = s' ∧ a = a')
    |>.map (fun (_, _, ts) => ts)
    |>.getD (none)

/-- The set of states reachable from `q` by one input symbol, forgetting
outputs. -/
def adj (q : σ) [FinEnum α] [FinEnum σ] : Finset σ :=
    { p | ∃ a, (∃ s ∈ M.step q a, s.1 = p)}


universe u_1 u_2


/-! ### FST: composition -/

/-- Execute one input symbol of `M₁` and immediately feed the emitted output
through `M₂`.

This is the local step relation underlying transducer composition.
-/
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

/-- A direct semantic evaluator for the composition of `M₁` and `M₂`. -/
def compose_fun_evalFrom { β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (s₁ : σ) (s₂ : τ) (w : List α) : Option ((σ × τ) × List β) :=
  match M₁.evalFrom s₁ w with
  | none => none
  | some (s₁', S) =>
    match (M₂.evalFrom s₂ S) with
    | none => none
    | some (s₂', T) => ((s₁', s₂'), T)

/-- One step of the semantic composition equals: compose the first step, then recurse. -/
lemma compose_fun_step_cons { β : Type u_1 } { τ : Type u_2 }
  (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (s₁ : σ) (s₂ : τ) (w : α) (ws : List α) :
    compose_fun_evalFrom M₁ M₂ s₁ s₂ (w :: ws) =
      match compose_fun_step M₁ M₂ s₁ s₂ w with
      | none => none
      | some ((s₁', s₂'), T) =>
        (compose_fun_evalFrom M₁ M₂ s₁' s₂' ws).map (fun ((s₁'', s₂''), T') => ((s₁'', s₂''), T ++ T'))
  := by
  cases h₁ : M₁.step s₁ w with
  | none =>
      simp [compose_fun_evalFrom, compose_fun_step, evalFrom, h₁]
  | some sp =>
      cases h₂ : M₁.evalFrom sp.1 ws with
      | none =>
          cases h₃ : M₂.evalFrom s₂ sp.2 <;>
            simp [compose_fun_evalFrom, compose_fun_step, evalFrom, h₁, h₂, h₃]
      | some sp' =>
          cases h₃ : M₂.evalFrom s₂ sp.2 with
          | none =>
              simp [compose_fun_evalFrom, compose_fun_step, evalFrom, h₁, h₂, h₃, M₂.evalFrom_append]
          | some sp2 =>
              simp [compose_fun_evalFrom, compose_fun_step, evalFrom, h₁, h₂, h₃, M₂.evalFrom_append]
              cases h₄ : M₂.evalFrom sp2.1 sp'.2 <;> rfl

def compose_fun_eval {β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (w : List α) : Option ((σ × τ) × List β) :=
  (compose_fun_evalFrom M₁ M₂ M₁.start M₂.start w)

/-- The operational composition `M₁.compose M₂` agrees with the direct
semantic formulation `compose_fun_evalFrom`. -/
def compose_correct { β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (w : List α) (q1 : σ) (q2 : τ) :
  ((M₁.compose M₂).evalFrom (q1, q2) w) = compose_fun_evalFrom M₁ M₂ q1 q2 w := by
  simp[compose_fun_evalFrom]
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
  exact lem



variable {β τ}
  (M₁ : FST α Γ σ) (M₂ : FST Γ β τ)

@[simp]
lemma compose_fun_evalFrom_nil (s₁ : σ) (s₂ : τ) : compose_fun_evalFrom M₁ M₂ s₁ s₂ [] = some ((s₁, s₂), []) :=
  rfl


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




/-! ### FST to FSA projection -/

/-- Project an FST to its underlying FSA by forgetting outputs. -/
def toFSA : FSA α σ where
  start := M.start
  step s a := (M.step s a).map Prod.fst
  accept := M.accept

@[simp] lemma toFSA_start : M.toFSA.start = M.start := rfl
@[simp] lemma toFSA_accept : M.toFSA.accept = M.accept := rfl

@[simp]
lemma toFSA_step (s : σ) (a : α) :
    M.toFSA.step s a = (M.step s a).map Prod.fst := rfl

@[simp]
lemma toFSA_evalFrom (s : σ) (w : List α) :
    M.toFSA.evalFrom s w = (M.evalFrom s w).map Prod.fst := by
  induction w generalizing s with
  | nil => simp [FSA.evalFrom, evalFrom]
  | cons x xs ih =>
    simp only [FSA.evalFrom, evalFrom, toFSA_step]
    cases M.step s x with
    | none => simp
    | some p =>
      dsimp only [Option.map]
      rw [ih]
      cases M.evalFrom p.1 xs <;> rfl

lemma toFSA_eval (w : List α) :
    M.toFSA.eval w = (M.eval w).map Prod.fst :=
  toFSA_evalFrom M M.start w

theorem toFSA_accepts : M.toFSA.accepts = M.accepts := by
  ext x
  simp only [FSA.accepts, FSA.acceptsFrom, accepts, acceptsFrom,
    toFSA_evalFrom, toFSA_start, toFSA_accept]
  constructor
  · rintro ⟨f, hf, hmem⟩
    rw [Option.map_eq_some_iff] at hf
    obtain ⟨⟨f', out⟩, heval, rfl⟩ := hf
    exact ⟨(f', out), heval, hmem⟩
  · rintro ⟨⟨f, out⟩, hf, hmem⟩
    refine ⟨f, ?_, hmem⟩
    rw [Option.map_eq_some_iff]
    exact ⟨(f, out), hf, rfl⟩

end FST

instance [DecidableEq σ] : Coe (FSA α σ) (NFA α σ) := ⟨fun fsa => fsa.toNFA⟩

instance [DecidableEq σ] : Coe (FSA α σ) (DFA α (Option σ)) := ⟨fun fsa => fsa.toDFA⟩
