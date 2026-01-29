import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.Language
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

import ConstrainedDecodingFormalization.RegularExpressionsToEpsilonNFA
import ConstrainedDecodingFormalization.Automata

open List RegularExpression

universe u v w

abbrev RE := RegularExpression

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ] [DecidableEq Γ]
  [BEq α] [BEq σ] [LawfulBEq σ] [LawfulBEq α]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype σ] [Fintype Γ]

/-- Extend character alphabet with EOS symbol-/
inductive ExtChar (α : Type u)
| char : α → ExtChar α
| eos  : ExtChar α
deriving DecidableEq, Repr

instance {α} : Coe (α) (ExtChar α) := ⟨fun a => ExtChar.char a⟩
instance [e: FinEnum α] : FinEnum (ExtChar α) where
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
          simp [h]
      }
  decEq := by infer_instance

abbrev Ch := ExtChar

variable (P : RE (Ch α))

@[ext]
structure Terminal (α : Type u) (Γ : Type v)  where
  expr : RegularExpression α
  symbol : Γ
deriving Repr

def LexingFSA := P.toεNFA.toNFA

@[ext]
structure Token (α : Type u) (Γ : Type v) where
  symbol : Γ
  string : List α
deriving Repr, DecidableEq

structure LexerSpec (α Γ σ) where
  automaton : FSA α σ
  term: σ → Option Γ
  hterm: ∀ s, s ∈ automaton.accept ↔ (term s).isSome
  term_inj: ∀ s₁ s₂ t, term s₁ = some t ∧ term s₂ = some t → s₁ = s₂

def LexerSpec.seq_term (spec: LexerSpec α Γ σ) (seq: List α) : Option Γ :=
  match spec.automaton.eval seq with
  | some s => spec.term s
  | none => none

def Lexer (α : Type u) (Γ : Type v) := List (Ch α) -> Option (List (Ch Γ) × List α)

inductive PartialLexRel (spec: LexerSpec α Γ σ)
  : List (Ch α) → List (Ch Γ) → List α → Prop
  -- base case
| nil :
    PartialLexRel spec
      [] [] []
  -- case 1
| step_eos {w wn tokens unlexed} :
    PartialLexRel spec w tokens unlexed →
    -- this nonsense needs to be done to satisfy the eliminator for some reason
    -- related? https://github.com/leanprover/lean4/issues/9803
    wn = w ++ [ExtChar.eos] →
    unlexed ∈ spec.automaton.accepts →
      PartialLexRel spec wn (tokens ++ [.eos]) []
  -- case 2
| step_char_continue {w wn tokens unlexed ch} :
    PartialLexRel spec w tokens unlexed →
    wn = w ++ [ExtChar.char ch] →
    unlexed ++ [ch] ∈ spec.automaton.prefixLanguage →
      PartialLexRel spec wn tokens (unlexed ++ [ch])
  -- case 3
| step_char_commit {w wn tokens unlexed ch t} :
    PartialLexRel spec w tokens unlexed →
    wn = w ++ [ExtChar.char ch] →
    -- next is not in prefix language, but current is in accept
    unlexed ++ [ch] ∉ spec.automaton.prefixLanguage →
    some t = spec.seq_term unlexed →
      PartialLexRel spec wn (tokens ++ [ExtChar.char t]) [ch]

private def PartialLex_trans (spec: LexerSpec α Γ σ) (prev: Option (List (Ch Γ) × List α))
   (c : Ch α) : Option (List (Ch Γ) × List α) :=
  match prev with
  | none => none
  | some (tokens, unlexed) =>
    match c with
    | ExtChar.eos =>
      if unlexed ∈ spec.automaton.accepts then
        some (tokens ++ [.eos], [])
      else
        none
    | ExtChar.char ch =>
      let new_unlexed := unlexed ++ [ch]
      match spec.automaton.eval new_unlexed with
      | some σ' => some (tokens, new_unlexed)
      | none =>
        let dst := spec.automaton.eval unlexed
        match dst with
        | none => none
        | some σ =>
          if h : σ ∈ spec.automaton.accept then
            let term := spec.term σ
            have h2 := (spec.hterm σ).mp h
            match hc : term with
            | some t => some (tokens ++ [ExtChar.char t], [ch])
            | none => by
              simp[term] at hc
              simp_all
          else
            none

private def PartialLex_seed (spec: LexerSpec α Γ σ) (seed: Option (List (Ch Γ) × List α)) : Lexer α Γ :=
  fun w => List.foldl (PartialLex_trans spec) seed w

def PartialLex (spec: LexerSpec α Γ σ) : Lexer α Γ :=
  PartialLex_seed spec (some ([], []))

lemma PartialLex_pruned_eq_PartialLexRel_seed (spec: LexerSpec α Γ σ) (hp: spec.automaton.pruned) :
    (∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) → PartialLex_seed spec (some ([], [])) w = some (tokens, unlexed)) ∧
    (∀ wp ws seed_f seed_s tokens unlexed, (PartialLexRel spec wp seed_f seed_s) ∧ PartialLex_seed spec (some (seed_f, seed_s)) ws = some (tokens, unlexed) → PartialLexRel spec (wp ++ ws) tokens unlexed)
      := by
  have hprune := spec.automaton.pruned_prefixLanguage hp
  have left : (∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) → PartialLex_seed spec (some ([], [])) w = some (tokens, unlexed)) := by
    intro w tokens unlexed h
    induction h
    case nil =>
      simp[PartialLex, PartialLex_seed, PartialLex_trans]
    case step_eos w wn tokens unlexed ih wwn h hacc =>
      simp[PartialLex, PartialLex_seed, PartialLex_trans] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      exact h
    case step_char_continue w wn tokens unlexed ch ih wwn h hacc =>
      simp[PartialLex, PartialLex_seed, PartialLex_trans] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      cases he: spec.automaton.eval (unlexed ++ [ch]) with
      | none =>
        have : unlexed ++ [ch] ∉ spec.automaton.prefixLanguage := by
          exact Eq.mpr_not (congrFun (id (Eq.symm hprune)) (unlexed ++ [ch])) fun a => a he
        contradiction
      | some σ' =>
        simp at he
        simp[he]
    case step_char_commit w wn tokens unlexed ch t ih wwn hni ht hacc =>
      simp[PartialLex, PartialLex_seed, PartialLex_trans] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      cases he: spec.automaton.eval (unlexed ++ [ch]) with
      | none =>
        simp[FSA.eval] at he
        simp[he]
        simp[LexerSpec.seq_term] at ht
        split at ht
        case h_1 st heq =>
          simp[heq]
          have : st ∈ spec.automaton.accept := by
            apply (spec.hterm st).mpr
            simp[←ht]
          exists this
          split
          <;> simp_all
        case h_2 heq =>
          simp[heq] at ht
      | some σ' =>
        have : spec.automaton.evalFrom spec.automaton.start (unlexed ++ [ch]) = none := by
          simp[←hprune] at hni
          simp[FSA.intermediateLanguage] at hni
          have : ¬¬ spec.automaton.evalFrom spec.automaton.start (unlexed ++ [ch]) = none := by
            exact hni
          exact not_not.mp this
        simp[this] at he

  constructor
  . exact left
  . intro wp ws seed_f seed_s tokens unlexed
    intro h
    induction ws generalizing wp seed_f seed_s
    case nil =>
      simp[PartialLex_seed] at h
      cases h.left
      <;> simp_all
      case step_eos =>
        have ⟨hl, htokens, _⟩ := h
        simp[←htokens]
        exact hl
      case step_char_continue =>
        have ⟨hl, htokens, hunlexed⟩ := h
        simp[←htokens, ←hunlexed]
        exact hl
      case step_char_commit =>
        have ⟨hl, htokens, hunlexed⟩ := h
        simp[←htokens, ←hunlexed]
        exact hl
    case cons ch tail ih =>
      have my_inductive_seed:= h.left
      have computable_eq_some := left wp seed_f seed_s my_inductive_seed
      have h_token_unlexed := h.right

      simp[PartialLex_seed] at h_token_unlexed
      cases hns : (PartialLex_trans spec (some (seed_f, seed_s)) ch) with
      | none =>
        rw[hns] at h_token_unlexed
        have : foldl (PartialLex_trans spec) none tail = none := by
          apply List.foldl_fixed'
          simp[PartialLex_trans]
        rw[this] at h_token_unlexed
        contradiction
      | some qp =>
        rw[hns] at h_token_unlexed
        let ⟨step_tokens, step_unlexed⟩ := qp

        match ch with
        | ExtChar.eos =>
          simp[PartialLex_trans] at hns

          have haccept : seed_s ∈ spec.automaton.accepts := by exact hns.left
          let new_tokens := seed_f ++ [.eos]
          have step := PartialLexRel.step_eos my_inductive_seed rfl haccept
          have ihr := ih (wp ++ [ExtChar.eos]) new_tokens []
          have ihr := by
            apply ihr
            constructor
            exact step
            simp[PartialLex_seed]
            simp[←hns.right.left, ←hns.right.right, new_tokens] at h_token_unlexed ⊢
            exact h_token_unlexed
          suffices wp ++ ExtChar.eos :: tail = (wp ++ [ExtChar.eos]) ++ tail by
            rw[this]
            exact ihr
          exact append_cons wp ExtChar.eos tail
        | ExtChar.char ch =>
          simp[PartialLex_trans] at hns
          cases hp : spec.automaton.evalFrom spec.automaton.start (seed_s ++ [ch]) with
          | some σ' =>
            simp[hp] at hns
            let new_tokens := seed_f
            let new_unlexed := seed_s ++ [ch]

            have hint : (seed_s ++ [ch] ∈ spec.automaton.intermediateLanguage) := by
              simp [FSA.intermediateLanguage]
              rw[Set.mem_setOf]
              simp [hp]
            have hpfx : (seed_s ++ [ch] ∈ spec.automaton.prefixLanguage) := by
              rw[←hprune]
              exact hint
            have ihr := ih (wp ++ [ExtChar.char ch]) new_tokens new_unlexed
            have ihr := by
              apply ihr
              constructor
              exact PartialLexRel.step_char_continue my_inductive_seed rfl hpfx
              simp[PartialLex_seed]
              simp[new_tokens, new_unlexed, hns]
              exact h_token_unlexed
            suffices wp ++ ExtChar.char ch :: tail = (wp ++ [ExtChar.char ch]) ++ tail by
              rw[this]
              exact ihr
            exact append_cons wp (ExtChar.char ch) tail
          | none =>
            cases ha : spec.automaton.evalFrom spec.automaton.start seed_s with
            | none => simp[hp, ha] at hns
            | some σ =>
              simp[hp, ha] at hns

              have hint : (seed_s ++ [ch] ∉ spec.automaton.intermediateLanguage) := by
                simp [FSA.intermediateLanguage]
                rw[Set.mem_setOf]
                simp [hp]
              have hpfx : (seed_s ++ [ch] ∉ spec.automaton.prefixLanguage) := by
                rw[←hprune]
                exact hint

              have haccept : (seed_s ∈ spec.automaton.accepts) := by
                have ⟨t, ht⟩ := hns
                simp[FSA.accepts, FSA.acceptsFrom]
                rw[Set.mem_setOf]
                exists σ

              -- quite round about away but works
              let term := spec.term σ
              have ⟨t, ht⟩ : ∃ t, term = some t := by
                have ⟨ha, ht⟩ := hns
                have h2 := (spec.hterm σ).mp ha
                match hc: term with
                | none =>
                  simp[term] at hc
                  simp[hc] at h2
                | some t => exists t

              let new_tokens := seed_f ++ [ExtChar.char t]
              let new_unlexed := [ch]

              have ihr := ih (wp ++ [ExtChar.char ch]) new_tokens new_unlexed
              have ihr := by
                apply ihr
                constructor
                apply PartialLexRel.step_char_commit my_inductive_seed
                simp[PartialLex_seed]
                exact hpfx
                simp[term] at ht
                simp[LexerSpec.seq_term]
                simp[ha, ht]
                simp[PartialLex_seed, new_tokens, new_unlexed, hns]
                have ⟨ha, ht'⟩ := hns
                split at ht'
                case h_1 heq =>
                  have := h_token_unlexed
                  simp_all
                  simp[←ht'.left, ←ht'.right] at this ⊢
                  simp[heq, ht, term] at ht
                  rw[←ht]
                  exact this
                case h_2 heq =>
                  simp[heq, ht, term] at ht
              suffices wp ++ ExtChar.char ch :: tail = (wp ++ [ExtChar.char ch]) ++ tail by
                rw[this]
                exact ihr
              exact append_cons wp (ExtChar.char ch) tail

theorem PartialLex_pruned_eq_PartialLexRel (spec: LexerSpec α Γ σ) (hp: spec.automaton.pruned) :
    ∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) ↔ PartialLex spec w = some (tokens, unlexed)
      := by
  intro w tokens unlexed
  apply Iff.intro
  . exact (PartialLex_pruned_eq_PartialLexRel_seed spec hp).left w tokens unlexed
  . intro h
    have : PartialLexRel spec ([] ++ w) tokens unlexed := by
      apply (PartialLex_pruned_eq_PartialLexRel_seed spec hp).right [] w
      constructor
      exact PartialLexRel.nil
      simp[PartialLex] at h
      exact h
    simp at this
    exact this


/-- Given a lexing automaton `A`, build a character-to-token lexing FST with output over `Γ`
    For the lexing FSA, we'll use the convention that each terminal symbol is attached to an accept state (see Fig. 1) -/
def BuildLexingFST (spec: LexerSpec α Γ σ) :
    FST (Ch α) (Ch Γ) σ := Id.run do
  let ⟨A, term, hterm, _⟩ := spec

  let q0 := A.start
  let F := A.accept

  let step := fun (q : σ) (c : Ch α) =>
    match c with
    | ExtChar.char c =>
      if h : (A.step q c).isSome then
        some ((A.step q c).get h, [])
      else if h : q ∈ F then
        let T := (term q).get <| ((hterm q).mp h)
        A.step q0 c |>.map (fun q' => (q', [ExtChar.char T]))
      else
        none
    | ExtChar.eos =>
      if h : q ∈ F then
        let T := (term q).get <| ((hterm q).mp h)
        some (q0, [T, .eos])
      else if q = q0 then
        some (q0, [.eos])
      else
        none

  ⟨q0, step, [q0]⟩

def LexingFST_trans_iff_PartialLex (spec: LexerSpec α Γ σ) (h: [] ∉ spec.automaton.accepts) :
  ∀ w ts,
      (∀ wr, PartialLex spec w = some (ts, wr) →
        (∃ q', ((BuildLexingFST spec).eval w = some (q', ts)) ∧
                (BuildLexingFST spec).eval wr = some (q', []))) ∧
      (∀ q', (BuildLexingFST spec).eval w = some (q', ts) → ∃ wr, PartialLex spec w = some (ts, wr))
            := by
  intro w ts
  -- evalFrom fold matches lex foldl more nicely induction wise
  suffices ∀ seed, (∀ wr, PartialLex_seed spec seed w = some (ts, wr) →
        (∃ q', ((BuildLexingFST spec).evalFrom_fold_seed w seed = some (q', ts)) ∧
                (BuildLexingFST spec).evalFrom_fold wr = some (q', []))) ∧
      (∀ q', (BuildLexingFST spec).eval_fold w = some (q', ts) → ∃ wr, PartialLex_seed spec seed w = some (ts, wr)) by
    simp[FST.eval_fold_eq_eval] at this
    exact this

  induction w generalizing ts
  case nil =>
    simp[FST.eval_fold, FST.evalFrom_fold, FST.evalFrom_fold_seed]
    apply And.intro
    . intro wr
      intro h
      simp[PartialLex] at h
      constructor
      exact h.left
      simp[h.right]
    . intro hl
      simp[PartialLex]
      exact hl
  case cons head tail ih =>
    constructor
    . intro wr
      intro h
      simp[PartialLex] at h
      rw[List.foldl.eq_def] at h

    . sorry
namespace Detokenizing

universe x
variable { V : Type x }
variable [BEq V]

def BuildDetokenizingFST (tokens: List (Token α V)) : FST V α Unit :=
  let step := fun _ s =>
    match tokens.find? λ t => t.symbol == s with
    | some t => (Unit.unit, t.string)
    | none => none

  FST.mk Unit.unit step [Unit.unit]

def detokenize (tokens: List (Token α V)) (w : List V) : Option (List α) :=
  match w with
  | [] => some []
  | w' :: ws =>
    match tokens.find? λ t => t.symbol == w' with
    | some t => do
      let res ← detokenize tokens ws
      t.string ++ res
    | none => none

theorem detokenizerFST_eq_detokenizer  ( tokens : List (Token α V)) :
  ∀ ( w : List V ), detokenize tokens w = ((BuildDetokenizingFST tokens).eval w).map Prod.snd := by
  intro w
  have lem : ∀ w, detokenize tokens w = ((BuildDetokenizingFST tokens).evalFrom Unit.unit w).map Prod.snd := by
    intro w
    induction w
    case nil =>
      simp[detokenize, BuildDetokenizingFST, FST.evalFrom]
    case cons head tail ih =>
      simp[FST.eval, FST.evalFrom, detokenize]
      split <;> simp_all
      case h_1 =>
        rename_i tt heq
        conv =>
          pattern (BuildDetokenizingFST tokens).step 0 head
          simp[BuildDetokenizingFST]
        simp[heq]
        split <;> simp_all
      case h_2 =>
        rename_i tt heq
        conv =>
          pattern (BuildDetokenizingFST tokens).step 0 head
          simp[BuildDetokenizingFST]
        have h : tokens.find? (λ t => t.symbol == head) = none := by
          apply List.find?_eq_none.mpr
          intro x hx
          rw [heq x hx]
          trivial
        rw[h]
        simp
  exact lem w

theorem detokenizer_comp { σ0 } ( tokens : List (Token α V)) (f : FST α Γ σ0) :
  ∀ w, ((FST.compose (BuildDetokenizingFST tokens) f).eval w).map Prod.snd =
    match detokenize tokens w with
    | some u => (f.eval u).map Prod.snd
    | none => none := by
  intro w
  have := FST.compose_correct (BuildDetokenizingFST tokens) f w
  rw[this]
  simp[FST.compose_fun_eval, FST.compose_fun_evalFrom]
  rw[detokenizerFST_eq_detokenizer]
  simp[FST.eval]
  cases h : (BuildDetokenizingFST tokens).evalFrom (BuildDetokenizingFST tokens).start w with
  | some u =>
    simp_all[h, Option.map, Prod.snd]
    cases f.evalFrom f.start u.2 <;> simp_all
  | none => simp_all

end Detokenizing
