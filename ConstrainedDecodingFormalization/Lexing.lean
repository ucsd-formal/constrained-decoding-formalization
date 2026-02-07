import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.Language
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Flatten
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Vocabulary

open List

universe u v w

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ]
  [BEq α] [BEq σ] [LawfulBEq σ]

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
          simp
      }
  decEq := by infer_instance

abbrev Ch := ExtChar

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

def LexerSpec.accept_seq_term (spec: LexerSpec α Γ σ) (seq: List α) (h: seq ∈ spec.automaton.accepts) : Γ :=
  let s := (spec.automaton.eval seq).get <| by
    simp[FSA.accepts, FSA.acceptsFrom] at h
    rw[Set.mem_setOf] at h
    have ⟨e, he⟩ := h
    simp[FSA.eval, he]
  have sa : s ∈ spec.automaton.accept := by
    simp[FSA.accepts, FSA.acceptsFrom] at h
    rw[Set.mem_setOf] at h
    have ⟨e, he⟩ := h
    simp[s, he]
  let term := spec.term s
  term.get ((spec.hterm s).mp sa)

def Lexer (α : Type u) (Γ : Type v) := List (Ch α) -> Option (List (Ch Γ) × List α)

inductive PartialLexRel (spec: LexerSpec α Γ σ)
  : List (Ch α) → List (Ch Γ) → List α → Prop
  -- base case
| nil :
    PartialLexRel spec
      [] [] []
-- case 0 (unmentioned in paper but implicitly done in the lexing transducer)
| step_nil_eos { w wn tokens }:
    PartialLexRel spec w tokens [] →
    wn = w ++ [ExtChar.eos] →
    [] ∉ spec.automaton.accepts →
    PartialLexRel spec wn (tokens ++ [.eos]) []
  -- case 1
| step_eos {w wn tokens unlexed} :
    PartialLexRel spec w tokens unlexed →
    -- this nonsense needs to be done to satisfy the eliminator for some reason
    -- related? https://github.com/leanprover/lean4/issues/9803
    wn = w ++ [ExtChar.eos] →
    (h : unlexed ∈ spec.automaton.accepts) →
      PartialLexRel spec wn (tokens ++ [.char (spec.accept_seq_term unlexed h), .eos]) []
  -- case 2
| step_char_continue {w wn tokens unlexed ch} :
    PartialLexRel spec w tokens unlexed →
    wn = w ++ [ExtChar.char ch] →
    unlexed ++ [ch] ∈ spec.automaton.prefixLanguage →
      PartialLexRel spec wn tokens (unlexed ++ [ch])
  -- case 3
| step_char_commit {w wn tokens unlexed ch} :
    PartialLexRel spec w tokens unlexed →
    wn = w ++ [ExtChar.char ch] →
    -- next is not in prefix language, but current is in accept, and ch is a prefix of something
    unlexed ++ [ch] ∉ spec.automaton.prefixLanguage →
    [ch] ∈ spec.automaton.prefixLanguage →
    (h : unlexed ∈ spec.automaton.accepts) →
      PartialLexRel spec wn (tokens ++ [ExtChar.char (spec.accept_seq_term unlexed h)]) [ch]

private def PartialLex_trans (spec: LexerSpec α Γ σ) (prev: Option (List (Ch Γ) × List α))
   (c : Ch α) : Option (List (Ch Γ) × List α) :=
  match prev with
  | none => none
  | some (tokens, unlexed) =>
    match c with
    | ExtChar.eos =>
      if h : unlexed ∈ spec.automaton.accepts then
        some (tokens ++ [.char (spec.accept_seq_term unlexed h), .eos], [])
      else if unlexed = [] then
        some (tokens ++ [.eos], [])
      else
        none
    | ExtChar.char ch =>
      let new_unlexed := unlexed ++ [ch]
      match spec.automaton.eval new_unlexed with
      | some _ => some (tokens, new_unlexed)
      | none =>
        let dst := spec.automaton.eval unlexed
        match dst with
        | none => none
        | some σ =>
          if h : σ ∈ spec.automaton.accept then
            let term := spec.term σ
            have h2 := (spec.hterm σ).mp h
            let t := term.get h2
            if (spec.automaton.eval [ch]).isSome then
              some (tokens ++ [ExtChar.char t], [ch])
            else
              none
          else
            none

@[simp]
private def PartialLex_trans_nil (spec: LexerSpec α Γ σ) (c : Ch α) :
  PartialLex_trans spec none c = none := by
  simp[PartialLex_trans]

@[simp]
private def PartialLex_trans_foldl_nil (spec: LexerSpec α Γ σ) (ws : List (Ch α)) :
  foldl (PartialLex_trans spec) none ws = none := by
  exact foldl_fixed' (congrFun rfl) ws

@[simp]
private def PartialLex_seed (spec: LexerSpec α Γ σ) (seed: Option (List (Ch Γ) × List α)) : Lexer α Γ :=
  fun w => List.foldl (PartialLex_trans spec) seed w

@[simp]
def PartialLex (spec: LexerSpec α Γ σ) : Lexer α Γ :=
  PartialLex_seed spec (some ([], []))


inductive LexingState (σ : Type w) where
| id : σ → LexingState σ
| start : LexingState σ
deriving DecidableEq, Repr

def LexingState.src {σ : Type w} (spec: LexerSpec α Γ σ) : LexingState σ → σ
| LexingState.id s => s
| LexingState.start => spec.automaton.start

@[simp]
def LexingState_src_id [DecidableEq α] [BEq α]{σ : Type w} (spec: LexerSpec α Γ σ) (s : σ) :
  LexingState.src spec (LexingState.id s) = s := by
  simp[LexingState.src]


/-- Given a lexing automaton `A`, build a character-to-token lexing FST with output over `Γ`
    For the lexing FSA, we'll use the convention that each terminal symbol is attached to an accept state (see Fig. 1) -/
def BuildLexingFST [BEq α] [DecidableEq α] (spec: LexerSpec α Γ σ) :
    FST (Ch α) (Ch Γ) (LexingState σ) := Id.run do
  let ⟨A, term, hterm, _⟩ := spec

  let new_q0 := LexingState.start
  let q0 := spec.automaton.start
  let F := A.accept

  let step := fun (q : LexingState σ) (c : Ch α) =>
    let qorg := LexingState.src spec q
    match c with
    | ExtChar.char c =>
      if h : (A.step qorg c).isSome then
        some (LexingState.id ((A.step qorg c).get h), [])
      else if h : qorg ∈ F then
        let T := (term qorg).get <| ((hterm qorg).mp h)
        A.step q0 c |>.map (fun q' => (LexingState.id q', [ExtChar.char T]))
      else
        none
    | ExtChar.eos =>
      if h : qorg ∈ F then
        let T := (term qorg).get <| (hterm qorg).mp h
        some (new_q0, [T, .eos])
      else if q = new_q0 then
        some (new_q0, [.eos])
      else
        none

  ⟨new_q0, step, [new_q0]⟩

@[simp]
def LexingFST_start (spec: LexerSpec α Γ σ) : (BuildLexingFST spec).start = LexingState.start := by
  simp[BuildLexingFST, Id.run]

omit [DecidableEq α] [DecidableEq σ] [BEq α] in
lemma PartialLex_pruned_eq_PartialLexRel_seed (spec: LexerSpec α Γ σ) (hp: spec.automaton.pruned) :
    (∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) → PartialLex_seed spec (some ([], [])) w = some (tokens, unlexed)) ∧
    (∀ wp ws seed_f seed_s tokens unlexed, (PartialLexRel spec wp seed_f seed_s) ∧ PartialLex_seed spec (some (seed_f, seed_s)) ws = some (tokens, unlexed) → PartialLexRel spec (wp ++ ws) tokens unlexed)
      := by
  have hprune := spec.automaton.pruned_prefixLanguage hp
  have left : (∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) → PartialLex_seed spec (some ([], [])) w = some (tokens, unlexed)) := by
    intro w tokens unlexed h
    induction h
    case nil =>
      simp[PartialLex_seed]
    case step_nil_eos w wn tokens ih wwn h hacc =>
      simp[PartialLex_seed] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      exact h
    case step_eos w wn tokens unlexed ih wwn h hacc =>
      simp[PartialLex_seed] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      simp[h]
    case step_char_continue w wn tokens unlexed ch ih wwn h hacc =>
      simp[PartialLex_seed] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      cases he: spec.automaton.eval (unlexed ++ [ch]) with
      | none =>
        have : unlexed ++ [ch] ∉ spec.automaton.prefixLanguage := by
          exact Eq.mpr_not (congrFun (id (Eq.symm hprune)) (unlexed ++ [ch])) fun a => a he
        contradiction
      | some σ' =>
        simp at he
        simp[he]
    case step_char_commit w wn tokens unlexed ch ih wwn hni hc_pfx ht hacc =>
      simp[PartialLex_seed] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      cases he: spec.automaton.eval (unlexed ++ [ch]) with
      | none =>
        simp[FSA.eval] at he
        simp[he]
        simp[FSA.accepts, FSA.acceptsFrom] at ht
        split
        <;> simp_all
        rw[Set.mem_setOf] at ht
        have ⟨e, he'⟩ := ht
        rename_i σ' _ heq
        simp[he'] at heq
        constructor
        rw[←hprune] at hc_pfx
        simp[FSA.intermediateLanguage] at hc_pfx
        rw[Set.mem_setOf] at hc_pfx ht
        cases hch : spec.automaton.evalFrom spec.automaton.start [ch]
        <;> simp_all
        rename_i heq'
        rw[Set.mem_setOf] at ht
        simp[heq'] at ht
        exists ht
        rename_i ht' _ _
        simp[heq', LexerSpec.accept_seq_term]
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
  . intro wp ws seed_f seed_s tokens unlexed h
    induction ws generalizing wp seed_f seed_s
    case nil =>
      simp[PartialLex_seed] at h
      cases h.left
      <;> simp_all
      case step_nil_eos =>
        have ⟨hl, htokens, _⟩ := h
        simp[←htokens]
        exact hl
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
      have my_inductive_seed := h.left
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
          by_cases haccept : seed_s ∈ spec.automaton.accepts
          . let new_tokens := seed_f ++ [.char (spec.accept_seq_term seed_s haccept), .eos]
            have step := PartialLexRel.step_eos my_inductive_seed rfl haccept
            have ihr := ih (wp ++ [ExtChar.eos]) new_tokens []
            have ihr := by
              apply ihr
              constructor
              exact step
              simp[PartialLex_seed]
              simp[haccept] at hns
              have := h_token_unlexed
              simp[←hns.left, ←hns.right, new_tokens] at h_token_unlexed ⊢
              exact h_token_unlexed
            suffices wp ++ ExtChar.eos :: tail = (wp ++ [ExtChar.eos]) ++ tail by
              rw[this]
              exact ihr
            exact append_cons wp ExtChar.eos tail
          . simp[haccept] at hns
            let new_tokens := seed_f ++ [.eos]
            simp[hns.left] at my_inductive_seed
            simp[hns] at haccept
            have step := PartialLexRel.step_nil_eos my_inductive_seed rfl haccept
            have ihr := ih (wp ++ [ExtChar.eos]) new_tokens []
            have ihr := by
              apply ihr
              constructor
              exact step
              simp[PartialLex_seed]
              have := h_token_unlexed
              simp[←hns.right, new_tokens] at h_token_unlexed ⊢
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
              simp_all
              cases hbo : spec.automaton.eval [ch]
              . simp at hbo
                simp[hbo] at hns
              . have hint : (seed_s ++ [ch] ∉ spec.automaton.intermediateLanguage) := by
                  simp [FSA.intermediateLanguage]
                  rw[Set.mem_setOf]
                  simp[←hns.right.right] at hp
                  simp [hp]
                have hpfx : (seed_s ++ [ch] ∉ spec.automaton.prefixLanguage) := by
                  rw[←hprune]
                  exact hint

                have haccept : (seed_s ∈ spec.automaton.accepts) := by
                  have ⟨⟨h, _⟩, ht⟩ := hns.right
                  simp[FSA.accepts, FSA.acceptsFrom]
                  rw[Set.mem_setOf]
                  exists σ

                -- very round about away but works
                let term := spec.term σ
                have ⟨t, ht⟩ : ∃ t, term = some t := by
                  have ⟨⟨h, _⟩, ht⟩ := hns.right
                  have h2 := (spec.hterm σ).mp h
                  match hc: term with
                  | none =>
                    simp[term] at hc
                    simp[hc] at h2
                  | some t => exists t

                let tused := spec.accept_seq_term seed_s haccept
                have htused : t = tused := by
                  simp[term] at ht
                  simp[tused, LexerSpec.accept_seq_term]
                  conv =>
                    rhs
                    pattern spec.automaton.evalFrom spec.automaton.start seed_s
                    rw[ha]
                  simp[ht]
                let new_tokens := seed_f ++ [ExtChar.char tused]
                let new_unlexed := [ch]

                have ihr := ih (wp ++ [ExtChar.char ch]) new_tokens new_unlexed
                have ihr : PartialLexRel spec (wp ++ [ExtChar.char ch] ++ tail) tokens unlexed := by
                  have ⟨⟨_, hseed⟩, ht'⟩ := hns.right
                  apply ihr
                  apply PartialLexRel.step_char_commit h.left
                  simp
                  exact hpfx
                  simp[hns]
                  simp_all
                  simp[term] at ht
                  simp[ht] at hseed
                  rw[←hprune]
                  simp[FSA.intermediateLanguage]
                  rw[Set.mem_setOf]
                  rw[hbo]
                  simp
                  simp[new_tokens, new_unlexed, ←ht', ←hseed, ←htused, ht, term] at h_token_unlexed ⊢
                  exact h_token_unlexed
                suffices wp ++ ExtChar.char ch :: tail = (wp ++ [ExtChar.char ch]) ++ tail by
                  rw[this]
                  exact ihr
                exact append_cons wp (ExtChar.char ch) tail

omit [DecidableEq α] [DecidableEq σ] [BEq α] in
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

-- automata parsing iff LexingFst parses and does not produce tokens
private def FSA_ch_to_LexingFST (spec: LexerSpec α Γ σ) :
  ∀ (w : List α) q q', (q ≠ LexingState.start ∨ w ≠ []) →
    (spec.automaton.evalFrom (q.src spec) w = some q' ↔
    (BuildLexingFST spec).evalFrom q w = some (LexingState.id q', []))
    := by
  intro w q q' h
  induction w generalizing q q'
  case nil =>
    simp[LexingState.src]
    simp at h
    split
    case h_1 x s => simp
    case h_2 s => simp at h
  case cons hd tl ih =>
    simp[FSA.evalFrom]
    simp at h
    cases hstep : spec.automaton.step (LexingState.src spec q) hd
    . simp[FST.evalFrom]
      nth_rewrite 1 [BuildLexingFST, Id.run]
      simp[hstep]
      by_cases haccept: LexingState.src spec q ∈ spec.automaton.accept
      simp_all
      split <;> simp_all
      split <;> simp_all
      intro _ h
      rename_i heq _ _ _ _ _
      have ⟨e, hw⟩ := heq
      simp[←hw.right] at h
      simp[haccept]
    . rename_i astep
      have : (spec.automaton.step (LexingState.src spec q) hd).isSome := by
        simp[hstep]
      simp[FST.evalFrom]
      conv =>
        pattern (BuildLexingFST spec).step q
        unfold BuildLexingFST
      simp[Id.run, this]
      simp[hstep]
      have ih := ih (LexingState.id astep) q' (by simp)
      simp[LexingState.src] at ih
      convert ih
      split <;> simp_all

private def PartialLex_to_LexingFST_evalFold (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) :
  ∀ wp ws q' seed_ts seed_wr,
       PartialLex spec wp = some (seed_ts, seed_wr) →
      (BuildLexingFST spec).eval wp = some (q', seed_ts) →
      (BuildLexingFST spec).eval seed_wr = some (q', []) →
      (seed_wr = [] ↔ q' = LexingState.start) →
      match PartialLex_seed spec (some (seed_ts, seed_wr)) ws with
      | some (ts, wr) =>
        (∃ q'', ((BuildLexingFST spec).evalFrom_fold_seed q' ws seed_ts = some (q'', ts)) ∧
                 (BuildLexingFST spec).evalFrom_fold_seed (BuildLexingFST spec).start wr [] = some (q'', []))
      | none => (BuildLexingFST spec).evalFrom_fold_seed q' ws seed_ts = none := by
  intro wp ws q' seed_ts seed_wr
  let fst := BuildLexingFST spec
  let new_q0 := fst.start
  let old_q0 := spec.automaton.start

  have h_q0_na : old_q0 ∉ spec.automaton.accept := by
    by_contra h'
    simp[FSA.accepts_iff] at he
    have : spec.automaton.evalFrom old_q0 [] = some old_q0 := by
      simp[FSA.evalFrom_nil]
    have w : ∃ f, spec.automaton.evalFrom spec.automaton.start [] = some f ∧ f ∈ spec.automaton.accept := by
      exists old_q0
    simp at w
    exact he w

  induction ws generalizing wp q' seed_ts seed_wr
  <;> (
    intro h₀ h₁ h₂ h₃
    have h₂_fsa : spec.automaton.evalFrom spec.automaton.start seed_wr = some (LexingState.src spec q') := by
      by_cases hempty : seed_wr = []
      . simp[hempty]
        have := h₃.mp hempty
        simp[LexingState.src, this]
      . have : q' ≠ LexingState.start := by
          exact (Iff.ne h₃).mp hempty
        have hbase := (FSA_ch_to_LexingFST spec (seed_wr) LexingState.start (q'.src spec) (Or.inr hempty)).mpr (by
          convert h₂
          cases q' <;> simp_all
        )
        simp[LexingState.src] at hbase ⊢
        cases q' <;> simp_all

    simp[FST.evalFrom_fold_seed]
    rw[←FST.eval_fold_eq_eval] at h₂
    simp[FST.eval_fold, FST.evalFrom_fold] at h₂
  )
  case nil =>
    exact h₂
  case cons head tail ih =>
    let pl_step := (PartialLex_trans spec (some (seed_ts, seed_wr)) head)
    cases hh : head
    case eos =>
      simp[PartialLex_trans]
      let afinal := spec.automaton.eval seed_wr
      by_cases haccept : seed_wr ∈ spec.automaton.accepts
      . simp[haccept]
        have ⟨aq', haq'⟩ := spec.automaton.accepts_iff.mp haccept
        have : spec.automaton.evalFrom (LexingState.src spec LexingState.start) seed_wr = some aq' := by
          simp[LexingState.src, haq']
        -- this shows that the state at the fst is "accepting" in the fsa
        have hfsa := (FSA_ch_to_LexingFST spec (seed_wr) LexingState.start aq'
           (by simp; by_contra ha; rw[ha] at haccept; contradiction)).mp this

        have hq'aq' : q' = LexingState.id aq' := by
          rw[FST.evalFrom_fold_seed_eq_evalFrom_seed] at h₂
          simp[FST.evalFrom_seed] at h₂
          simp at hfsa
          simp[hfsa] at h₂
          exact Eq.symm h₂

        -- find out the token that is produced
        let produced_token := spec.accept_seq_term seed_wr haccept
        -- have hseq_term : aq = spec_term
        have hlex_trans :
          (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) head = some (LexingState.start, seed_ts ++ [ExtChar.char produced_token, ExtChar.eos]) := by
          simp at h₁ ⊢
          rw[←FST.evalFrom_fold_eq_evalFrom] at h₁
          simp[FST.evalFrom_fold_seed] at h₁ ⊢
          simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run, hh]
          simp[hq'aq', LexingState.src, haq']
          simp[produced_token]
          simp[LexerSpec.accept_seq_term]
          have : afinal = spec.automaton.evalFrom spec.automaton.start seed_wr := by simp[afinal]
          conv =>
            rhs
            pattern spec.automaton.evalFrom spec.automaton.start seed_wr
            rw[←this]
          simp[haq', this]

        have hlex_wp_step : (BuildLexingFST spec).eval (wp ++ [head]) = some (LexingState.start, seed_ts ++ [.char produced_token, ExtChar.eos]) := by
          simp[FST.eval] at h₁ ⊢
          rw[←FST.evalFrom_fold_eq_evalFrom] at h₁ ⊢
          simp[FST.evalFrom_fold, FST.evalFrom_fold_seed] at h₁ ⊢
          rw[h₁]
          exact hlex_trans

        have hplex_step : PartialLex spec (wp ++ [head]) = some (seed_ts ++ [.char produced_token, ExtChar.eos], []) := by
          simp[PartialLex, PartialLex_seed] at h₀ ⊢
          rw[h₀]
          simp[PartialLex_trans, hh]
          simp[produced_token]
          simp[haccept]

        have lex_wr_step : (BuildLexingFST spec).eval [] = some (LexingState.start, []) := by
          simp[BuildLexingFST, Id.run, FST.eval, FST.evalFrom]
        have ih := ih (wp ++ [head]) LexingState.start (seed_ts ++ [.char produced_token, ExtChar.eos]) [] hplex_step hlex_wp_step lex_wr_step

        simp[hh] at hlex_trans
        rw[hlex_trans]
        simp[produced_token] at ih

        convert ih
      . simp[haccept]
        by_cases hempty : seed_wr = []
        . simp at hempty
          have hlex_trans :
            (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) head = some (LexingState.start, seed_ts ++ [ExtChar.eos]) := by
            simp[FST.eval] at h₁ ⊢
            rw[←FST.evalFrom_fold_eq_evalFrom] at h₁
            simp[FST.evalFrom_fold, FST.evalFrom_fold_seed] at h₁ ⊢
            simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run, hh]
            -- what q' is when seed_wr = []
            have hq'_start : q' = LexingState.start := by
              rw[FST.evalFrom_fold_seed_eq_evalFrom_seed] at h₂
              simp[FST.evalFrom_seed, hempty] at h₂
              exact Eq.symm h₂
            simp[hq'_start, LexingState.src]
            simp[old_q0] at h_q0_na
            simp[h_q0_na]

          have hlex_wp_step : (BuildLexingFST spec).eval (wp ++ [head]) = some (LexingState.start, seed_ts ++ [ExtChar.eos]) := by
            simp[FST.eval] at h₁ ⊢
            rw[←FST.evalFrom_fold_eq_evalFrom] at h₁ ⊢
            simp[FST.evalFrom_fold, FST.evalFrom_fold_seed] at h₁ ⊢
            rw[h₁]
            exact hlex_trans

          have hplex_step : PartialLex spec (wp ++ [head]) = some (seed_ts ++ [ExtChar.eos], []) := by
            simp[PartialLex, PartialLex_seed] at h₀ ⊢
            rw[h₀]
            simp[PartialLex_trans, hh, hempty]
            exact he

          have lex_wr_step : (BuildLexingFST spec).eval [] = some (LexingState.start, []) := by
            simp[BuildLexingFST, Id.run, FST.eval, FST.evalFrom]

          have ih := ih (wp ++ [head]) LexingState.start (seed_ts ++ [ExtChar.eos]) [] hplex_step hlex_wp_step lex_wr_step

          simp[hh] at hlex_trans
          rw[hlex_trans]
          simp at ih
          convert ih
          simp[hempty]
        .  -- we have no transition and must show thats the case for both of them
          simp[hempty]
          -- since seed_wr ≠ [], q' is not start
          have hq'_not_start : q' ≠ LexingState.start := by
            exact (Iff.ne h₃).mp hempty
          -- and so, the corresponding fsa state is the fst state
          simp[LexingState.src] at h₂_fsa
          cases hq' : q'
          case neg.start => contradiction
          rename_i src
          -- in particular, its not accepting
          have hlex_step : ((BuildLexingFST spec).evalFrom_fold_step (some (LexingState.id src, seed_ts)) ExtChar.eos) = none := by
            simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
            simp[FSA.accepts_iff] at haccept ⊢
            simp[hq', h₂_fsa] at haccept
            simp[haccept]

          simp[hlex_step]
    case char ch =>
      cases hstep : spec.automaton.step (LexingState.src spec q') ch
      case none =>
        simp_all
        by_cases haccept : LexingState.src spec q' ∈ spec.automaton.accept
        case pos =>
          let qsrc := LexingState.src spec q'
          let term := spec.term qsrc
          let unwrapped := term.get ((spec.hterm qsrc).mp haccept)
          cases hch : spec.automaton.step spec.automaton.start ch
          case none =>
            -- no transition in both if ch is not in the prefix language
            have : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = none := by
              simp[PartialLex_trans]
              simp[FSA.evalFrom_append]
              simp[h₂_fsa, haccept]
              simp[FSA.evalFrom, hstep]
              simp[hch]
            simp[this]
            have : ((BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch)) = none := by
              simp[BuildLexingFST, Id.run, FST.evalFrom_fold_step]
              simp[hch, hstep, haccept]
            simp[this]
          case some qnext =>
            have hplex_step : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = some (seed_ts ++ [ExtChar.char unwrapped], [ch]) := by
              simp[PartialLex_trans]
              simp[FSA.evalFrom_append]
              simp[h₂_fsa, haccept]
              simp[FSA.evalFrom, hstep]
              simp[unwrapped, term, qsrc]
              simp[hch]

            have hplex_trans : PartialLex spec (wp ++ [head]) = some (seed_ts ++ [ExtChar.char unwrapped], [ch]) := by
              simp[PartialLex_seed] at h₀ ⊢
              rw[h₀]
              simp[hh]
              exact hplex_step

            have hlex_wp_step : (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch) = some (LexingState.id qnext, seed_ts ++ [ExtChar.char unwrapped]) := by
              simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
              simp[hstep, haccept]
              simp[hch, unwrapped, term, qsrc]

            have hlex_wp_trans : (BuildLexingFST spec).eval (wp ++ [head]) = some (LexingState.id qnext, seed_ts ++ [ExtChar.char unwrapped]) := by
              simp[FST.eval] at h₁ ⊢
              rw[←FST.evalFrom_fold_eq_evalFrom] at h₁ ⊢
              simp[FST.evalFrom_fold, FST.evalFrom_fold_seed] at h₁ ⊢
              rw[h₁]
              simp[hh]
              exact hlex_wp_step

            have lex_wr_step : (BuildLexingFST spec).eval [ch] = some (LexingState.id qnext, []) := by
              simp[BuildLexingFST, Id.run, FST.eval, FST.evalFrom]
              simp[LexingState.src, hch]

            have ih := ih (wp ++ [head]) (LexingState.id qnext) (seed_ts ++ [ExtChar.char unwrapped]) [ch] hplex_trans hlex_wp_trans lex_wr_step (by simp)
            rw[hplex_step]
            rw[hlex_wp_step]
            unfold FST.evalFrom_fold_seed at ih
            exact ih
        case neg =>
          have : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = none := by
            simp[PartialLex_trans]
            simp[FSA.evalFrom_append]
            simp[h₂_fsa, FSA.evalFrom, hstep, haccept]
          simp[this]
          have : ((BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch)) = none := by
            simp[BuildLexingFST, Id.run, FST.evalFrom_fold_step]
            simp[hstep, haccept]
          simp[this]
      case some dst =>
        -- both will effectively take the transition specified by automata
        have hplex_step : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = some (seed_ts, seed_wr ++ [ch]) := by
          simp[PartialLex_trans]
          simp[FSA.evalFrom_append]
          simp[h₂_fsa]
          simp[FSA.evalFrom, hstep]

        have hplex_trans : PartialLex spec (wp ++ [head]) = some (seed_ts, seed_wr ++ [ch]) := by
          simp[PartialLex_seed] at h₀ ⊢
          rw[h₀]
          simp[hh]
          exact hplex_step

        have hlex_wp_step : (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch) = some (LexingState.id dst, seed_ts) := by
          simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
          simp[hstep]

        have hlex_wp_trans : (BuildLexingFST spec).eval (wp ++ [head]) = some (LexingState.id dst, seed_ts) := by
          simp[FST.eval] at h₁ ⊢
          rw[←FST.evalFrom_fold_eq_evalFrom] at h₁ ⊢
          simp[FST.evalFrom_fold, FST.evalFrom_fold_seed] at h₁ ⊢
          rw[h₁]
          simp[hh]
          exact hlex_wp_step

        have lex_wr_step : (BuildLexingFST spec).eval (seed_wr ++ [ch]) = some (LexingState.id dst, []) := by
          simp[FST.evalFrom, FST.evalFrom_append]
          rw[←FST.evalFrom_fold_eq_evalFrom]
          simp[FST.evalFrom_fold]
          rw[h₂]
          simp[BuildLexingFST, Id.run, hstep]

        have ih := ih (wp ++ [head]) (LexingState.id dst) seed_ts (seed_wr ++ [ch]) hplex_trans hlex_wp_trans lex_wr_step (by simp)
        rw[hplex_step]
        rw[hlex_wp_step]
        unfold FST.evalFrom_fold_seed at ih
        simp at ih
        exact ih

theorem PartialLex_to_LexingFST (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) :
  ∀ w, match PartialLex spec w with
       | some (ts', wr) =>
          ∃ q', (BuildLexingFST spec).eval w = some (q', ts') ∧ (BuildLexingFST spec).eval wr = some (q', [])
       | none => (BuildLexingFST spec).eval w = none := by

  let fst := BuildLexingFST spec
  let new_q0 := fst.start

  have := PartialLex_to_LexingFST_evalFold spec he
  intro w
  have := this [] w new_q0 [] []
  have := this rfl
  have := this (by simp[FST.eval, fst, new_q0]) (by simp[FST.eval, fst, new_q0]) (by simp[new_q0, fst])
  simp[PartialLex] at this ⊢
  rw[FST.evalFrom_fold_seed_eq_evalFrom_seed] at this
  simp[FST.evalFrom_seed] at this
  split
  <;> simp_all
  rename_i t'' wr _ _ _
  obtain ⟨q'', hq⟩ := this
  exists q''
  split at hq
  simp_all
  rename_i heq
  constructor
  simp[←hq.left]
  exact heq
  rw[FST.evalFrom_fold_seed_eq_evalFrom_seed] at hq
  simp[FST.evalFrom_seed] at hq
  split at hq
  try split at this
  rename_i heq
  simp at hq
  simp[hq] at heq
  simp_all
  split at this
  <;> simp_all
  assumption


theorem PartialLexRel_to_LexingFST (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned) :
  ∀ w terminals unlexed,
    PartialLexRel spec w terminals unlexed →
      ∃ q', (BuildLexingFST spec).eval w = some (q', terminals)
          ∧ (BuildLexingFST spec).eval unlexed = some (q', []) := by
  intro w terminals unlexed h
  have hpl := (PartialLex_pruned_eq_PartialLexRel spec hpruned w terminals unlexed).mp h
  have := PartialLex_to_LexingFST spec he w
  simp only [hpl] at this
  obtain ⟨q', heval_w, heval_unlexed⟩ := this
  exists q'

theorem LexingFST_to_PartialLexRel (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned) :
  ∀ w q' terminals,
    (BuildLexingFST spec).eval w = some (q', terminals) →
    ∃ (unlexed: List α),
      (BuildLexingFST spec).eval unlexed = some (q', []) ∧ PartialLexRel spec w terminals unlexed := by
  intro w q' terminals h
  cases hpl : PartialLex spec w
  case none =>
    have : (BuildLexingFST spec).eval w = none := by
      have := PartialLex_to_LexingFST spec he w
      simp only [hpl] at this
      exact this
    simp at this
    simp[this] at h
  case some ts_wr =>
    have ⟨ ts', wr⟩ := ts_wr
    have := PartialLex_to_LexingFST spec he w
    simp only [hpl] at this
    obtain ⟨q'', heval_w, heval_wr⟩ := this
    have heq : q'' = q' ∧ ts' = terminals := by
      simp at h heval_w
      simp[heval_w] at h
      exact h
    exists wr
    simp at heval_wr ⊢
    constructor
    simp[heq] at heval_wr
    exact heval_wr
    have hrel := (PartialLex_pruned_eq_PartialLexRel spec hpruned w ts' wr).mpr
    simp only [hpl, heq] at hrel
    simp[hrel]

lemma LexingFst_smallStep (spec: LexerSpec α Γ σ) :
  ∀ q a q' terminals,
    (BuildLexingFST spec).step q a = some (q', terminals) →
    terminals = [] ∨ (∃ t, terminals = [t]) ∨ (LexingState.src spec q ∈ spec.automaton.accept ∧ a = ExtChar.eos ∧ ∃ t, terminals = [ExtChar.char t, ExtChar.eos]) := by
  intro q a q' terminals h
  simp[BuildLexingFST, Id.run] at h
  split at h <;> split at h <;> simp_all
  have ⟨ha, _, pf⟩ := h
  apply Or.inr
  have pf := pf.right.right
  rw[←pf]
  simp
  apply Or.inr
  apply Or.inr
  rw[←h.right]
  simp
  simp[←h.right]


namespace Detokenizing

universe x
variable { V : Type x }
variable [BEq V]

def BuildDetokenizingFST [v: Vocabulary α V] : FST V α Unit :=
  let step := fun _ s => some (Unit.unit, v.flatten s)
  FST.mk Unit.unit step [Unit.unit]

def detokenize [v: Vocabulary α V] (w : List V) : List α :=
  match w with
  | [] => []
  | w' :: ws => v.flatten w' ++ detokenize ws

omit [DecidableEq α] [BEq V] in
lemma detokenize_flatmap [v: Vocabulary α V] (w : List V) :
  detokenize (v := v) w = (w.flatMap (fun big => v.flatten big)) := by
  induction w
  case nil => simp[detokenize, List.flatMap]
  case cons head tail ih =>
    simp[detokenize, List.flatMap]
    simp[ih]
    rfl

omit [DecidableEq α] [BEq V] in
lemma detokenize_app [v: Vocabulary α V] (s1 s2 : List V) :
  detokenize (v := v) (s1 ++ s2) = detokenize (v := v) s1 ++ detokenize (v := v) s2 := by
  induction s1
  case nil => simp[detokenize]
  case cons head tail ih =>
    simp[detokenize, List.append_assoc]
    rw[←ih]

omit [DecidableEq α] [BEq V] in
theorem detokenizerFST_eq_detokenizer [v: Vocabulary α V] :
  ∀ ( w : List V ), some ((Unit.unit, detokenize w,)) = (BuildDetokenizingFST (v := v)).eval w := by
  intro w
  induction w
  case nil =>
    simp[detokenize, BuildDetokenizingFST, FST.evalFrom]
  case cons head tail ih =>
    simp[FST.eval, FST.evalFrom, detokenize]
    conv =>
      pattern BuildDetokenizingFST.step BuildDetokenizingFST.start head
      simp[BuildDetokenizingFST]
    simp at ih ⊢
    conv at ih =>
      pattern (BuildDetokenizingFST).start
      simp[BuildDetokenizingFST]
    cases h : (BuildDetokenizingFST (v := v)).evalFrom () tail
    <;> rw[h] at ih
    simp at ih
    simp at ih ⊢
    rename_i val
    let ⟨_, tail⟩ := val
    simp at ih ⊢
    exact ih

omit [DecidableEq α] [BEq V] in
lemma detokenizer_comp_step [v: Vocabulary α V] { σ0 } (f : FST α Γ σ0) (q: σ0) :
  ∀ a, ((FST.compose (BuildDetokenizingFST (v := v)) f).step (Unit.unit, q) a) =
    (f.evalFrom q (v.flatten a)).map (fun (q, out) => ((Unit.unit, q), out)) := by
  intro a
  simp[FST.compose, FST.compose_fun_step, BuildDetokenizingFST]
  split <;> simp_all

omit [DecidableEq α] [BEq V] in
theorem detokenizer_comp [v: Vocabulary α V] { σ0 } (f : FST α Γ σ0) (q: σ0) :
  ∀ w, ((FST.compose (BuildDetokenizingFST (v := v)) f).evalFrom (Unit.unit, q) w) =
    (f.evalFrom q (detokenize (v := v) w)).map (fun (q, out) => ((Unit.unit, q), out)) := by
  intro w
  have := FST.compose_correct (BuildDetokenizingFST (v := v)) f w Unit.unit q
  rw[this]
  simp[FST.compose_fun_evalFrom]
  have := detokenizerFST_eq_detokenizer (v := v) w
  simp at this
  rw[←this]
  simp
  simp[Option.map]
  split
  <;> simp_all

-- if two words detokenize to the same thing, then their compositions with any fst are equal
omit [DecidableEq α] [BEq V] in
theorem detokenize_eq_comp [v: Vocabulary α V] { σ0 } (w1: List V) (w2: List V) (f : FST α Γ σ0) (q: σ0) :
  detokenize (v := v) w1 = detokenize (v := v) w2 → (FST.compose (BuildDetokenizingFST (v := v) ) f).evalFrom (Unit.unit, q) w1 = (FST.compose (BuildDetokenizingFST (v := v)) f).evalFrom (Unit.unit, q) w2 := by
  intro h
  have hw1 := detokenizer_comp (v := v) f q w1
  have hw2 := detokenizer_comp (v := v) f q w2
  rw[←h] at hw2
  cases hd : detokenize (v := v) w1
  <;> simp[hd] at hw1 hw2
  <;> simp[hw1, hw2]

-- via the singleton assumption on the vocabulary, this means
-- that if something is realizable, it is realizable via singletons
omit [DecidableEq α] [BEq V] in
theorem detokenize_singleton [v: Vocabulary α V] { σ0 } (f: FST α Γ σ0) (q: σ0) :
  ∀ ( w : List V ), ∃ ( ws : List V ),
    (FST.compose (BuildDetokenizingFST (v := v) ) f).evalFrom (Unit.unit, q) w = (FST.compose (BuildDetokenizingFST (v := v)) f).evalFrom (Unit.unit, q) ws
    ∧ (∀ t ∈ ws, ∃ t0, v.flatten t = [t0]) := by
  intro w
  let ws := w.flatMap (fun big => (v.flatten big).map (fun ch => v.embed ch))
  have h_w_ws : detokenize (v := v) w = detokenize (v := v) ws := by
    induction w
    case nil => simp[ws]
    case cons head tail ih =>
      simp[ws, detokenize]
      simp at ih
      simp[detokenize_app]
      rw[←ih]
      simp
      rw[detokenize_flatmap]
      simp[List.flatMap_map]
      simp[v.fe]
  exists ws
  have := detokenize_eq_comp (v := v) w ws f q
  constructor
  exact this h_w_ws
  simp[ws]
  intro t x hx x_1 _ hx_1
  simp[←hx_1, v.fe]


def BuildDetokLexer [v: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ) : FST V (Ch Γ) (Unit × LexingState σ) :=
  let lex_fst := BuildLexingFST spec
  let detok := Detokenizing.BuildDetokenizingFST (v := v)
  FST.compose detok lex_fst

-- whitespace is accepted exactly in the start state and the state after the start state
-- and there is at least one non whitespace token
def whitespace_assumption (spec: LexerSpec α Γ σ) (twhite : α) (qwhite : σ) : Prop :=
  qwhite ∈ spec.automaton.accept ∧
  spec.automaton.step spec.automaton.start twhite = some qwhite ∧
  spec.automaton.step qwhite twhite = some qwhite ∧
  (∀ t', twhite ≠ t' → spec.automaton.step qwhite t' = none) ∧
  (∀ q, q ≠ spec.automaton.start ∧ q ≠ qwhite → spec.automaton.step q twhite = none)

def whitespace_terminal (spec: LexerSpec α Γ σ) (twhite : α) (qwhite : σ) (hw: whitespace_assumption spec twhite qwhite) : Γ :=
  let ret := spec.term qwhite
  have := (spec.hterm qwhite).mp hw.left
  ret.get this

@[simp]
private def produce {σ V Γ} (step : σ × V × σ × List (Ch Γ)) : List (Ch Γ) :=
  step.2.2.2

private lemma flatMap_prefix_suffix {σ V Γ} (l : List (σ × V × σ × List (Ch Γ))) (j : Nat) (x : List (Ch Γ))
    (h : l.flatMap (fun (_, _, _, d) => d) = x) :
    (l.take j).flatMap (fun (_, _, _, d) => d) ++ (l.drop j).flatMap (fun (_, _, _, d) => d) = x := by
  simp at h
  have h_app : (l.take j) ++ (l.drop j) = l := by simp[List.take_append_drop]
  rw[←h_app] at h
  simp only [List.flatMap_append] at h
  simp
  exact h

private lemma find_first_nonempty { σ V Γ } [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] (filtered_step_list : List (σ × V × σ × List (Ch Γ)))
    (x : List (Ch Γ)) (he : x ≠ [])
    (h_filt : filtered_step_list.flatMap produce = x) :
    ∃ idx, produce filtered_step_list[idx] ≠ [] ∧
           ∀ (j : Fin filtered_step_list.length), j < idx → produce filtered_step_list[j] = [] := by
  let oFirst := filtered_step_list.findFinIdx? (fun a => produce a != [])
  have h_some : oFirst.isSome := by
    by_contra ha
    simp only [not_not, ne_eq, bne_iff_ne, Option.not_isSome_iff_eq_none, findFinIdx?_eq_none_iff, oFirst] at ha
    have hnull: (List.map produce filtered_step_list) = List.map (fun _ => []) filtered_step_list := by
      apply List.map_congr_left
      exact ha
    simp[flatMap, hnull] at h_filt
    simp[h_filt] at he
  exists oFirst.get h_some
  have h_find : filtered_step_list.findFinIdx? (fun a => produce a != []) = some (oFirst.get h_some) := by
    simp only [Option.some_get, oFirst]
  have := findFinIdx?_eq_some_iff.mp h_find
  simp at this
  exact this

private lemma empty_prefix_all_empty {σ V Γ} (step_list : List (σ × V × σ × List (Ch Γ)))
    (idx : Fin step_list.length)
    (h_prefix : ∀ (j : Fin step_list.length), j < idx → produce step_list[j] = []) :
    (step_list.take idx).flatMap (fun a => produce a) = [] := by
  simp[List.flatMap]
  intro l hl
  obtain ⟨j, hjlt, hj⟩ := List.mem_take_iff_getElem.mp (by simpa using hl)
  rw[←hj]
  simp
  have hjlti := (Nat.lt_min.mp hjlt).left
  have : j < step_list.length := by
    have : idx < step_list.length := by simp
    exact Nat.lt_trans hjlti this
  exact h_prefix (Fin.mk j this) hjlti

-- Helper: show first element equals head of first nonempty transition
private lemma first_eq_head_of_first_nonempty {Γ V σ} (x : List (Ch Γ)) (he : x ≠ [])
    (step_list : List (σ × V × σ × List (Ch Γ))) (idx : Fin step_list.length)
    (h_filt : step_list.flatMap (fun a => produce a) = x)
    (h_prefix_empty : (step_list.take idx).flatMap (fun a => produce a) = [])
    (hne : produce step_list[idx] ≠ []) :
    x.head he = (produce step_list[idx]).head hne := by
  simp at hne
  have h_decomp := flatMap_prefix_suffix step_list idx x h_filt
  simp only [produce] at h_prefix_empty
  simp[h_prefix_empty] at h_decomp
  subst h_decomp
  simp[List.flatMap]
  rw[List.head_flatten_eq_head_head]
  simp
  simp[hne]

omit [BEq V] in
lemma detok_rs_pfx [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { twhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts)
  (hwa: whitespace_assumption spec twhite qwhite) (q: LexingState σ) :
  let white_term := (whitespace_terminal spec twhite qwhite hwa)
  let lexer := BuildDetokLexer (v := vocab) spec
  lexer.tailModdedRealizableSequences (Unit.unit, q) white_term =
    { Ts | Ts = [] ∨
           (∃ t tsfx,
             ¬Ts.contains (ExtChar.char white_term) ∧
             Ts = t :: tsfx ∧ t ∈ lexer.singleProducible (Unit.unit, q)) } := by
  ext x
  let lexer := BuildDetokLexer (v := vocab) spec
  have hlexer : lexer = (BuildDetokenizingFST.compose (BuildLexingFST spec)) := by
    simp[BuildDetokLexer, lexer]
  set white_term := (whitespace_terminal spec twhite qwhite hwa) with hwhite_term

  apply Iff.intro
  -- forward:
    -- effectively just need to show that it must start with a single producible token
    -- via assumption of singletons
    -- otherwise, the fact that tsfx can be anything means that we are done
  . intro h
    by_cases he : x = []
    . simp[he]
      rw[Set.mem_setOf]
      simp
    . rw[Set.mem_setOf]
      apply Or.inr
      exists x.head he
      exists x.tail
      simp[FST.tailModdedRealizableSequences] at h
      rw[Set.mem_setOf] at h
      obtain ⟨v, hv_rs, hv_filter⟩ := h
      have hvne : v ≠ [] := by
        by_contra hve
        simp[hve] at hv_filter
        exact he hv_filter
      constructor
      · rw[←hv_filter.right]; simp
      constructor
      · simp

      -- only non trivial part
      show x.head he ∈ lexer.singleProducible ((), q)
      simp[FST.singleProducible]
      simp[FST.realizableSequences] at hv_rs
      rw[Set.mem_setOf] at hv_rs
      obtain ⟨_, qf, w, hw⟩ := hv_rs
      have h_singleton := detokenize_singleton (BuildLexingFST spec) q w
      rw[←hlexer] at h_singleton
      obtain ⟨ws, h_eq, h_ws_singleton⟩ := h_singleton
      rw[hw] at h_eq

      have h_step_list_app_v := lexer.stepList_of_eval ((), q) ws
      simp[←h_eq] at h_step_list_app_v
      obtain ⟨step_list, h_step_list⟩ := h_step_list_app_v
      -- so we know that the translist concatenated together forms v
      -- and that v filtered forms x
      -- so then translist filtered concatenated forms x

      let rem_ws := fun t => t != ExtChar.char white_term
      let filtered_step_list := step_list.map (fun (a, b, c, d) => (a, b, c, d.filter rem_ws))

      have h_filt_step_list : (filtered_step_list.flatMap (fun (_, _, _, d) => d)) = x := by
        simp[filtered_step_list, List.flatMap]
        conv =>
          pattern ((fun x => _) ∘ _)
          unfold Function.comp
          simp
        rw[←hv_filter.right]
        rw[←h_step_list.right]
        simp[List.flatMap]
        conv =>
          pattern ((fun x => _) ∘ _)
          unfold Function.comp
          simp

      -- by using he, find the first nonempty transition
      -- this does use a little indexing which makes stuff hard to prove
      obtain ⟨firstTransitionIdx, hft_ne, h_prefix_empty⟩ :=
        find_first_nonempty filtered_step_list x he h_filt_step_list

      have h_firstTransition_lt_stepList : firstTransitionIdx < step_list.length := by
        have : filtered_step_list.length = step_list.length := by simp[filtered_step_list]
        rw[←this]
        simp

      set unfiltered_emptyPrefix := step_list.take firstTransitionIdx with hunfiltered_emptyPrefix

      have huft_ne : step_list[firstTransitionIdx.val].2.2.2 ≠ [] := by
        by_contra he
        simp[he, filtered_step_list] at hft_ne

      have h_emptyPrefix_flatMap : (filtered_step_list.take firstTransitionIdx).flatMap (fun (_, _, _, d) => d) = [] :=
        empty_prefix_all_empty filtered_step_list firstTransitionIdx h_prefix_empty

      have h_v_prefix_suffix : v = unfiltered_emptyPrefix.flatMap (fun (_, _, _, d) => d) ++
                                  (step_list.drop firstTransitionIdx).flatMap (fun (_, _, _, d) => d) :=
        Eq.symm (flatMap_prefix_suffix step_list firstTransitionIdx v h_step_list.right)

      -- so then, if the firstTransition is not empty (which its not), its head must be the global head
      have h_first_from_ft : x.head he = filtered_step_list[firstTransitionIdx].2.2.2.head
          (by simp at hft_ne; exact hft_ne) :=
        first_eq_head_of_first_nonempty x he filtered_step_list firstTransitionIdx
          h_filt_step_list h_emptyPrefix_flatMap hft_ne

      -- translist (and translist filtered) consists of steps of 0, 1, or 2
      -- lets show that the first one must be 1 or 2
      have h_first_production : lexer.step step_list[firstTransitionIdx].1 step_list[firstTransitionIdx].2.1 =
          some step_list[firstTransitionIdx].2.2 := by
        have := lexer.stepList_zip ((), q) ws
        simp only [h_step_list] at this
        exact this step_list[firstTransitionIdx] (by simp)

      have ⟨flat, h_flat⟩ : ∃ t, vocab.flatten step_list[firstTransitionIdx.val].2.1 = [t] := by
        have := lexer.stepList_w ((), q) ws
        simp only [h_step_list] at this
        have : step_list[firstTransitionIdx].2.1 ∈ ws := by
          have h_in : step_list[firstTransitionIdx].2.1 ∈ List.map (fun x => x.2.1) step_list := by
            apply mem_map.mpr
            exists step_list[firstTransitionIdx]
            simp
          rw[this] at h_in
          exact h_in
        exact h_ws_singleton step_list[firstTransitionIdx].2.1 this

      simp[lexer, BuildDetokLexer] at h_first_production
      rw[detokenizer_comp_step] at h_first_production
      simp[h_flat] at h_first_production
      obtain ⟨q', produced, hstep, hq'produced⟩ := h_first_production
      have h_first_production_small := LexingFst_smallStep spec step_list[firstTransitionIdx].1.2 flat q' produced hstep

      -- the produced tokens can't be 0 (as it is assumed to be first non zero)
      have hproduced_ne : produced ≠ [] := by
        simp[filtered_step_list] at hft_ne
        have : produced = step_list[firstTransitionIdx].2.2.2 := by
          simpa using congrArg Prod.snd hq'produced
        simp[this]
        exact huft_ne
      simp[hproduced_ne] at h_first_production_small


      -- we showed before that the filtered prefix is empty
      -- but we actually need that the unfiltered prefix is empty
      -- we can get this by using hv.left, namely that the source
      -- realizable sequence did not start with whitespace
      -- consequently, the unfiltered emptyPrefix cannot contain whitespace
      have h_prefix_production_must_all_be_wt : ∀ p ∈ unfiltered_emptyPrefix.flatMap (fun (_, _, _, d) => d),
          p = ExtChar.char white_term := by
        intro p hp
        simp only [mem_flatMap, unfiltered_emptyPrefix] at hp
        obtain ⟨a, ha⟩ := hp
        have : a.2.2.2.filter rem_ws = [] := by
          obtain ⟨j, hjlt, hj⟩ := List.mem_take_iff_getElem.mp ha.left
          have : filtered_step_list[j].2.2.2 = a.2.2.2.filter rem_ws := by
            simp[filtered_step_list, hj]
          rw[←this]
          have : j < filtered_step_list.length := by
            have : firstTransitionIdx < filtered_step_list.length := by simp
            exact Nat.lt_trans (Nat.lt_min.mp hjlt).left this
          apply h_prefix_empty (Fin.mk j this)
          exact (Nat.lt_min.mp hjlt).left
        simp[rem_ws] at this
        exact this p ha.right

      have h_unfiltered_emptyPrefix : unfiltered_emptyPrefix.flatMap (fun (_, _, _, d) => d) = [] := by
        by_contra hne
        have : v.head hvne = ExtChar.char white_term := by
          have : v.head hvne = (unfiltered_emptyPrefix.flatMap (fun (_, _, _, d) => d)).head hne := by
            simp[h_v_prefix_suffix]
            exact head_append_left hne
          simp[this]
          exact h_prefix_production_must_all_be_wt _ (by simp)
        have : [ExtChar.char white_term] <+: v := by
          exists v.tail
          have cons : v = v.head hvne :: v.tail := by simp
          simp[this] at cons ⊢
          exact cons.symm
        exact hv_filter.left this

      have h_unfiltered_emptyPrefixTrans : (List.take (min (firstTransitionIdx.toNat + 1) ws.length) step_list) =
               unfiltered_emptyPrefix ++ [step_list[firstTransitionIdx]] := by
        have : firstTransitionIdx + 1 = min (firstTransitionIdx.toNat + 1) ws.length := by
          simp[Nat.add_one_le_iff]
          have := lexer.stepList_len ((), q) ws
          simp[h_step_list.left] at this
          rw[←this]
          have : step_list.length = filtered_step_list.length := by simp[filtered_step_list]
          rw[this]
          simp
        rw[←this]
        simp[List.take_add_one, unfiltered_emptyPrefix]

      cases h_first_production_small
      -- if its 1, we're 'done', just need to combine results
      . rename_i h_production
        obtain ⟨t, ht⟩ := h_production
        -- we already showed that first is the same as t
        -- and that production on the prefix is empty
        -- now need to glue everything together
        let wfinal := (ws.take (firstTransitionIdx.toNat + 1))
        exists wfinal
        have hpfx := lexer.stepList_prefix_w ((), q) ws
        simp[h_step_list] at hpfx
        have h_step_wfinal : lexer.stepList ((), q) wfinal =
            some (take wfinal.length step_list) := by
          apply hpfx
          simp[wfinal, List.take_prefix]

        have := lexer.eval_of_stepList ((), q) wfinal
        simp[h_step_wfinal] at this
        have ⟨a, b, hterm⟩ := this
        exists a
        exists b
        convert hterm
        simp only [wfinal, length_take]
        rw[h_unfiltered_emptyPrefixTrans]
        simp[flatMap_append]
        simp[h_unfiltered_emptyPrefix]
        -- these proofs use proofs (dependent types ig) within their type (for accessing head)
        -- so its often motive incorrect to do rewrites
        -- this adds a lot of type gymnastics so i have to do this weird thing here
        let firstTransition := filtered_step_list[firstTransitionIdx]
        have ⟨head, tail, hcons, hhead⟩ : ∃ H T, firstTransition.2.2.2 = H :: T ∧ H = x.head he := by
          cases h : filtered_step_list[firstTransitionIdx].2.2.2
          <;> simp at h_first_from_ft
          . simp at hft_ne
            contradiction
          . rename_i head tail
            exists head, tail
            simp at h
            simp[h, h_first_from_ft]
        rw[←hhead]
        simp[firstTransition, filtered_step_list] at hcons
        have := congrArg Prod.snd hq'produced
        simp[ht] at this
        rw[←this] at hcons
        simp[←this]
        simp[filter] at hcons
        split at hcons
        <;> (
          simp at hcons
          try simp[hcons]
        )
      . rename_i h_production
        -- its only two if second one is EOS (this is the annoying case)
        -- in this case, replace the eos with whitespace and then we will singly produce the target
        obtain ⟨hq, hflat, t, ht⟩ := h_production
        exists (ws.take firstTransitionIdx) ++ [vocab.embed twhite]
        have hpfx := lexer.stepList_prefix_w ((), q) ws
        simp[h_step_list] at hpfx
        have h_step_empty : lexer.stepList ((), q) (ws.take firstTransitionIdx) =
            some (take (ws.take firstTransitionIdx).length step_list) := by
          apply hpfx
          simp[List.take_prefix]

        have : (ws.take firstTransitionIdx).length = firstTransitionIdx.toNat := by
          simp
          have := lexer.stepList_len ((), q) ws
          simp[h_step_list] at this
          rw[←this]
          have : step_list.length = filtered_step_list.length := by simp[filtered_step_list]
          rw[this]
          simp
        rw[this] at h_step_empty
        have := lexer.eval_of_stepList ((), q) (ws.take firstTransitionIdx)
        simp[h_step_empty] at this
        rw[←hunfiltered_emptyPrefix] at this
        simp[h_unfiltered_emptyPrefix] at this
        have ⟨u, emptyq', hemptyq'⟩ := this

        have : firstTransitionIdx < ws.length := by
          have := lexer.stepList_len ((), q) ws
          simp[h_step_list.left] at this
          rw[←this]
          have : filtered_step_list.length = step_list.length := by simp[filtered_step_list]
          rw[←this]
          simp

        have h_emptyq_first_trans := lexer.stepList_eval_take ((), q) ws (Fin.mk firstTransitionIdx this)
        simp[hemptyq', h_step_list] at h_emptyq_first_trans
        have hindex_good : step_list[firstTransitionIdx.val]? = some step_list[firstTransitionIdx] := by simp
        rw[hindex_good] at h_emptyq_first_trans
        simp at h_emptyq_first_trans
        simp[←h_emptyq_first_trans] at hq
        simp[FST.evalFrom_append, hemptyq']
        exists Unit.unit
        simp[lexer, BuildDetokLexer]
        cases u
        simp[detokenizer_comp_step]
        simp[vocab.fe, BuildLexingFST, Id.run, hq]
        -- in accept so couldn't be start
        have hnstart : LexingState.src spec emptyq' ≠ spec.automaton.start := by
          intro h
          rw[h] at hq
          simp[FSA.accepts_iff] at hempty
          exact hempty hq
        -- it couldn't be qwhite either, but the reason is more subtle
        -- basically if it was, then we would've produced white as the first token = impossible
        have hvhead : v.head hvne = t := by
            simp[h_v_prefix_suffix, h_unfiltered_emptyPrefix]
            simp[List.flatMap]
            rw[List.head_flatten_eq_head_head]
            <;> simp[←hq'produced, ht]
        have h_t_ne_white : t ≠ white_term := by
          by_contra heq
          have : v.head hvne = ExtChar.char white_term := by
            simp[hvhead]
            exact heq
          have : [ExtChar.char white_term] <+: v := by
            exists v.tail
            have cons : v = v.head hvne :: v.tail := by simp
            simp[this] at cons ⊢
            exact cons.symm
          exact hv_filter.left this
        have hxhead_vhead : x.head he = v.head hvne := by
          simp_rw[←hv_filter.right]
          simp[hvhead]
          have lem : (List.find? (fun x => x != ExtChar.char white_term) v) = some (ExtChar.char t) := by
            have : v = v.head hvne :: v.tail := by simp
            rw[this]
            simp[hvhead, h_t_ne_white]
          simp[lem]
        have h_first_eq_prod : ExtChar.char ((spec.term (LexingState.src spec emptyq')).get
            ((spec.hterm (LexingState.src spec emptyq')).mp hq)) = x.head he := by
          rw[hxhead_vhead]
          rw[hvhead]
          simp
          simp[hflat, BuildLexingFST, Id.run] at hstep
          have : step_list[firstTransitionIdx.val].1.2 = emptyq' := by
            have h := congrArg Prod.snd h_emptyq_first_trans
            simp at h
            exact h.symm
          rw[this] at hstep
          simp[hq, ht] at hstep
          exact hstep.right
        have hnqwhite : LexingState.src spec emptyq' ≠ qwhite := by
          simp[hxhead_vhead, hvhead] at h_first_eq_prod
          rw[←h_first_eq_prod] at h_t_ne_white
          simp[white_term, whitespace_terminal] at h_t_ne_white
          have cp := spec.term_inj (LexingState.src spec emptyq') qwhite
          by_contra h
          simp_rw[h] at h_t_ne_white
          contradiction
        have ⟨_, hstart_good, _, _, hnonqhite_fail⟩ := hwa
        have : spec.automaton.step (LexingState.src spec emptyq') twhite = none := by
          exact hnonqhite_fail (LexingState.src spec emptyq') (by simp[hnstart, hnqwhite])
        simp[this]
        constructor
        exists qwhite
        exact h_first_eq_prod
  . rw[Set.mem_setOf]
    intro h
    cases h
    -- empty sequence is trivial
    . rename_i h
      simp[h]
      simp[FST.tailModdedRealizableSequences]
      rw[Set.mem_setOf]
      exists []
      simp[FST.realizableSequences]
      rw[Set.mem_setOf]
      exists ()
      exists q
      exists []
    . rename_i h
      have ⟨t, tsfx, h_no_white, h_eq, h_singleton⟩ := h
      -- since t is single producible, we can construct a sequence construction t followed by whitespace
      -- this is painful as shit
      -- produce each one via producing a token and a whitespace right after
      sorry
  -- backward
    -- show that we can create anything afterwards basically
    --

def whitespace_tokens : List (Token Char Unit) :=
  [ { symbol := Unit.unit, string := [' ', '\n', '\t'] } ]


end Detokenizing
