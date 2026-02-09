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

import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Char
import ConstrainedDecodingFormalization.Vocabulary

open List

universe u v w

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ]
  [BEq α] [BEq σ] [LawfulBEq σ]


structure LexerSpec (α Γ σ) where
  automaton : FSA α σ
  term: σ → Option Γ
  hterm: ∀ s, s ∈ automaton.accept ↔ (term s).isSome
  term_inj: ∀ s₁ s₂ t, term s₁ = some t ∧ term s₂ = some t → s₁ = s₂
  term_surj: ∀ t, ∃ s, term s = some t

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
  let ⟨A, term, hterm, _, _⟩ := spec

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
-- technically it's possible to derive the non whitespace based on other assumptions
-- but this is not necessary
-- this assumption also does allow whitespace to be formed by going to another state and back to the start
-- and then appending whitespace, but this doesn't hurt the proof
def whitespace_assumption (spec: LexerSpec α Γ σ) (tnonwhite : α) (twhite : α) (qnonwhite : σ) (qwhite : σ) : Prop :=
  qwhite ∈ spec.automaton.accept ∧
  (∀ s t, spec.automaton.step s t = some qwhite ↔ ((s = qwhite ∨ s = spec.automaton.start) ∧ t = twhite)) ∧
  (∀ t', twhite ≠ t' → spec.automaton.step qwhite t' = none) ∧
  (∀ q, q ≠ spec.automaton.start ∧ q ≠ qwhite → spec.automaton.step q twhite = none) ∧
  qnonwhite ∈ spec.automaton.accept ∧
  spec.automaton.step spec.automaton.start tnonwhite = some qnonwhite ∧
  tnonwhite ≠ twhite

def whitespace_terminal (spec: LexerSpec α Γ σ) (tnonwhite : α) (twhite : α) (qnonwhite : σ) (qwhite : σ) (hw: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) : Γ :=
  let ret := spec.term qwhite
  have := (spec.hterm qwhite).mp hw.left
  ret.get this

@[simp]
private def produce {σ V Γ} (step : σ × V × σ × List (Ch Γ)) : List (Ch Γ) :=
  step.2.2.2

private lemma detok_eval_embed { V Γ } [v: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ) (q: LexingState σ) (t: ExtChar α) :
  (BuildDetokLexer spec).step ((), q) (v.embed t) =
  (Option.map (fun x => (((), x.1), x.2)) ((BuildLexingFST spec).step q t)) := by
  simp[BuildDetokLexer]
  rw[detokenizer_comp_step]
  simp[v.fe]


private lemma flatMap_prefix_suffix {σ V Γ} (l : List (σ × V × σ × List (Ch Γ))) (j : Nat) (x : List (Ch Γ))
    (h : l.flatMap (fun (_, _, _, d) => d) = x) :
    (l.take j).flatMap (fun (_, _, _, d) => d) ++ (l.drop j).flatMap (fun (_, _, _, d) => d) = x := by
  simp at h
  have h_app : (l.take j) ++ (l.drop j) = l := by simp[List.take_append_drop]
  rw[←h_app] at h
  simp only [List.flatMap_append] at h
  simp
  exact h

-- general exchange argument
-- remove to shortest prefix that produces the token
-- may also assume that each word in the vocabulary is a singleton
omit [BEq V] in
private lemma exchange_basis [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ) (char: ExtChar Γ)
  (q : LexingState σ) (hchar: char ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
  ∃ wpfx wlast pfx last,
                (BuildDetokLexer (v := vocab) spec).stepList ((), q) (wpfx) = some (pfx) ∧
                (BuildDetokLexer (v := vocab) spec).stepList ((), q) (wpfx ++ [wlast]) = some (pfx ++ [last]) ∧
                flatMap produce pfx = [] ∧
                produce last = [char] ∧
                (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) (wpfx ++ [wlast]) = some (last.2.2.1, [char]) ∧
                ∀ t ∈ (wpfx ++ [wlast]), ∃ t0, vocab.flatten t = [t0] := by
  let lexer := BuildDetokLexer (v := vocab) spec
  simp[FST.singleProducible] at hchar
  obtain ⟨w, _, qf, hwqforg⟩ := hchar
  simp[BuildDetokLexer] at hwqforg
  obtain ⟨w, hwqf, hw⟩ := detokenize_singleton (v := vocab) (BuildLexingFST spec) q w
  rw[hwqforg, Eq.comm] at hwqf
  have dum : (BuildDetokenizingFST.compose (BuildLexingFST spec)) = BuildDetokLexer (v := vocab) spec := by simp[BuildDetokLexer]
  rw[dum] at hwqf
  have := lexer.stepList_of_eval ((), q) w
  simp[lexer, hwqf] at this
  obtain ⟨step_list, hstep_list, flat_step⟩ := this
  let firstTransitionIndexO := step_list.findFinIdx? (fun step => produce step ≠ [])
  have : firstTransitionIndexO.isSome := by
    by_contra h
    simp only [findFinIdx?_eq_none_iff, Option.not_isSome_iff_eq_none, firstTransitionIndexO] at h
    simp only [produce, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Decidable.not_not] at h
    have : flatMap (fun step => produce step) step_list = [] := by
      simp only [mem_map, produce, flatMap, flatten_eq_nil_iff]
      intro l he
      obtain ⟨a, ha⟩ := he
      rw[h a] at ha
      <;> simp[ha]
    simp only [produce] at this
    rw[flat_step.left] at this
    simp at this
  obtain ⟨firstTransitionIndex, ho⟩ : ∃ i, firstTransitionIndexO = some i := by
    simp only [Option.isSome_iff_exists, firstTransitionIndexO] at this
    exact this
  have hfirst := findFinIdx?_eq_some_iff.mp ho
  simp at hfirst
  obtain ⟨hne, hbefore⟩ := hfirst
  have h_prefix_empty : (step_list.take firstTransitionIndex).flatMap produce = [] := by
    simp[flatMap]
    intro l hl
    obtain ⟨j, hjlt, hj⟩ := List.mem_take_iff_getElem.mp (by simpa using hl)
    rw[←hj]
    simp
    have : j < step_list.length := Nat.lt_trans (Nat.lt_min.mp hjlt).left (by simp : firstTransitionIndex < step_list.length)
    exact hbefore (Fin.mk j this) (Nat.lt_min.mp hjlt).left
  unfold produce at h_prefix_empty
  -- The first non-empty transition produces exactly [char]
  have hprod_first : produce step_list[firstTransitionIndex] = [char] := by
    have h_decomp := flatMap_prefix_suffix step_list firstTransitionIndex [char] flat_step.left
    simp[h_prefix_empty] at h_decomp

    have : step_list[firstTransitionIndex] :: (step_list.drop firstTransitionIndex).tail = step_list.drop firstTransitionIndex := by
      have : firstTransitionIndex < step_list.length := by simp
      simp only [List.drop_eq_getElem_cons this]
      simp

    rw[←this] at h_decomp
    simp[flatMap] at h_decomp
    cases hprod : (drop (↑firstTransitionIndex) (map (fun x => x.2.2.2) step_list))
    <;> rw[hprod] at h_decomp
    . simp at h_decomp
    . rename_i head tail
      simp[append_eq_singleton_iff] at h_decomp
      set dummy := head :: tail with hdummy
      have : dummy.head (by simp) = head := by simp[dummy]
      simp_rw[←hprod] at this
      simp at this
      rw[←this] at h_decomp
      cases h_decomp
      case inr h => simp[h]
      case inl h => simp[hne] at h

  have hslen:= lexer.stepList_len ((), q) w
  simp[lexer, hstep_list] at hslen
  have hft_lt_w : firstTransitionIndex.val < w.length := by
     rw[←hslen]
     simp
  exists w.take firstTransitionIndex
  exists w[firstTransitionIndex]'hft_lt_w
  exists step_list.take firstTransitionIndex
  exists step_list[firstTransitionIndex]
  have hpfxo := lexer.stepList_prefix_w ((), q) w
  simp[lexer, hstep_list] at hpfxo
  have hpfx := hpfxo (List.take (↑firstTransitionIndex + 1) w) (by simp[List.take_prefix])
  constructor
  . have hpfx := hpfxo (List.take ↑firstTransitionIndex w) (by simp[List.take_prefix])
    simp[hpfx]
    exact Nat.le_of_lt hft_lt_w
  constructor
  . simp[hpfx]
    simp[hslen]
  . constructor
    · simp[flatMap]
      intro l hl
      obtain ⟨j, hjlt, hj⟩ := List.mem_take_iff_getElem.mp (by simpa using hl)
      rw[←hj]
      simp
      have : j < step_list.length := Nat.lt_trans (Nat.lt_min.mp hjlt).left (by simp : firstTransitionIndex < step_list.length)
      exact hbefore (Fin.mk j this) (Nat.lt_min.mp hjlt).left
    constructor
    . exact hprod_first
    . have := lexer.eval_of_stepList ((), q) (take (↑firstTransitionIndex + 1) w)
      simp[lexer, hpfx] at this
      have hlt : firstTransitionIndex + 1 ≤ w.length := by simp[←hslen, Nat.add_one_le_of_lt]
      simp[hlt] at this
      simp[this]
      simp[getLast?_take]
      rw[take_add_one]
      simp only [List.flatMap_append, h_prefix_empty]
      simp at hprod_first
      simp[hprod_first]
      intro t ht
      apply hw
      exact List.mem_of_mem_take ht

-- the only reachable state from qwhite is qwhite
private lemma qwhite_sink { σ α } [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { tnonwhite twhite qnonwhite qwhite } (spec: LexerSpec α Γ σ)
   (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) :
    ∀ q w, spec.automaton.evalFrom qwhite w = some q → q = qwhite := by
  intro q w h
  induction w
  case nil =>
     simp[FSA.evalFrom] at h
     exact h.symm
  case cons head tail ih =>
    obtain ⟨_, hstay , hwa, _⟩ := hwa
    simp[FSA.evalFrom] at h
    split at h
    simp at h
    rename_i heq
    have : head = twhite := by
      by_contra hx
      have := hwa head (by intro hx'; exact hx hx'.symm)
      rw[this] at heq
      simp at heq
    have hstay := hstay qwhite head
    simp[this] at hstay heq
    rw[hstay] at heq
    simp at heq
    simp[←heq] at h
    exact ih h

-- for any non qwhite state
-- we can build a path to it that does not start with twhite
omit [BEq V] in
private lemma path_nonwhitespace [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { tnonwhite twhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hpruned: spec.automaton.pruned) (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite)
  : ∀ qtarget, qtarget ≠ qwhite → qtarget ≠ spec.automaton.start →
    ∃ ws wt qi, ws ≠ twhite ∧
            spec.automaton.step spec.automaton.start ws = some qi ∧
            (BuildDetokLexer (v := vocab) spec).step (Unit.unit, LexingState.start) (vocab.embed ws) = some (((), LexingState.id qi), []) ∧
            (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, LexingState.start) (map vocab.embed (ExtChar.char ws :: wt)) = some ((Unit.unit, LexingState.id qtarget), []) := by
  -- take
  intro qt hqt_nonwhite hqt_nstart
  simp[FSA.pruned] at hpruned
  obtain ⟨w, hw⟩ := (hpruned qt).right
  have : w ≠ [] := by
    intro h
    simp[h] at hw
    exact hqt_nstart hw
  let h := w.head this
  have hhtail : w = h :: w.tail := by simp[h]
  have ⟨step, hstep⟩ : ∃ q, spec.automaton.step spec.automaton.start h = some q := by
    rw[hhtail] at hw
    simp[FSA.evalFrom] at hw
    split at hw
    simp at hw
    rename_i s' heq
    exists s'

  exists h
  exists map ExtChar.char w.tail
  exists step
  constructor
  . intro ha
    rw[hhtail] at hw
    simp[FSA.evalFrom] at hw
    split at hw
    simp at hw
    rename_i heq
    simp[ha] at heq
    have ⟨_, hstay, _⟩ := hwa
    have hstay := hstay spec.automaton.start h
    simp[ha] at hstay
    rw[heq] at hstay
    simp at hstay
    simp[hstay] at hw
    have := qwhite_sink spec hwa qt (w.tail) hw.symm
    exact hqt_nonwhite this
  constructor
  exact hstep
  constructor
  . simp[detok_eval_embed, BuildLexingFST, Id.run, LexingState.src]
    simp[hstep]
  . rw[←List.map_cons, ←hhtail]
    generalize hqs : spec.automaton.start = qs at hw
    generalize hq's : LexingState.start = q's
    have hrel : LexingState.src spec q's = qs := by
      simp[LexingState.src, hqs]
      simp[←hq's]
    clear hqs hq's hstep
    induction w generalizing qs q's
    case nil => simp at hhtail
    case cons head tail ih =>
      simp[FSA.evalFrom] at hw
      simp at ih ⊢
      simp[FST.evalFrom]
      split at hw <;> try simp at hw
      simp[detok_eval_embed]
      simp[BuildLexingFST, Id.run]
      rename_i s heq
      simp[hrel, heq]
      by_cases h : tail = []
      simp[h] at hw ⊢
      exact hw.symm
      have ih' := ih h s hw (LexingState.id s) (by simp[LexingState.src])
      rw[ih']

-- extract the common proof that qp.2 = LexingState.id qwhite
omit [BEq V] in
private lemma exchange_basis_ends_at_qwhite [BEq (Ch Γ)] [LawfulBEq (Ch Γ)]  [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (_: (BuildDetokLexer (v := vocab) spec).stepList ((), q) (wpfx ++ [wlast]) = some (pfx ++ [last]))
  (hflat_pfx: flatMap produce pfx = [])
  (hlast: produce last = [ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)])
  (hflat: ∀ t ∈ wpfx ++ [wlast], ∃ t0, vocab.flatten t = [t0])
  (heval: (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) (wpfx ++ [wlast]) = some (last.2.2.1, [ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)]))
  (hqp: (BuildDetokLexer spec).evalFrom ((), q) wpfx = some ((unt, qp), flatMap (fun x => x.2.2.2) pfx)) : qp = LexingState.id qwhite := by
  simp[FSA.accepts_iff] at hempty
  unfold produce at hflat_pfx hlast
  simp[FST.evalFrom_append, hflat_pfx, hqp] at heval
  simp[BuildDetokLexer] at heval
  rw[detokenizer_comp_step] at heval
  obtain ⟨t, ht⟩ := hflat wlast (by simp)
  rw[ht] at heval
  simp[FST.evalFrom_singleton] at heval
  have ⟨unt, hunt⟩ := heval
  simp[BuildLexingFST, Id.run] at hunt
  split at hunt
  <;> split at hunt
  <;> try split at hunt
  all_goals (
    simp at hunt
  )
  obtain ⟨⟨a, ⟨_, _, hq⟩⟩, x⟩ := hunt
  obtain ⟨haccept, _⟩ := hwa
  simp[whitespace_terminal] at hq
  have hws := ((spec.hterm qwhite).mp haccept)
  rename_i haccept2 _ _ _
  have hqps := ((spec.hterm (LexingState.src spec qp)).mp haccept2)
  have := spec.term_inj (LexingState.src spec qp) qwhite ((spec.term qwhite).get hws)
  simp at this
  have hterm_eq : spec.term (LexingState.src spec qp) = spec.term qwhite := by
    simp[Option.isSome_iff_exists] at hws hqps
    obtain ⟨a, ha⟩ := hws
    obtain ⟨b, hb⟩ := hqps
    simp_rw[ha, hb] at hq
    simp at hq
    simp[ha, hb]
    exact hq
  simp[hterm_eq] at this
  unfold LexingState.src at this
  split at this <;> try simp[this]
  rw[←this] at haccept
  exact hempty haccept

-- if you can produce a single whitespace,
-- you can produce whitespace while ending up at any non whitespace state
--
-- most complicated of the exchange arguments
-- since white term is producible, we may find a path that goes to qwhite
-- traverse that path, then traverse the path to the qtarget (which must not start with qwhite)
-- these two together will produce the necessary construction
omit [BEq V] in
private lemma exchange_whitespacea [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { tnonwhite twhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned) (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (hwsa: ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa) ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    ∀ qtarget, qtarget ≠ qwhite → qtarget ≠ spec.automaton.start →
    ∃ w, (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, q) w = some ((Unit.unit, LexingState.id qtarget), [ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)]) := by
  let lexer := BuildDetokLexer (v := vocab) spec
  let white_term := whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa
  obtain ⟨wpfx, wlast, pfx, last, hprefix_list, hstep_list, hflat_pfx, hlast, heval, hflat⟩ := exchange_basis spec white_term q hwsa
  intro qtarget hqt_nonwhite hqt_nstart
  obtain ⟨ws, wt, step, hws_nwhite, hstep, hfst_step, hw⟩ := path_nonwhitespace (vocab := vocab) spec hpruned hwa qtarget hqt_nonwhite hqt_nstart
  let w := wpfx ++ ([vocab.embed ws] ++ (map vocab.embed wt))
  exists w
  simp[w, FST.evalFrom_append]
  rw[←map_cons]
  have := lexer.eval_of_stepList_opaque ((), q) wpfx
  simp[lexer, hprefix_list] at this
  obtain ⟨unt, qp, hqp⟩ := this
  simp[hqp]
  exists ()
  unfold produce at hflat_pfx
  simp[hflat_pfx]
  have hqp_white : qp = LexingState.id qwhite := by
    exact exchange_basis_ends_at_qwhite spec hempty hwa q hstep_list hflat_pfx hlast hflat heval hqp

  simp only [hqp_white]
  have : unt = () := by simp
  rw[this]
  simp[FST.evalFrom] at hw ⊢
  simp[detok_eval_embed]
  simp[BuildLexingFST, Id.run]
  obtain ⟨haccept, _, hwa, _⟩ := hwa
  have hwa := hwa ws (by intro ha; exact hws_nwhite ha.symm)
  simp[hwa, haccept]
  simp[whitespace_terminal]
  split at hw
  simp at hw
  rename_i heq
  simp[hstep]
  simp[hfst_step] at heq
  rw[heq.left]
  simp[heq] at hw
  split at hw
  simp at hw
  rename_i heq'
  simp[heq']
  simp at hw
  exact hw

-- if you can produce whitespace,
-- you can produce that and eos and end at qwhite
omit [BEq V] in
private lemma exchange_whitespace_eos [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { tnonwhite twhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (hwsa: ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa) ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    ∃ w, (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, q) w = some ((Unit.unit, LexingState.id qwhite), [ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa), ExtChar.eos]) := by
  let lexer := BuildDetokLexer (v := vocab) spec
  let white_term := whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa
  obtain ⟨wpfx, wlast, pfx, last, hprefix_list, hstep_list, hflat_pfx, hlast, heval, hflat⟩ := exchange_basis spec white_term q hwsa
  let w := wpfx ++ [vocab.embed .eos, vocab.embed twhite]
  exists w
  simp[w, FST.evalFrom_append]
  have := lexer.eval_of_stepList_opaque ((), q) wpfx
  simp[lexer, hprefix_list] at this
  obtain ⟨unt, qp, hqp⟩ := this
  unfold produce at hflat_pfx
  simp[hqp, hflat_pfx]
  have hqp_white : qp = LexingState.id qwhite := by
    exact exchange_basis_ends_at_qwhite spec hempty hwa q hstep_list hflat_pfx hlast hflat heval hqp

  simp[hqp_white, BuildDetokLexer, FST.evalFrom]
  rw[detokenizer_comp_step]
  simp[vocab.fe]
  simp[BuildLexingFST, Id.run]
  obtain ⟨haccept, hwa, _⟩ := hwa
  simp[haccept]
  rw[detokenizer_comp_step]
  simp[vocab.fe, LexingState.src, FST.evalFrom_singleton]
  have hwa := hwa spec.automaton.start twhite
  simp at hwa
  simp[hwa, whitespace_terminal]

-- if you can produce a single nonwhitespace,
-- you can produce that nonwhitespace while ending up at qwhite
omit [BEq V] in
private lemma exchange_nonwhitespace [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { tnonwhite twhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ) (term: Γ)
  (hterm: term ≠ (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa) ∧ ExtChar.char term ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    ∃ w, (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, q) w = some ((Unit.unit, LexingState.id qwhite), [ExtChar.char term]) := by
  simp[FSA.accepts_iff] at hempty
  let lexer := BuildDetokLexer (v := vocab) spec
  obtain ⟨wpfx, wlast, pfx, last, hprefix_list, hstep_list, hflat_pfx, hlast, heval, hflat⟩ := exchange_basis spec term q hterm.right
  let w := wpfx ++ [vocab.embed twhite]
  exists w
  simp[w, FST.evalFrom_append]
  have := lexer.eval_of_stepList_opaque ((), q) wpfx
  simp[lexer, hprefix_list] at this
  obtain ⟨unt, qp, hqp⟩ := this
  unfold produce at hflat_pfx
  simp[hflat_pfx] at hqp
  simp[hqp]
  -- since we produced term on the original branch
  -- old state must be that as well (in particular, not whitespace)
  have hqp_nwhite : (LexingState.src spec qp ≠ spec.automaton.start) ∧ qp ≠ LexingState.id qwhite ∧ spec.term (LexingState.src spec qp) = some term := by
    simp[FST.evalFrom_append, hqp] at heval
    simp[BuildDetokLexer] at heval
    rw[detokenizer_comp_step] at heval
    obtain ⟨t, ht⟩ := hflat wlast (by simp)
    rw[ht] at heval
    simp[FST.evalFrom_singleton] at heval
    obtain ⟨a, ha⟩ := heval
    simp[BuildLexingFST, Id.run] at ha
    split at ha
    <;> split at ha
    <;> try split at ha
    all_goals (
      simp at ha
    )
    obtain ⟨⟨q, hsteps, hqa, hspec⟩, g⟩ := ha
    rename_i hfailstep haccept
    constructor
    . intro ha
      rw[ha] at haccept
      exact hempty haccept
    have hspec' : spec.term (LexingState.src spec qp) = some term := by
      simp_rw[←hspec]
      simp
    constructor
    . intro ha
      rw[ha] at hspec'
      simp[whitespace_terminal] at hterm
      rw[←hspec] at hterm
      simp_rw[ha] at hterm
      simp[LexingState.src] at hterm
    . exact hspec'
  simp[BuildDetokLexer]
  rw[detokenizer_comp_step]
  simp[vocab.fe]
  simp[BuildLexingFST, Id.run]
  cases hstep : (spec.automaton.step (LexingState.src spec qp) twhite)
  simp
  obtain ⟨_, hwa, _⟩ := hwa
  have := hwa spec.automaton.start twhite
  simp at this
  simp[this]
  simp[hqp_nwhite]
  have := (spec.hterm (LexingState.src spec qp)).mpr (by simp[hqp_nwhite.right.right])
  exact this
  simp
  obtain ⟨haccept, _, _,  hwa, _⟩ := hwa
  have := hwa (LexingState.src spec qp)
  simp[hstep] at this
  simp[hqp_nwhite] at this
  unfold LexingState.src at this
  split at this
  rename_i a
  simp at hqp_nwhite hstep
  have := hwa a (by simp[hqp_nwhite])
  simp[this] at hstep
  rw[this] at hempty
  exact hempty haccept

-- if you can produce eos,
-- you can produce eos while ending up at qwhite
omit [BEq V] in
private lemma exchange_eos [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { tnonwhite twhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (hterm: ExtChar.eos ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    ∃ w, (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, q) w = some ((Unit.unit, LexingState.id qwhite), [ExtChar.eos]) := by
  -- exchange basis, can get it to something that has a steplist which is empty and then [target]
  -- and for non eos, that means it must
  let lexer := BuildDetokLexer (v := vocab) spec
  obtain ⟨wpfx, wlast, pfx, last, hprefix_list, hstep_list, hflat_pfx, hlast, heval, hflat⟩ := exchange_basis spec (ExtChar.eos) q hterm
  set w := wpfx ++ [wlast]
  exists w ++ [vocab.embed twhite]
  have := lexer.eval_of_stepList ((), q) w
  simp[lexer] at this
  -- show that last.2.2.1 = qstart since thats the only way to produce a single eos
  have hlast_start : last.2.2.1 = ((), LexingState.start) := by
    have := lexer.stepList_zip ((), q) w
    simp only [lexer, hstep_list] at this
    have := this last (by simp)
    simp at hlast
    have l : last.2.2 = (last.2.2.1, [ExtChar.eos]) := by simp[←hlast]
    rw[l] at this
    simp[BuildDetokLexer] at this
    rw[detokenizer_comp_step] at this
    simp[BuildLexingFST, Id.run] at this
    have hmw : last.2.1 ∈ w := by
      have := lexer.stepList_mem_w  (() , q) w
      rw[hstep_list] at this
      simp only [] at this
      exact this last (by simp)
    obtain ⟨t, ht⟩ := hflat last.2.1 hmw
    rw[ht] at this
    simp[FST.evalFrom_singleton] at this
    split at this
    <;> split at this
    <;> try split at this
    all_goals (
      obtain ⟨a, ha⟩ := this
      simp at ha
    )
    simp[ha]
  simp[FST.evalFrom_append, heval]
  simp[BuildDetokLexer]
  rw[detokenizer_comp_step]
  simp[vocab.fe]
  simp[hlast_start, BuildLexingFST, Id.run]
  obtain ⟨_, hwa, _⟩ := hwa
  have := hwa spec.automaton.start twhite
  simp at this
  simp[LexingState.src, this]

omit [BEq V] in
private lemma qwhite_prod_white [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { tnonwhite twhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
   (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) :
    ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa) ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, LexingState.id qwhite) := by
  simp[FST.singleProducible]
  exists [vocab.embed tnonwhite]
  simp[BuildDetokLexer, detokenizer_comp_step]
  simp[BuildLexingFST, Id.run, vocab.fe]
  obtain ⟨hqwhite, _, h, _, hqnwhite, hqnwhite_t, hdiff⟩ := hwa
  have := h tnonwhite hdiff.symm
  simp[this]
  constructor
  exists qnonwhite
  exists hqwhite

omit [BEq V] in
lemma detok_ws_rs_pfx [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { twhite tnonwhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned)
  (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (hwsa: ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa) ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    let white_term := (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)
    { Ts | ¬Ts.contains (ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)) } =
    (BuildDetokLexer (v := vocab) spec).moddedRealizableSequences (Unit.unit, q) white_term := by
  intro white_term
  ext x
  rw[Set.mem_setOf]

  apply Iff.intro
  . simp[FST.moddedRealizableSequences]
    intro h
    induction x generalizing q
    case nil =>
      exists []
      simp[FST.realizableSequences]
      rw[Set.mem_setOf]
      exists ()
      exists q
      exists []
    case cons head tail ih =>
      have hwsa_o := hwsa
      simp[FST.singleProducible] at h hwsa
      have ⟨fatwstart, _, q', hq'⟩ := hwsa
      simp[BuildDetokLexer] at hq'
      cases hhead : head
      case char ch =>
        -- first build the sequence that produces just whitespace
        -- then build the actual target
        -- then append a whitespace
        -- then build the tail
        have ⟨qtarget, hqtarget⟩ := spec.term_surj ch
        have hqtarget_accept : qtarget ∈ spec.automaton.accept := by
          simp[spec.hterm, hqtarget]
        have hnestart : qtarget ≠ spec.automaton.start := by
          intro ha
          rw[ha] at hqtarget
          have : spec.automaton.start ∈ spec.automaton.accept := by
            simp[spec.hterm, hqtarget]
          simp[FSA.accepts_iff] at hempty
          exact hempty this
        have hne_qwhite : qtarget ≠ qwhite := by
          intro ha
          simp[ha] at hqtarget
          simp[whitespace_terminal, hqtarget] at h
          exact h.left hhead.symm
        obtain ⟨wbase, hwbase⟩ := exchange_whitespace (vocab := vocab) spec hempty hpruned hwa q hwsa_o qtarget hne_qwhite hnestart
        let wfull := wbase ++ [vocab.embed twhite]
        have ⟨tail_seq, htail_seq⟩ := ih (LexingState.id qwhite) (qwhite_prod_white (vocab := vocab) spec hwa) h.right
        exists [ExtChar.char white_term, head] ++ tail_seq
        constructor
        simp[FST.realizableSequences] at htail_seq ⊢
        rw[Set.mem_setOf] at htail_seq ⊢
        exists Unit.unit
        obtain ⟨_, qf, ⟨wtail, hwqf⟩⟩ := htail_seq.left
        exists qf
        exists wfull ++ wtail
        simp[wfull, FST.evalFrom_append]
        simp[hwbase, white_term, FST.evalFrom]
        nth_rewrite 1 [BuildDetokLexer]
        simp[detokenizer_comp_step, vocab.fe, BuildLexingFST, Id.run]
        have : spec.automaton.step qtarget twhite = none := by
          obtain ⟨_, _, _, target, _⟩ := hwa
          have := target qtarget
          simp[hne_qwhite, hnestart] at this
          exact this
        simp[this, hqtarget_accept, hqtarget]
        obtain ⟨_, target, _⟩ := hwa
        have := target spec.automaton.start twhite
        simp at this
        simp[this, hwqf, hhead]
        simp[white_term, filter_cons, htail_seq]
        simp[hhead] at h ⊢
        rw[eq_comm]
        exact h.left
      case eos =>
        obtain ⟨wbase, hwbase⟩ := exchange_whitespace_eos (vocab := vocab) spec hempty hwa q hwsa_o
        have ⟨tail_seq, htail_seq⟩ := ih (LexingState.id qwhite) (qwhite_prod_white (vocab := vocab) spec hwa) h.right
        exists [ExtChar.char white_term, ExtChar.eos] ++ tail_seq
        constructor
        simp[FST.realizableSequences] at htail_seq ⊢
        rw[Set.mem_setOf] at htail_seq ⊢
        exists Unit.unit
        obtain ⟨_, qf, ⟨wtail, hwqf⟩⟩ := htail_seq.left
        exists qf
        exists wbase ++ wtail
        simp[FST.evalFrom_append, hwbase]
        simp[white_term]
        constructor
        exact hwqf
        simp[htail_seq]
  . intro h
    simp[FST.moddedRealizableSequences] at h
    have ⟨v, hv⟩ := h
    simp[white_term] at hv
    rw[←hv.right]
    simp

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
private lemma detok_rs_pfx_forward [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { tnonwhite twhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts)
  (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ) :
  let white_term := (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)
  let lexer := BuildDetokLexer (v := vocab) spec
  ∀ x ∈ lexer.tailModdedRealizableSequences (Unit.unit, q) white_term,
    x ∈ { Ts | Ts = [] ∨
           (∃ t tsfx,
             ¬Ts.contains (ExtChar.char white_term) ∧
             Ts = t :: tsfx ∧ t ∈ lexer.singleProducible (Unit.unit, q)) } := by
  -- forward:
    -- effectively just need to show that it must start with a single producible token
    -- via assumption of singletons
    -- otherwise, the fact that tsfx can be anything means that we are done
  intro white_term lexer x h
  have hlexer : lexer = (BuildDetokenizingFST.compose (BuildLexingFST spec)) := by
    simp[BuildDetokLexer, lexer]
  by_cases he : x = []
  . simp[he]
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
      rw[←h_step_list.right.left]
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
      Eq.symm (flatMap_prefix_suffix step_list firstTransitionIdx v h_step_list.right.left)

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

      have := lexer.eval_of_stepList_opaque ((), q) wfinal
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
      have := lexer.eval_of_stepList_opaque ((), q) (ws.take firstTransitionIdx)
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
      obtain ⟨_, hstart_good, _, hnonqhite_fail, _⟩ := hwa
      have : spec.automaton.step (LexingState.src spec emptyq') twhite = none := by
        exact hnonqhite_fail (LexingState.src spec emptyq') (by simp[hnstart, hnqwhite])
      simp[this]
      constructor
      exists qwhite
      have := hstart_good spec.automaton.start twhite
      simp at this
      assumption
      exact h_first_eq_prod

omit [BEq V] in
private lemma detok_rs_pfx_backward [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { twhite tnonwhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned)
  (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ) :
  let white_term := (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)
  let lexer := BuildDetokLexer (v := vocab) spec
  ∀ x, x ∈ { Ts | Ts = [] ∨
           (∃ t tsfx,
             ¬Ts.contains (ExtChar.char white_term) ∧
             Ts = t :: tsfx ∧ t ∈ lexer.singleProducible (Unit.unit, q)) } →
       x ∈ lexer.tailModdedRealizableSequences (Unit.unit, q) white_term := by
  intro white_term lexer x h
  have hlexer : lexer = (BuildDetokenizingFST.compose (BuildLexingFST spec)) := by
    simp[BuildDetokLexer, lexer]
  rw[Set.mem_setOf] at h
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
    have ⟨w, hw⟩ := h_singleton
    simp[white_term, h_eq] at h_no_white
    -- our sequence will be to compute the first one as is
    -- and then do whitespace, and then do whatever else via previous lemma
    obtain ⟨w', hw'⟩ : ∃ w', (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) w' = some (((), LexingState.id qwhite), [t]) := by
      cases ht : t
      case char ch =>
        obtain ⟨w', hw'⟩ := exchange_nonwhitespace (vocab := vocab) spec hempty hwa q ch (by
          simp[ht] at h_no_white
          rw[eq_comm] at h_no_white
          simp
          constructor
          exact h_no_white.left
          simp[←ht]
          exact h_singleton
        )
        exists w'
      case eos =>
        obtain ⟨w', hw'⟩ := exchange_eos (vocab := vocab) spec hwa q (by simp[h_singleton, lexer, ←ht])
        exists w'
    simp[FST.tailModdedRealizableSequences]
    rw[Set.mem_setOf]
    -- build rest of tail via previous lemma
    have htail := detok_ws_rs_pfx spec hempty hpruned hwa (LexingState.id qwhite) (qwhite_prod_white (vocab := vocab) spec hwa)
    have htsfx : tsfx ∈ (BuildDetokLexer spec (v := vocab)).moddedRealizableSequences ((), LexingState.id qwhite) (ExtChar.char white_term) := by
      rw[←htail]
      rw[Set.mem_setOf]
      simp
      exact h_no_white.right
    simp[FST.moddedRealizableSequences] at htsfx
    rw[Set.mem_setOf] at htsfx
    obtain ⟨v, hv⟩ := htsfx
    exists t :: v
    simp[FST.realizableSequences]
    rw[Set.mem_setOf]
    simp[white_term]
    constructor
    . exists Unit.unit
      simp[FST.realizableSequences] at hv
      rw[Set.mem_setOf] at hv
      obtain ⟨_, qf, wfinal, hwfinal⟩ := hv.left
      exists qf
      exists w' ++ wfinal
      simp[FST.evalFrom_append, lexer, hw']
      simp[hwfinal]
    . constructor
      exact h_no_white.left
      simp[filter_cons]
      have : (t != ExtChar.char (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)) = true := by
        simp
        rw[eq_comm] at h_no_white
        exact h_no_white.left
      simp[this, h_eq]
      simp[white_term] at hv
      exact hv.right

omit [BEq V] in
lemma detok_rs_pfx [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] { twhite tnonwhite qnonwhite qwhite } [vocab: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned)
  (hwa: whitespace_assumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ) :
  let white_term := (whitespace_terminal spec tnonwhite twhite qnonwhite qwhite hwa)
  let lexer := BuildDetokLexer (v := vocab) spec
  lexer.tailModdedRealizableSequences (Unit.unit, q) white_term =
    { Ts | Ts = [] ∨
           (∃ t tsfx,
             ¬Ts.contains (ExtChar.char white_term) ∧
             Ts = t :: tsfx ∧ t ∈ lexer.singleProducible (Unit.unit, q)) } := by
  ext x
  apply Iff.intro
  . intro h
    exact detok_rs_pfx_forward spec hempty hwa q x h
  . intro h
    exact detok_rs_pfx_backward spec hempty hpruned hwa q x h

end Detokenizing
