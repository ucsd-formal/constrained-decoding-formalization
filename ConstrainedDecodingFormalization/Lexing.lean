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
lemma LexingState_src_id {σ : Type w} (spec: LexerSpec α Γ σ) (s : σ) :
  LexingState.src spec (LexingState.id s) = s := by
  simp[LexingState.src]

/-- Given a lexing automaton `A`, build a character-to-token lexing FST with output over `Γ`
    For the lexing FSA, we'll use the convention that each terminal symbol is attached to an accept state (see Fig. 1) -/
def BuildLexingFST (spec: LexerSpec α Γ σ) :
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
    case step_nil_eos w wn tokens ih wwn h hacc =>
      simp[PartialLex, PartialLex_seed, PartialLex_trans] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      exact h
    case step_eos w wn tokens unlexed ih wwn h hacc =>
      simp[PartialLex, PartialLex_seed, PartialLex_trans] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      simp[h]
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
    case step_char_commit w wn tokens unlexed ch ih wwn hni hc_pfx ht hacc =>
      simp[PartialLex, PartialLex_seed, PartialLex_trans] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      cases he: spec.automaton.eval (unlexed ++ [ch]) with
      | none =>
        simp[FSA.eval] at he
        simp[he]
        simp[LexerSpec.accept_seq_term, FSA.accepts, FSA.acceptsFrom] at ht
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
        simp[heq', LexerSpec.accept_seq_term, FSA.accepts, FSA.acceptsFrom]
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
              simp_all[hp, ha]
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
                  simp[PartialLex_seed]
                  exact hpfx
                  simp[PartialLex_seed, new_tokens, new_unlexed, hns]
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
    simp[FST.eval, FST.evalFrom] at h
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
      . simp[hempty, h₃]
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

    simp[FST.eval, FST.eval_fold, FST.evalFrom_fold, FST.evalFrom_fold_seed]
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
          simp[FST.evalFrom, FST.eval] at h₁ ⊢
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
            simp[FST.evalFrom, FST.eval] at h₁ ⊢
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
            simp[FST.evalFrom, FST.eval] at h₁ ⊢
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

          simp[hq', haccept, h₂_fsa, hlex_step]
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
              simp[h₂_fsa, hh, hstep, haccept]
              simp[FSA.evalFrom, hstep]
              simp[hch]
            simp[this]
            have : ((BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch)) = none := by
              simp[BuildLexingFST, Id.run, FST.evalFrom_fold_step]
              simp[hh, hch, hstep, haccept]
            simp[this]
          case some qnext =>
            have hplex_step : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = some (seed_ts ++ [ExtChar.char unwrapped], [ch]) := by
              simp[PartialLex_trans, hh]
              simp[FSA.evalFrom_append]
              simp[h₂_fsa, hh, haccept]
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
              simp[h₂_fsa, hstep, haccept]
              simp[hch, unwrapped, term, qsrc]

            have hlex_wp_trans : (BuildLexingFST spec).eval (wp ++ [head]) = some (LexingState.id qnext, seed_ts ++ [ExtChar.char unwrapped]) := by
              simp[FST.evalFrom, FST.eval] at h₁ ⊢
              rw[←FST.evalFrom_fold_eq_evalFrom] at h₁ ⊢
              simp[FST.evalFrom_fold, FST.evalFrom_fold_seed] at h₁ ⊢
              rw[h₁]
              simp[hh]
              exact hlex_wp_step

            have lex_wr_step : (BuildLexingFST spec).eval [ch] = some (LexingState.id qnext, []) := by
              simp[BuildLexingFST, Id.run, FST.eval, FST.evalFrom]
              simp[LexingState.src, hch]

            have ih := ih (wp ++ [head]) (LexingState.id qnext) (seed_ts ++ [ExtChar.char unwrapped]) [ch] hplex_trans hlex_wp_trans lex_wr_step (by simp[hh])
            rw[hplex_step]
            rw[hlex_wp_step]
            unfold FST.evalFrom_fold_seed at ih
            exact ih
        case neg =>
          have : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = none := by
            simp[PartialLex_trans, hh]
            simp[FSA.evalFrom_append]
            simp[h₂_fsa, FSA.evalFrom, hstep, haccept]
          simp[this]
          have : ((BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch)) = none := by
            simp[BuildLexingFST, Id.run, FST.evalFrom_fold_step]
            simp[hh, hstep, haccept]
          simp[this]
      case some dst =>
        -- both will effectively take the transition specified by automata
        have hplex_step : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = some (seed_ts, seed_wr ++ [ch]) := by
          simp[PartialLex_trans, hh]
          simp[FSA.evalFrom_append]
          simp[h₂_fsa, hh]
          simp[FSA.evalFrom, hstep]

        have hplex_trans : PartialLex spec (wp ++ [head]) = some (seed_ts, seed_wr ++ [ch]) := by
          simp[PartialLex_seed] at h₀ ⊢
          rw[h₀]
          simp[hh]
          exact hplex_step

        have hlex_wp_step : (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch) = some (LexingState.id dst, seed_ts) := by
          simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
          simp[h₂_fsa, hstep]

        have hlex_wp_trans : (BuildLexingFST spec).eval (wp ++ [head]) = some (LexingState.id dst, seed_ts) := by
          simp[FST.evalFrom, FST.eval] at h₁ ⊢
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

        have ih := ih (wp ++ [head]) (LexingState.id dst) seed_ts (seed_wr ++ [ch]) hplex_trans hlex_wp_trans lex_wr_step (by simp[hh])
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
  simp[PartialLex, fst] at this ⊢
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
