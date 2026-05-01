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
import ConstrainedDecodingFormalization.Producible
import ConstrainedDecodingFormalization.Char
import ConstrainedDecodingFormalization.Vocabulary

/-!
# Lexing transducers

This file connects deterministic character-level lexing with the finite-state
transducer model used by the rest of the development.

Its main ingredients are:

* `LexerSpec`, which packages a character automaton together with token labels
  on accepting states;
* `PartialLexRel` and `PartialLex`, relational and executable formulations of
  incremental lexing;
* `BuildLexingFST`, which turns a lexer specification into an FST over
  EOS-extended characters;
* the `Detokenizing` namespace, which lifts token vocabularies into FSTs and
  composes them with lexers.
-/

open List

universe u v w

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ]
  [BEq α] [BEq σ] [LawfulBEq σ]

/-! ### Lexer specification -/

/-- A lexer specification given by a character automaton together with token
labels on accepting states.

This is the interface from which the lexing FST and the grammar-constrained
decoding checker are built.
-/
structure LexerSpec (α Γ σ) where
  automaton : FSA α σ
  term: σ → Option Γ
  hterm: ∀ s, s ∈ automaton.accept ↔ (term s).isSome
  term_inj: ∀ s₁ s₂ t, term s₁ = some t ∧ term s₂ = some t → s₁ = s₂
  term_surj: ∀ t, ∃ s, term s = some t

/-- Evaluate a character sequence and, if it is accepted, return the token
attached to its accepting state. -/
def LexerSpec.seq_term (spec: LexerSpec α Γ σ) (seq: List α) : Option Γ :=
  match spec.automaton.eval seq with
  | some s => spec.term s
  | none => none

/-- Extract the token attached to an accepted character sequence. -/
def LexerSpec.accept_seq_term (spec: LexerSpec α Γ σ) (seq: List α) (h: seq ∈ spec.automaton.accepts) : Γ :=
  let s := (spec.automaton.eval seq).get <| by
    simp[FSA.accepts, FSA.acceptsFrom] at h
    have mem_set := Set.mem_setOf.mp h
    rcases mem_set with ⟨e, he, he1⟩
    simp_all only [FSA.eval, Option.isSome_some]
  have sa : s ∈ spec.automaton.accept := by
    simp[FSA.accepts, FSA.acceptsFrom] at h
    have mem_set := Set.mem_setOf.mp h
    rcases mem_set with ⟨e, he, he1⟩
    simp_all only [FSA.eval, Option.get_some, s]
  let term := spec.term s
  term.get ((spec.hterm s).mp sa)

/-- An executable lexer from EOS-extended characters to EOS-extended tokens,
also returning the residual unlexed suffix of the current token candidate. -/
def Lexer (α : Type u) (Γ : Type v) := List (Ch α) -> Option (List (Ch Γ) × List α)

/-! ### Relational and executable lexing -/

/-- Relational semantics of incremental lexing.

`PartialLexRel spec w tokens unlexed` means that after reading `w`, the lexer
has committed `tokens` and retained `unlexed` as the unfinished suffix of the
current token candidate.
-/
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

/-- One-step transition of the executable lexer.

Decides, given a partial token `unlexed` and the next EOS-extended character,
whether to commit the current token, continue extending it, or report failure. -/
private def PartialLex_trans (spec: LexerSpec α Γ σ) (prev: Option (List (Ch Γ) × List α)) (c : Ch α)
  : Option (List (Ch Γ) × List α) :=
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
  foldl (PartialLex_trans spec) none ws = none :=
  foldl_fixed' (congrFun rfl) ws

@[simp]
private def PartialLex_seed (spec: LexerSpec α Γ σ) (seed: Option (List (Ch Γ) × List α)) : Lexer α Γ :=
  fun w => List.foldl (PartialLex_trans spec) seed w

@[simp]
def PartialLex (spec: LexerSpec α Γ σ) : Lexer α Γ :=
  PartialLex_seed spec (some ([], []))

/-! ### Lexing FST construction -/

/-- States of the lexing FST: either the distinguished start state or a state
tracking an underlying lexer-automaton state. -/
inductive LexingState (σ : Type w) where
| id : σ → LexingState σ
| start : LexingState σ
deriving DecidableEq, Repr

instance {σ} [e : FinEnum σ] : FinEnum (LexingState σ) where
  card := FinEnum.card σ + 1
  equiv :=
    let e := e.equiv
    { toFun := fun x =>
        match x with
        | LexingState.start => ⟨FinEnum.card σ, Nat.lt_succ_self _⟩
        | LexingState.id s => ⟨e s, Nat.lt_succ_of_lt (Fin.is_lt (e s))⟩
      invFun := fun i =>
        if h : i.val < FinEnum.card σ then LexingState.id (e.symm ⟨i.val, h⟩)
        else LexingState.start
      left_inv := by
        intro x
        cases x with
        | start =>
          simp
        | id s =>
          simp
      right_inv := by
        intro ⟨i, hi⟩
        by_cases h : i < FinEnum.card σ
        · simp [h]
        · have : i = FinEnum.card σ := by
            linarith
          subst this
          simp
      }
  decEq := by infer_instance

/-- Recover the underlying lexer-automaton state represented by a lexing-FST
state. -/
def LexingState.src {σ : Type w} (spec: LexerSpec α Γ σ) : LexingState σ → σ
| LexingState.id s => s
| LexingState.start => spec.automaton.start

@[simp]
def LexingState_src_id [DecidableEq α] [BEq α] {σ : Type w} (spec: LexerSpec α Γ σ) (s : σ) :
  LexingState.src spec (LexingState.id s) = s := by
  simp[LexingState.src]


/-- Build the character-to-token lexing FST associated to a lexer
specification.

The construction follows the convention that tokens are attached to accepting
states of the lexer automaton. This is the central machine-level object that is
later composed with detokenization and parser preprocessing.
-/
def BuildLexingFST [BEq α] [DecidableEq α] (spec: LexerSpec α Γ σ)
  : FST (Ch α) (Ch Γ) (LexingState σ) := Id.run do
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

omit [DecidableEq α] [DecidableEq σ] [BEq α] [BEq σ] [LawfulBEq σ] in
/-- Under pruning, the seeded executable lexer and the relational semantics are
equivalent in both directions. This is the technical core behind the later
equivalence theorems. -/
private lemma PartialLexRel_append_singleton_tail (spec: LexerSpec α Γ σ)
    {tail wp : List (Ch α)} {c : Ch α}
    {tokens : List (Ch Γ)} {unlexed : List α}
    (h : PartialLexRel spec ((wp ++ [c]) ++ tail) tokens unlexed) :
    PartialLexRel spec (wp ++ c :: tail) tokens unlexed := by
  simpa using h

omit [DecidableEq α] [DecidableEq σ] [BEq α] in
lemma PartialLex_pruned_eq_PartialLexRel_seed (spec: LexerSpec α Γ σ) (hp: spec.automaton.pruned) :
  (∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) →
    PartialLex_seed spec (some ([], [])) w = some (tokens, unlexed)) ∧
  (∀ wp ws seed_f seed_s tokens unlexed,
    (PartialLexRel spec wp seed_f seed_s) ∧
      PartialLex_seed spec (some (seed_f, seed_s)) ws = some (tokens, unlexed) →
    PartialLexRel spec (wp ++ ws) tokens unlexed) := by
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
        rcases ht with ⟨t, ht, ht1⟩
        subst wwn
        simp_all only [reduceCtorEq]
        have ⟨e, he'⟩ := ht
        rename_i σ' _ heq
        simp[he'] at heq
        constructor
        · rw[←hprune] at hc_pfx
          simp[FSA.intermediateLanguage] at hc_pfx
          change spec.automaton.evalFrom spec.automaton.start [ch] ≠ none at hc_pfx
          cases hch : spec.automaton.evalFrom spec.automaton.start [ch] with
          | none =>
              contradiction
          | some qch =>
              simp
        · refine ⟨heq ▸ he'.2, ?_⟩
          subst heq
          have his : (spec.term e).isSome := (spec.hterm e).mp he'.2
          rcases Option.isSome_iff_exists.mp his with ⟨t, hterm⟩
          have hs :
              (spec.automaton.eval unlexed).get
                (by simp [FSA.eval, he'.1]) = e := by
            simp [FSA.eval, he'.1]
          unfold LexerSpec.accept_seq_term
          simp [FSA.eval, he'.1, hterm]
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
          exact PartialLex_trans_foldl_nil spec tail
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
            have htail : PartialLex_seed spec (some (new_tokens, [])) tail = some (tokens, unlexed) := by
              simp[PartialLex_seed]
              simp[haccept] at hns
              have := h_token_unlexed
              simp[←hns.left, ←hns.right, new_tokens] at h_token_unlexed ⊢
              exact h_token_unlexed
            exact PartialLexRel_append_singleton_tail spec (ih (wp ++ [ExtChar.eos]) new_tokens [] ⟨step, htail⟩)
          . simp[haccept] at hns
            let new_tokens := seed_f ++ [.eos]
            simp[hns.left] at my_inductive_seed
            simp[hns] at haccept
            have step := PartialLexRel.step_nil_eos my_inductive_seed rfl haccept
            have htail : PartialLex_seed spec (some (new_tokens, [])) tail = some (tokens, unlexed) := by
              simp[PartialLex_seed]
              have := h_token_unlexed
              simp[←hns.right, new_tokens] at h_token_unlexed ⊢
              exact h_token_unlexed
            exact PartialLexRel_append_singleton_tail spec (ih (wp ++ [ExtChar.eos]) new_tokens [] ⟨step, htail⟩)
        | ExtChar.char ch =>
          simp[PartialLex_trans] at hns
          cases hp : spec.automaton.evalFrom spec.automaton.start (seed_s ++ [ch]) with
          | some σ' =>
            simp[hp] at hns
            let new_tokens := seed_f
            let new_unlexed := seed_s ++ [ch]

            have hint : (seed_s ++ [ch] ∈ spec.automaton.intermediateLanguage) := by
              change spec.automaton.evalFrom spec.automaton.start (seed_s ++ [ch]) ≠ none
              simp [hp]
            have hpfx : (seed_s ++ [ch] ∈ spec.automaton.prefixLanguage) := by
              rw[←hprune]
              exact hint
            have hstep_rel : PartialLexRel spec (wp ++ [ExtChar.char ch]) new_tokens new_unlexed :=
              PartialLexRel.step_char_continue my_inductive_seed rfl hpfx
            have htail : PartialLex_seed spec (some (new_tokens, new_unlexed)) tail = some (tokens, unlexed) := by
              simp[PartialLex_seed]
              simp[new_tokens, new_unlexed, hns]
              exact h_token_unlexed
            exact PartialLexRel_append_singleton_tail spec (ih (wp ++ [ExtChar.char ch]) new_tokens new_unlexed ⟨hstep_rel, htail⟩)
          | none =>
            cases ha : spec.automaton.evalFrom spec.automaton.start seed_s with
            | none => simp[hp, ha] at hns
            | some σ =>
              simp_all
              cases hbo : spec.automaton.eval [ch]
              . simp at hbo
                simp[hbo] at hns
              . have hint : (seed_s ++ [ch] ∉ spec.automaton.intermediateLanguage) := by
                  change ¬ spec.automaton.evalFrom spec.automaton.start (seed_s ++ [ch]) ≠ none
                  simp[←hns.right.right] at hp
                  simp [hp]
                have hpfx : (seed_s ++ [ch] ∉ spec.automaton.prefixLanguage) := by
                  rw[←hprune]
                  exact hint

                have haccept : (seed_s ∈ spec.automaton.accepts) := by
                  have ⟨⟨h, _⟩, ht⟩ := hns.right
                  change ∃ f, spec.automaton.evalFrom spec.automaton.start seed_s = some f ∧ f ∈ spec.automaton.accept
                  exact ⟨σ, ha, h⟩

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

                have hstep_rel : PartialLexRel spec (wp ++ [ExtChar.char ch]) new_tokens new_unlexed := by
                  have ⟨⟨_, hseed⟩, ht'⟩ := hns.right
                  apply PartialLexRel.step_char_commit h.left
                  simp
                  exact hpfx
                  simp[hns]
                  simp_all
                  simp[term] at ht
                  simp[ht] at hseed
                  rw[←hprune]
                  change spec.automaton.evalFrom spec.automaton.start step_unlexed ≠ none
                  rw[hbo]
                  simp
                have htail : PartialLex_seed spec (some (new_tokens, new_unlexed)) tail = some (tokens, unlexed) := by
                  have ⟨⟨_, hseed⟩, ht'⟩ := hns.right
                  simp[new_tokens, new_unlexed, ←ht', ←hseed, ←htused, ht, term] at h_token_unlexed ⊢
                  exact h_token_unlexed
                exact PartialLexRel_append_singleton_tail spec (ih (wp ++ [ExtChar.char ch]) new_tokens new_unlexed hstep_rel htail)

/-! ### Equivalence of relational and executable lexing -/

omit [DecidableEq α] [DecidableEq σ] [BEq α] in
/-- Pruning lets us identify `PartialLex` with the relational lexer semantics. -/
theorem PartialLex_pruned_eq_PartialLexRel (spec: LexerSpec α Γ σ) (hp: spec.automaton.pruned) :
  ∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) ↔
    PartialLex spec w = some (tokens, unlexed) := by
  intro w tokens unlexed
  apply Iff.intro
  . exact (PartialLex_pruned_eq_PartialLexRel_seed spec hp).left w tokens unlexed
  . intro h
    have : PartialLexRel spec ([] ++ w) tokens unlexed := by
      apply (PartialLex_pruned_eq_PartialLexRel_seed spec hp).right [] w
      exact ⟨PartialLexRel.nil, by simp[PartialLex] at h; exact h⟩
    simp at this
    exact this

/-! ### Lexing FST correctness -/

/-- A character-level FSA run lifts to a lexing-FST run that produces no
output tokens. -/
private def FSA_ch_to_LexingFST (spec: LexerSpec α Γ σ) :
  ∀ (w : List α) q q', (q ≠ LexingState.start ∨ w ≠ []) →
    (spec.automaton.evalFrom (q.src spec) w = some q' ↔
      (BuildLexingFST spec).evalFrom q w = some (LexingState.id q', [])) := by
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

omit [DecidableEq α] [DecidableEq σ] [BEq α] in
private lemma PartialLex_append_singleton_of_trans (spec: LexerSpec α Γ σ)
    {w : List (Ch α)} {head : Ch α}
    {seed_ts ts : List (Ch Γ)} {seed_wr wr : List α}
    (hw : PartialLex spec w = some (seed_ts, seed_wr))
    (hstep : PartialLex_trans spec (some (seed_ts, seed_wr)) head = some (ts, wr)) :
    PartialLex spec (w ++ [head]) = some (ts, wr) := by
  simp [PartialLex, PartialLex_seed] at hw ⊢
  rw [hw]
  simpa using hstep

omit [DecidableEq α] [DecidableEq σ] [BEq α] [BEq σ] [LawfulBEq σ] in
private lemma FST_eval_append_singleton_of_evalFrom_fold_step (M : FST α Γ σ)
    {w : List α} {head : α} {q q' : σ} {ts ts' : List Γ}
    (hw : M.eval w = some (q, ts))
    (hstep : M.evalFrom_fold_step (some (q, ts)) head = some (q', ts')) :
    M.eval (w ++ [head]) = some (q', ts') := by
  simp [FST.eval] at hw ⊢
  rw [←FST.evalFrom_fold_eq_evalFrom] at hw ⊢
  simp [FST.evalFrom_fold, FST.evalFrom_fold_seed] at hw ⊢
  rw [hw]
  simpa using hstep

private def PartialLex_to_LexingFST_evalFold (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) :
  ∀ wp ws q' seed_ts seed_wr,
    PartialLex spec wp = some (seed_ts, seed_wr) →
    (BuildLexingFST spec).eval wp = some (q', seed_ts) →
    (BuildLexingFST spec).eval seed_wr = some (q', []) →
    (seed_wr = [] ↔ q' = LexingState.start) →
    match PartialLex_seed spec (some (seed_ts, seed_wr)) ws with
    | some (ts, wr) =>
      ∃ q'',
        (BuildLexingFST spec).evalFrom_fold_seed q' ws seed_ts = some (q'', ts) ∧
        (BuildLexingFST spec).evalFrom_fold_seed (BuildLexingFST spec).start wr [] = some (q'', [])
    | none => (BuildLexingFST spec).evalFrom_fold_seed q' ws seed_ts = none := by
  intro wp ws q' seed_ts seed_wr
  let fst := BuildLexingFST spec
  let new_q0 := fst.start
  let old_q0 := spec.automaton.start

  have hlex_nil : fst.eval [] = some (new_q0, []) := by
    simp [fst, new_q0, BuildLexingFST, Id.run, FST.eval, FST.evalFrom]

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
    have hplex_append :
        ∀ {ts wr}, PartialLex_trans spec (some (seed_ts, seed_wr)) head = some (ts, wr) →
          PartialLex spec (wp ++ [head]) = some (ts, wr) := by
      intro ts wr hstep
      exact PartialLex_append_singleton_of_trans spec h₀ hstep

    have hlex_append :
        ∀ {q'' ts''}, fst.evalFrom_fold_step (some (q', seed_ts)) head = some (q'', ts'') →
          fst.eval (wp ++ [head]) = some (q'', ts'') := by
      intro q'' ts'' hstep
      exact FST_eval_append_singleton_of_evalFrom_fold_step fst h₁ hstep

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

        have hlex_wp_step : fst.eval (wp ++ [head]) = some (LexingState.start, seed_ts ++ [.char produced_token, ExtChar.eos]) :=
          hlex_append hlex_trans

        have hplex_step : PartialLex spec (wp ++ [head]) = some (seed_ts ++ [.char produced_token, ExtChar.eos], []) :=
          hplex_append (by
            simp [PartialLex_trans, hh, produced_token, haccept])

        have ih := ih (wp ++ [head]) LexingState.start (seed_ts ++ [.char produced_token, ExtChar.eos]) [] hplex_step hlex_wp_step hlex_nil

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

          have hlex_wp_step : fst.eval (wp ++ [head]) = some (LexingState.start, seed_ts ++ [ExtChar.eos]) :=
            hlex_append hlex_trans

          have hplex_step : PartialLex spec (wp ++ [head]) = some (seed_ts ++ [ExtChar.eos], []) :=
            hplex_append (by
              simp [PartialLex_trans, hh, hempty]
              exact he)

          have ih := ih (wp ++ [head]) LexingState.start (seed_ts ++ [ExtChar.eos]) [] hplex_step hlex_wp_step hlex_nil

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
              simpa [hh] using (PartialLex_append_singleton_of_trans spec h₀ hplex_step)

            have hlex_wp_step : (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch) = some (LexingState.id qnext, seed_ts ++ [ExtChar.char unwrapped]) := by
              simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
              simp[hstep, haccept]
              simp[hch, unwrapped, term, qsrc]

            have hlex_wp_trans : fst.eval (wp ++ [head]) = some (LexingState.id qnext, seed_ts ++ [ExtChar.char unwrapped]) := by
              simpa [fst, hh] using (FST_eval_append_singleton_of_evalFrom_fold_step fst h₁ hlex_wp_step)

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
          simpa [hh] using (PartialLex_append_singleton_of_trans spec h₀ hplex_step)

        have hlex_wp_step : (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch) = some (LexingState.id dst, seed_ts) := by
          simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
          simp[hstep]

        have hlex_wp_trans : fst.eval (wp ++ [head]) = some (LexingState.id dst, seed_ts) := by
          simpa [fst, hh] using (FST_eval_append_singleton_of_evalFrom_fold_step fst h₁ hlex_wp_step)

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

/-- The executable lexer and the lexing FST agree on successful executions. -/
theorem PartialLex_to_LexingFST (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) :
  ∀ w, match PartialLex spec w with
    | some (ts', wr) =>
      ∃ q', (BuildLexingFST spec).eval w = some (q', ts') ∧
        (BuildLexingFST spec).eval wr = some (q', [])
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


/-- A relational lexing derivation yields a corresponding FST execution. -/
theorem PartialLexRel_to_LexingFST (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned) :
  ∀ w terminals unlexed,
    PartialLexRel spec w terminals unlexed →
    ∃ q', (BuildLexingFST spec).eval w = some (q', terminals) ∧
      (BuildLexingFST spec).eval unlexed = some (q', []) := by
  intro w terminals unlexed h
  have hpl := (PartialLex_pruned_eq_PartialLexRel spec hpruned w terminals unlexed).mp h
  have := PartialLex_to_LexingFST spec he w
  simp only [hpl] at this
  obtain ⟨q', heval_w, heval_unlexed⟩ := this
  exists q'

/-- Any successful lexing-FST execution can be reinterpreted as a relational
lexing derivation with some residual unlexed suffix. -/
theorem LexingFST_to_PartialLexRel (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned) :
  ∀ w q' terminals,
    (BuildLexingFST spec).eval w = some (q', terminals) →
    ∃ (unlexed : List α),
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

/-- Every transition of the lexing FST emits either no tokens, a singleton
token, or the special two-symbol output `[t, eos]` used on finalization. -/
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

/-! ### Detokenizing FST -/
universe x
variable { V : Type x }
variable [BEq V]

/-- The FST that replaces each token by its flattened character sequence. -/
def BuildDetokenizingFST [v: Vocabulary α V] : FST V α Unit :=
  let step := fun _ s => some (Unit.unit, v.flatten s)
  FST.mk Unit.unit step [Unit.unit]

/-- Detokenize a token list by flattening each token and concatenating the
results. -/
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
/-- Executing `BuildDetokenizingFST` is equivalent to plain list
detokenization. -/
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
/-- A single step of the detokenizer composed with an FST equals evaluating the
second FST on the flattened token. -/
lemma detokenizer_comp_step [v: Vocabulary α V] { σ0 } (f : FST α Γ σ0) (q: σ0) :
  ∀ a, ((FST.compose (BuildDetokenizingFST (v := v)) f).step (Unit.unit, q) a) =
    (f.evalFrom q (v.flatten a)).map (fun (q, out) => ((Unit.unit, q), out)) := by
  intro a
  simp[FST.compose, FST.compose_fun_step, BuildDetokenizingFST]
  split <;> simp_all

omit [DecidableEq α] [BEq V] in
/-- Composing the detokenizer with an FST is equivalent to first detokenizing
and then evaluating the FST. -/
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
/-- If two token words detokenize to the same character word, then any
detokenizer-composed FST evaluates them identically. -/
theorem detokenize_eq_comp [v: Vocabulary α V] { σ0 } (w1: List V) (w2: List V) (f : FST α Γ σ0) (q: σ0) :
  detokenize (v := v) w1 = detokenize (v := v) w2 → (FST.compose (BuildDetokenizingFST (v := v) ) f).evalFrom (Unit.unit, q) w1 = (FST.compose (BuildDetokenizingFST (v := v)) f).evalFrom (Unit.unit, q) w2 := by
  intro h
  have hw1 := detokenizer_comp (v := v) f q w1
  have hw2 := detokenizer_comp (v := v) f q w2
  rw[←h] at hw2
  cases hd : detokenize (v := v) w1
  <;> simp[hd] at hw1 hw2
  <;> simp[hw1, hw2]

/-! ### Detokenizer-lexer composition -/

omit [DecidableEq α] [BEq V] in
/-- Any detokenized run can be replaced by one using only singleton-flattening
tokens, thanks to the vocabulary axioms. -/
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

/-- Compose detokenization with the lexing FST to obtain the token-level lexer
used by grammar-constrained decoding. -/
def BuildDetokLexer [v: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ) : FST V (Ch Γ) (Unit × LexingState σ) :=
  let lex_fst := BuildLexingFST spec
  let detok := Detokenizing.BuildDetokenizingFST (v := v)
  FST.compose detok lex_fst

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
/-- If the composed detokenizing lexer produces nonempty output from state `q`,
then the head of that output is singleton-producible from `q`.

This is the core FST-side lemma for completeness: it bridges a multi-step run
producing `T ≠ []` to a witness in `singleProducible q`.

The `hrestart` hypothesis asks that every accepting state of the character
automaton has at least one character that does **not** extend the current
lexeme but **can** start a new one from the start state.  This ensures
the lexer can always complete a token with a single-symbol emission
(without appending EOS), which is required when the first emission on a
run is the two-symbol EOS-triggered `[char t, eos]` pattern.  The
hypothesis holds for all practical lexer specifications—see the project
README for discussion. -/
theorem BuildDetokLexer_singleProducible_of_evalFrom
    [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] [vocab: Vocabulary (Ch α) V]
    (spec : LexerSpec α Γ σ)
    (_hempty : [] ∉ spec.automaton.accepts)
    (hrestart : ∀ s ∈ spec.automaton.accept,
      ∃ c : α, spec.automaton.step s c = none ∧
        (spec.automaton.step spec.automaton.start c).isSome)
    (q : LexingState σ) (w : List V) (qf : Unit × LexingState σ)
    (T : List (Ch Γ))
    (hrun : (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) w = some (qf, T))
    (hne : T ≠ []) :
    T.head hne ∈ (BuildDetokLexer (v := vocab) spec).singleProducible ((), q) := by
  let lexer := BuildDetokLexer (v := vocab) spec
  have hlexer : lexer = (BuildDetokenizingFST.compose (BuildLexingFST spec)) := by
    simp[BuildDetokLexer, lexer]
  -- Stage 1: reduce to singleton tokens
  have h_singleton := detokenize_singleton (v := vocab) (BuildLexingFST spec) q w
  rw[←hlexer] at h_singleton
  obtain ⟨ws, h_eq, h_ws_singleton⟩ := h_singleton
  rw[hrun] at h_eq
  -- Stage 2: decompose into step list
  have h_step_list_exists := lexer.stepList_of_eval ((), q) ws
  simp[←h_eq] at h_step_list_exists
  obtain ⟨step_list, h_step_list⟩ := h_step_list_exists
  -- Stage 3: find first non-empty emission
  obtain ⟨firstIdx, hft_ne, h_prefix_empty⟩ :=
    find_first_nonempty step_list T hne h_step_list.right.left
  -- Each token in ws is singleton
  have ⟨flat, h_flat⟩ : ∃ t, vocab.flatten step_list[firstIdx.val].2.1 = [t] := by
    have := lexer.stepList_w ((), q) ws
    simp only [h_step_list] at this
    have : step_list[firstIdx].2.1 ∈ ws := by
      have h_in : step_list[firstIdx].2.1 ∈ List.map (fun x => x.2.1) step_list := by
        apply List.mem_map.mpr
        exists step_list[firstIdx]
        simp
      rw[this] at h_in
      exact h_in
    exact h_ws_singleton step_list[firstIdx].2.1 this
  -- Stage 4: classify via LexingFst_smallStep
  have h_first_production : lexer.step step_list[firstIdx].1 step_list[firstIdx].2.1 =
      some step_list[firstIdx].2.2 := by
    have := lexer.stepList_zip ((), q) ws
    simp only [h_step_list] at this
    exact this step_list[firstIdx] (by simp)
  simp[lexer, BuildDetokLexer] at h_first_production
  rw[detokenizer_comp_step] at h_first_production
  simp[h_flat] at h_first_production
  obtain ⟨q', produced, hstep, hq'produced⟩ := h_first_production
  have h_small := LexingFst_smallStep spec step_list[firstIdx].1.2 flat q' produced hstep
  have hproduced_ne : produced ≠ [] := by
    have : produced = step_list[firstIdx].2.2.2 := by
      simpa using congrArg Prod.snd hq'produced
    rw[this]; simp at hft_ne; exact hft_ne
  simp[hproduced_ne] at h_small
  -- Prefix produces empty output
  have h_prefix_empty_flat : (step_list.take firstIdx).flatMap produce = [] :=
    empty_prefix_all_empty step_list firstIdx h_prefix_empty
  -- Compute the head
  have h_head_eq : T.head hne = (produce step_list[firstIdx]).head (by simp at hft_ne; exact hft_ne) :=
    first_eq_head_of_first_nonempty T hne step_list firstIdx h_step_list.right.left h_prefix_empty_flat hft_ne
  -- stepList prefix/take info
  have hslen := lexer.stepList_len ((), q) ws
  simp[lexer, h_step_list] at hslen
  have hft_lt_w : firstIdx.val < ws.length := by rw[←hslen]; simp
  -- Case split on output structure
  cases h_small with
  | inl h_one =>
    -- Case 1: produced = [t], exactly one symbol
    obtain ⟨t, ht⟩ := h_one
    have hprod_eq : produced = step_list[firstIdx].2.2.2 := by
      simpa using congrArg Prod.snd hq'produced
    let wfinal := ws.take (firstIdx.val + 1)
    have hpfx := lexer.stepList_prefix_w ((), q) ws
    simp[h_step_list] at hpfx
    have h_step_wfinal : lexer.stepList ((), q) wfinal =
        some (take wfinal.length step_list) := by
      apply hpfx; simp[wfinal, List.take_prefix]
    have heval_raw := lexer.eval_of_stepList_opaque ((), q) wfinal
    simp[h_step_wfinal] at heval_raw
    obtain ⟨a, b, heval⟩ := heval_raw
    -- Show wfinal.length = firstIdx.val + 1
    have hlt : firstIdx.val + 1 ≤ ws.length :=
      Nat.add_one_le_of_lt (hslen ▸ firstIdx.isLt)
    have h_wfinal_len : wfinal.length = firstIdx.val + 1 := by
      simp[wfinal, List.length_take, Nat.min_eq_left hlt]
    -- Bridge Fin/Nat indexing
    have hprod_nat : step_list[↑firstIdx].2.2.2 = [t] := by
      have : step_list[↑firstIdx] = step_list[firstIdx] := rfl
      rw[this, ←hprod_eq]; exact ht
    -- Show the flatMap output = [t]
    have h_produce_eq : (fun (x : (Unit × LexingState σ) × V ×
        (Unit × LexingState σ) × List (Ch Γ)) => x.2.2.2) = produce := rfl
    have h_output : (take wfinal.length step_list).flatMap
        (fun x => x.2.2.2) = [t] := by
      rw[h_wfinal_len, List.take_succ_eq_append_getElem firstIdx.isLt]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw[h_produce_eq, h_prefix_empty_flat, List.nil_append]
      exact hprod_nat
    rw[h_output] at heval
    -- Now heval : lexer.evalFrom ((), q) wfinal = some ((a, b), [t])
    have h_head_t : T.head hne = t := by
      have hprod_t : produce step_list[firstIdx] = [t] := by
        unfold produce; exact hprod_nat
      have : ∀ (l : List (Ch Γ)) (hl : l ≠ []), l = [t] → l.head hl = t := by
        intros l hl heq; subst heq; rfl
      rw[h_head_eq]; exact this _ hft_ne hprod_t
    simp only [FST.singleProducible, Set.mem_setOf_eq]
    exact ⟨wfinal, ((a, b), [T.head hne]), by rw[h_head_t]; exact heval, by simp[h_head_t]⟩
  | inr h_two =>
    -- Case 2: produced = [char t, eos], EOS case
    obtain ⟨hq_acc, hflat_eos, t, ht⟩ := h_two
    obtain ⟨c, hc_none, hc_start⟩ := hrestart _ hq_acc
    -- produced = step_list[firstIdx].2.2.2
    have hprod_eq : produced = step_list[firstIdx].2.2.2 := by
      simpa using congrArg Prod.snd hq'produced
    -- T.head = ExtChar.char t
    have h_head_t : T.head hne = ExtChar.char t := by
      have hprod_t : produce step_list[firstIdx] = [ExtChar.char t, ExtChar.eos] := by
        unfold produce; rw[←hprod_eq]; exact ht
      rw[h_head_eq]
      have : ∀ (l : List (Ch Γ)) (hl : l ≠ []), l = [ExtChar.char t, ExtChar.eos] → l.head hl = ExtChar.char t := by
        intros l hl heq; subst heq; rfl
      exact this _ hft_ne hprod_t
    -- Get prefix evaluation
    have hpfx := lexer.stepList_prefix_w ((), q) ws
    simp[h_step_list] at hpfx
    have h_pfx_len : (ws.take firstIdx.val).length = firstIdx.val := by
      rw[List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hft_lt_w)
    have h_step_pfx : lexer.stepList ((), q) (ws.take firstIdx.val) =
        some (step_list.take firstIdx.val) := by
      have h := hpfx (ws.take firstIdx.val) (List.take_prefix _ ws)
      rwa[h_pfx_len] at h
    -- Get evalFrom for prefix
    have heval_pfx_raw := lexer.eval_of_stepList_opaque ((), q) (ws.take firstIdx.val)
    rw[h_step_pfx] at heval_pfx_raw
    obtain ⟨q_mid, heval_pfx⟩ := heval_pfx_raw
    -- Prefix output is empty
    have h_pfx_output : (step_list.take firstIdx.val).flatMap
        (fun (x : (Unit × LexingState σ) × V × (Unit × LexingState σ) × List (Ch Γ)) => x.2.2.2) = [] := by
      change (step_list.take firstIdx.val).flatMap produce = []
      exact h_prefix_empty_flat
    rw[h_pfx_output] at heval_pfx
    -- Get intermediate state = step_list[firstIdx].1
    have hfi : firstIdx.val < ws.length := hslen ▸ firstIdx.isLt
    have h_eval_take := lexer.stepList_eval_take ((), q) ws ⟨firstIdx.val, hfi⟩
    simp[h_step_list] at h_eval_take
    -- h_eval_take : ∃ x, evalFrom ... = some (step_list[↑fi].1, x)
    -- heval_pfx   : evalFrom ... = some (q_mid, [])
    -- Therefore q_mid = step_list[firstIdx].1
    obtain ⟨out_take, h_out_take⟩ := h_eval_take
    rw[h_out_take] at heval_pfx
    have hqmid_eq : q_mid = step_list[firstIdx].1 := by
      have := congrArg (fun x => x.map Prod.fst) heval_pfx
      simp at this; exact this.symm
    subst hqmid_eq
    -- q_mid = step_list[firstIdx].1, which is (Unit × LexingState σ)
    -- Its second component is step_list[firstIdx].1.2
    set b_pfx := step_list[firstIdx].1.2
    have hqmid_pair : step_list[firstIdx].1 = ((), b_pfx) := by
      ext1
      · exact Unit.ext _ _
      · rfl
    -- Extract the terminal from the EOS step
    have h_term_eq : t = (spec.term (LexingState.src spec b_pfx)).get
        ((spec.hterm _).mp hq_acc) := by
      have hstep' := hstep
      simp only [BuildLexingFST, Id.run] at hstep'
      rw[hflat_eos] at hstep'
      simp only [hq_acc, dite_true] at hstep'
      -- hstep' : some (start, [char T_term, eos]) = some (q', produced)
      have hinj := Option.some.inj hstep'
      have hprod := congrArg Prod.snd hinj
      simp at hprod
      -- hprod now equates the terminal list with produced
      rw[ht] at hprod
      -- hprod should equate [char T_term, eos] with [char t, eos]
      simp at hprod
      exact hprod.symm
    -- Build restart step
    obtain ⟨q_new, hq_new⟩ := Option.isSome_iff_exists.mp hc_start
    have h_lex_restart : (BuildLexingFST spec).step b_pfx (.char c) =
        some (LexingState.id q_new, [ExtChar.char t]) := by
      simp only [BuildLexingFST, Id.run]
      have h_not_some : ¬(spec.automaton.step (LexingState.src spec b_pfx) c).isSome := by
        show ¬(spec.automaton.step (LexingState.src spec step_list[↑firstIdx].1.2) c).isSome
        simp[hc_none]
      have hq_acc' : LexingState.src spec b_pfx ∈ spec.automaton.accept := hq_acc
      simp only [h_not_some, hq_acc', dite_true]
      rw[h_term_eq, hq_new]; simp
    -- Lift to composed lexer
    have h_detok_restart : lexer.step ((), b_pfx) (vocab.embed (.char c)) =
        some (((), LexingState.id q_new), [ExtChar.char t]) := by
      have hde := detok_eval_embed (V := V) spec b_pfx (.char c)
      simp only [lexer, BuildDetokLexer] at hde ⊢
      rw[hde, h_lex_restart]; simp
    -- Build witness word and combine
    let wfinal := ws.take firstIdx.val ++ [vocab.embed (.char c)]
    -- Extract out_take = [] from heval_pfx
    have h_out_take_nil : out_take = [] := by
      have hinj := Option.some.inj heval_pfx
      have h2 := (Prod.ext_iff.mp hinj).2
      simp at h2; exact h2
    -- Simplify h_out_take with out_take = []
    rw[h_out_take_nil] at h_out_take
    -- h_out_take : lexer.evalFrom ((), q) (take ...) = some (step_list[↑firstIdx].1, [])
    -- step_list[↑firstIdx].1 = ((), b_pfx) via hqmid_pair
    have h_detok_restart' : lexer.step step_list[↑firstIdx].1 (vocab.embed (.char c)) =
        some (((), LexingState.id q_new), [ExtChar.char t]) := by
      show lexer.step step_list[firstIdx].1 _ = _
      rw[hqmid_pair]; exact h_detok_restart
    have h_eval_wfinal : lexer.evalFrom ((), q) wfinal =
        some (((), LexingState.id q_new), [ExtChar.char t]) := by
      simp only [wfinal]
      rw[lexer.evalFrom_append, h_out_take]
      show (lexer.evalFrom step_list[↑firstIdx].1 [vocab.embed (.char c)]).map _ = _
      rw[lexer.evalFrom_singleton, h_detok_restart']
      simp
    simp only [FST.singleProducible, Set.mem_setOf_eq]
    exact ⟨wfinal, (((), LexingState.id q_new), [T.head hne]),
      by rw[h_head_t]; exact h_eval_wfinal, by simp[h_head_t]⟩

end Detokenizing
