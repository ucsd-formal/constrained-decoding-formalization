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

/-!
# Base lexing transducers

This file connects deterministic character-level lexing with the finite-state
transducer model used by the rest of the development.

Its main ingredients are:

* `LexerSpec`, which packages a character automaton together with token labels
  on accepting states;
* `PartialLexRel` and `PartialLex`, relational and executable formulations of
  incremental lexing;
* `BuildLexingFST`, which turns a lexer specification into an FST over
  EOS-extended characters.

The FST-correctness, detokenizing FST, and whitespace-specific arguments are
split into `Lexing.Correctness`, `Lexing.Detokenizing`, and
`Lexing.Whitespace`.
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
def PartialLex_trans (spec: LexerSpec α Γ σ) (prev: Option (List (Ch Γ) × List α)) (c : Ch α)
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
def PartialLex_trans_nil (spec: LexerSpec α Γ σ) (c : Ch α) :
  PartialLex_trans spec none c = none := by
  simp[PartialLex_trans]

@[simp]
def PartialLex_trans_foldl_nil (spec: LexerSpec α Γ σ) (ws : List (Ch α)) :
  foldl (PartialLex_trans spec) none ws = none :=
  foldl_fixed' (congrFun rfl) ws

@[simp]
def PartialLex_seed (spec: LexerSpec α Γ σ) (seed: Option (List (Ch Γ) × List α)) : Lexer α Γ :=
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
