import ConstrainedDecodingFormalization.Lexing.Base
import ConstrainedDecodingFormalization.Vocabulary

/-!
# Detokenizing FSTs

This file defines the token-flattening FST and its composition with the lexing
FST. Whitespace-specific exchange arguments are in `Lexing.Whitespace`.
-/

namespace Detokenizing

/-! ### Detokenizing FST -/
open List
universe u v w
variable {α : Type u} {Γ : Type v} {σ : Type w}
variable [DecidableEq α] [DecidableEq σ] [BEq α] [BEq σ] [LawfulBEq σ]
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

universe y

section Vocabulary

variable [v : Vocabulary α V] {σ0 : Type y}

omit [DecidableEq α] [BEq V] in
lemma detokenize_flatmap (w : List V) :
  detokenize (v := v) w = (w.flatMap (fun big => v.flatten big)) := by
  induction w
  case nil => simp[detokenize, List.flatMap]
  case cons head tail ih =>
    simp[detokenize, List.flatMap]
    simp[ih]
    rfl

omit [DecidableEq α] [BEq V] in
lemma detokenize_app (s1 s2 : List V) :
  detokenize (v := v) (s1 ++ s2) = detokenize (v := v) s1 ++ detokenize (v := v) s2 := by
  induction s1
  case nil => simp[detokenize]
  case cons head tail ih =>
    simp[detokenize, List.append_assoc]
    rw[←ih]

omit [DecidableEq α] [BEq V] in
/-- Executing `BuildDetokenizingFST` is equivalent to plain list
detokenization. -/
theorem detokenizerFST_eq_detokenizer :
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
lemma detokenizer_comp_step (f : FST α Γ σ0) (q: σ0) :
  ∀ a, ((FST.compose (BuildDetokenizingFST (v := v)) f).step (Unit.unit, q) a) =
    (f.evalFrom q (v.flatten a)).map (fun (q, out) => ((Unit.unit, q), out)) := by
  intro a
  simp[FST.compose, FST.compose_fun_step, BuildDetokenizingFST]
  split <;> simp_all

omit [DecidableEq α] [BEq V] in
/-- Composing the detokenizer with an FST is equivalent to first detokenizing
and then evaluating the FST. -/
theorem detokenizer_comp (f : FST α Γ σ0) (q: σ0) :
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
theorem detokenize_eq_comp (w1: List V) (w2: List V) (f : FST α Γ σ0) (q: σ0) :
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
theorem detokenize_singleton (f: FST α Γ σ0) (q: σ0) :
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

end Vocabulary

/-- Compose detokenization with the lexing FST to obtain the token-level lexer
used by grammar-constrained decoding. -/
def BuildDetokLexer [v: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ) : FST V (Ch Γ) (Unit × LexingState σ) :=
  let lex_fst := BuildLexingFST spec
  let detok := Detokenizing.BuildDetokenizingFST (v := v)
  FST.compose detok lex_fst

end Detokenizing
