import VerifiedAgora.tagger
/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies, Anthony DeRossi
-/
import Mathlib.Computability.NFA
import Mathlib.Data.List.ReduceOption

/-!
# Epsilon Nondeterministic Finite Automata

This file contains the definition of an epsilon Nondeterministic Finite Automaton (`εNFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitions,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `Fintype` instance must be
supplied for true `εNFA`'s.
-/


open Set

open Computability

-- "ε_NFA"

universe u v

/-- An `εNFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states and can make ε-transitions by
  inputting `none`.
  Since this definition allows for Automata with infinite states, a `Fintype` instance must be
  supplied for true `εNFA`'s. -/
structure εNFA (α : Type u) (σ : Type v) where
  /-- Transition function. The automaton is rendered non-deterministic by this transition function
  returning `Set σ` (rather than `σ`), and ε-transitions are made possible by taking `Option α`
  (rather than `α`). -/
  step : σ → Option α → Set σ
  /-- Starting states. -/
  start : Set σ
  /-- Set of acceptance states. -/
  accept : Set σ

variable {α : Type u} {σ : Type v} (M : εNFA α σ) {S : Set σ} {s t u : σ} {a : α}

namespace εNFA

/-- The `εClosure` of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
inductive εClosure (S : Set σ) : Set σ
  | base : ∀ s ∈ S, εClosure S s
  | step : ∀ (s), ∀ t ∈ M.step s none, εClosure S s → εClosure S t

@[target, simp]
theorem subset_εClosure (S : Set σ) : S ⊆ M.εClosure S := by sorry

@[target, simp]
theorem εClosure_empty : M.εClosure ∅ = ∅ := by sorry

@[target, simp]
theorem εClosure_univ : M.εClosure univ = univ := by sorry

@[target]
theorem mem_εClosure_iff_exists : s ∈ M.εClosure S ↔ ∃ t ∈ S, s ∈ M.εClosure {t} := by sorry

/-- `M.stepSet S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.εClosure (M.step s a)

variable {M}

@[simp]
theorem mem_stepSet_iff : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.εClosure (M.step t a) := by
  simp_rw [stepSet, mem_iUnion₂, exists_prop]

@[target, simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by sorry

variable (M)

/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet (M.εClosure start)

@[target, simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S := by sorry

@[target, simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet (M.εClosure S) a := by sorry

@[target, simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by sorry

@[target, simp]
theorem evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅ := by sorry

@[target]
theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s ∈ M.evalFrom S x ↔ ∃ t ∈ S, s ∈ M.evalFrom {t} x := by sorry

/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
`M.start`. -/
def eval :=
  M.evalFrom M.start

@[target, simp]
theorem eval_nil : M.eval [] = M.εClosure M.start := by sorry

@[target, simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet (M.εClosure M.start) a := by sorry

@[target, simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a := by sorry

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α :=
  { x | ∃ S ∈ M.accept, S ∈ M.eval x }

/-- `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list
of transitions in order. -/
@[mk_iff]
inductive IsPath : σ → σ → List (Option α) → Prop
  | nil (s : σ) : IsPath s s []
  | cons (t s u : σ) (a : Option α) (x : List (Option α)) :
      t ∈ M.step s a → IsPath t u x → IsPath s u (a :: x)

@[target, simp]
theorem isPath_nil : M.IsPath s t [] ↔ s = t := by sorry

@[target, simp]
theorem isPath_singleton {a : Option α} : M.IsPath s t [a] ↔ t ∈ M.step s a := by sorry

theorem isPath_append {x y : List (Option α)} :
    M.IsPath s u (x ++ y) ↔ ∃ t, M.IsPath s t x ∧ M.IsPath t u y where
  mp := by
    induction' x with x a ih generalizing s
    · rw [List.nil_append]
      tauto
    · rintro (_ | ⟨t, _, _, _, _, _, h⟩)
      apply ih at h
      tauto
  mpr := by
    intro ⟨t, hx, _⟩
    induction x generalizing s <;> cases hx <;> tauto

@[target]
theorem mem_εClosure_iff_exists_path {s₁ s₂ : σ} :
    s₂ ∈ M.εClosure {s₁} ↔ ∃ n, M.IsPath s₁ s₂ (.replicate n none) := by sorry

@[target]
theorem mem_evalFrom_iff_exists_path {s₁ s₂ : σ} {x : List α} :
    s₂ ∈ M.evalFrom {s₁} x ↔ ∃ x', x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' := by sorry

@[target]
theorem mem_accepts_iff_exists_path {x : List α} :
    x ∈ M.accepts ↔
      ∃ s₁ s₂ x', s₁ ∈ M.start ∧ s₂ ∈ M.accept ∧ x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' := by sorry

/-! ### Conversions between `εNFA` and `NFA` -/


/-- `M.toNFA` is an `NFA` constructed from an `εNFA` `M`. -/
def toNFA : NFA α σ where
  step S a := M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept

@[target, simp]
theorem toNFA_evalFrom_match (start : Set σ) :
    M.toNFA.evalFrom (M.εClosure start) = M.evalFrom start := by sorry

@[target, simp]
theorem toNFA_correct : M.toNFA.accepts = M.accepts := by sorry

@[target]
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c, x = a ++ b ++ c ∧
      a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by sorry

end εNFA

namespace NFA

/-- `M.toεNFA` is an `εNFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def toεNFA (M : NFA α σ) : εNFA α σ where
  step s a := a.casesOn' ∅ fun a ↦ M.step s a
  start := M.start
  accept := M.accept

@[target, simp]
theorem toεNFA_εClosure (M : NFA α σ) (S : Set σ) : M.toεNFA.εClosure S = S := by sorry

@[target, simp]
theorem toεNFA_evalFrom_match (M : NFA α σ) (start : Set σ) :
    M.toεNFA.evalFrom start = M.evalFrom start := by sorry

@[target, simp]
theorem toεNFA_correct (M : NFA α σ) : M.toεNFA.accepts = M.accepts := by sorry

end NFA

/-! ### Regex-like operations -/


namespace εNFA

instance : Zero (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, ∅, ∅⟩⟩

instance : One (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, univ, univ⟩⟩

instance : Inhabited (εNFA α σ) :=
  ⟨0⟩

@[target, simp]
theorem step_zero (s a) : (0 : εNFA α σ).step s a = ∅ := by sorry

@[target, simp]
theorem step_one (s a) : (1 : εNFA α σ).step s a = ∅ := by sorry

@[simp]
theorem start_zero : (0 : εNFA α σ).start = ∅ :=
  rfl

@[target, simp]
theorem start_one : (1 : εNFA α σ).start = univ := by sorry

@[target, simp]
theorem accept_zero : (0 : εNFA α σ).accept = ∅ := by sorry

@[target, simp]
theorem accept_one : (1 : εNFA α σ).accept = univ := by sorry

end εNFA
