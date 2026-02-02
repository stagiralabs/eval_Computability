import VerifiedAgora.tagger
/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Computability.Language
import Mathlib.Tactic.AdaptationNote

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

## TODO

* Show that this regular expressions and DFA/NFA's are equivalent. -/

open List Set

open Computability

universe u

variable {α β γ : Type*}

-- Disable generation of unneeded lemmas which the simpNF linter would complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- This is the definition of regular expressions. The names used here is to mirror the definition
of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression α
  | epsilon : RegularExpression α
  | char : α → RegularExpression α
  | plus : RegularExpression α → RegularExpression α → RegularExpression α
  | comp : RegularExpression α → RegularExpression α → RegularExpression α
  | star : RegularExpression α → RegularExpression α

namespace RegularExpression

variable {a b : α}

instance : Inhabited (RegularExpression α) :=
  ⟨zero⟩

instance : Add (RegularExpression α) :=
  ⟨plus⟩

instance : Mul (RegularExpression α) :=
  ⟨comp⟩

instance : One (RegularExpression α) :=
  ⟨epsilon⟩

instance : Zero (RegularExpression α) :=
  ⟨zero⟩

instance : Pow (RegularExpression α) ℕ :=
  ⟨fun n r => npowRec r n⟩

@[target, simp]
theorem zero_def : (zero : RegularExpression α) = 0 := by sorry

@[target, simp]
theorem one_def : (epsilon : RegularExpression α) = 1 := by sorry

@[target, simp]
theorem plus_def (P Q : RegularExpression α) : plus P Q = P + Q := by sorry

@[target, simp]
theorem comp_def (P Q : RegularExpression α) : comp P Q = P * Q := by sorry

/-- `matches' P` provides a language which contains all strings that `P` matches -/
-- Porting note: was '@[simp] but removed based on
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simpNF.20issues.20in.20Computability.2ERegularExpressions.20!4.232306/near/328355362
def matches' : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | char a => {[a]}
  | P + Q => P.matches' + Q.matches'
  | P * Q => P.matches' * Q.matches'
  | star P => P.matches'∗

@[target, simp]
theorem matches'_zero : (0 : RegularExpression α).matches' = 0 := by sorry

@[target, simp]
theorem matches'_epsilon : (1 : RegularExpression α).matches' = 1 := by sorry

@[target, simp]
theorem matches'_char (a : α) : (char a).matches' = {[a]} := by sorry

@[target, simp]
theorem matches'_add (P Q : RegularExpression α) : (P + Q).matches' = P.matches' + Q.matches' := by sorry

@[target, simp]
theorem matches'_mul (P Q : RegularExpression α) : (P * Q).matches' = P.matches' * Q.matches' := by sorry

@[target, simp]
theorem matches'_pow (P : RegularExpression α) : ∀ n : ℕ, (P ^ n).matches' = P.matches' ^ n := by sorry

@[target, simp]
theorem matches'_star (P : RegularExpression α) : P.star.matches' = P.matches'∗ := by sorry

/-- `matchEpsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | star _P => true

section DecidableEq
variable [DecidableEq α]

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | star P, a => deriv P a * star P

@[target, simp]
theorem deriv_zero (a : α) : deriv 0 a = 0 := by sorry

@[target, simp]
theorem deriv_one (a : α) : deriv 1 a = 0 := by sorry

@[target, simp]
theorem deriv_char_self (a : α) : deriv (char a) a = 1 := by sorry

@[target, simp]
theorem deriv_char_of_ne (h : a ≠ b) : deriv (char a) b = 0 := by sorry

@[simp]
theorem deriv_add (P Q : RegularExpression α) (a : α) : deriv (P + Q) a = deriv P a + deriv Q a :=
  rfl

@[target, simp]
theorem deriv_star (P : RegularExpression α) (a : α) : deriv P.star a = deriv P a * star P := by sorry

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches'`. -/
def rmatch : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as

@[target, simp]
theorem zero_rmatch (x : List α) : rmatch 0 x = false := by sorry

@[target]
theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] := by sorry

@[target]
theorem char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a] := by sorry

@[target]
theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := by sorry

@[target]
theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatch x ↔ ∃ t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := by sorry

@[target]

theorem star_rmatch_iff (P : RegularExpression α) :
    ∀ x : List α, (star P).rmatch x ↔ ∃ S : List (List α), x
          = S.flatten ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatch t :=
  fun x => by
    have IH := fun t (_h : List.length t < List.length x) => star_rmatch_iff P t
    clear star_rmatch_iff
    constructor
    · rcases x with - | ⟨a, x⟩
      · intro _h
        use []; dsimp; tauto
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        have hwf : u.length < (List.cons a x).length := by
          rw [hs, List.length_cons, List.length_append]
          omega
        rw [IH _ hwf] at hu
        rcases hu with ⟨S', hsum, helem⟩
        use (a :: t) :: S'
        constructor
        · simp [hs, hsum]
        · intro t' ht'
          cases ht' with
          | head ht' =>
            simp only [ne_eq, not_false_iff, true_and, rmatch, reduceCtorEq]
            exact ht
          | tail _ ht' => exact helem t' ht'
    · rintro ⟨S, hsum, helem⟩
      rcases x with - | ⟨a, x⟩
      · rfl
      · rw [rmatch, deriv, mul_rmatch_iff]
        rcases S with - | ⟨t', U⟩
        · exact ⟨[], [], by tauto⟩
        · obtain - | ⟨b, t⟩ := t'
          · simp only [forall_eq_or_imp, List.mem_cons] at helem
            simp only [eq_self_iff_true, not_true, Ne, false_and] at helem
          simp only [List.flatten, List.cons_append, List.cons_eq_cons] at hsum
          refine ⟨t, U.flatten, hsum.2, ?_, ?_⟩
          · specialize helem (b :: t) (by simp)
            rw [rmatch] at helem
            convert helem.2
            exact hsum.1
          · have hwf : U.flatten.length < (List.cons a x).length := by
              rw [hsum.1, hsum.2]
              simp only [List.length_append, List.length_flatten, List.length]
              omega
            rw [IH _ hwf]
            refine ⟨U, rfl, fun t h => helem t ?_⟩
            right
            assumption
  termination_by t => (P, t.length)

@[target, simp]
theorem rmatch_iff_matches' (P : RegularExpression α) (x : List α) :
    P.rmatch x ↔ x ∈ P.matches' := by sorry

instance (P : RegularExpression α) : DecidablePred (· ∈ P.matches') := fun _ ↦
  decidable_of_iff _ (rmatch_iff_matches' _ _)

end DecidableEq

/-- Map the alphabet of a regular expression. -/
@[simp]
def map (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | char a => char (f a)
  | R + S => map f R + map f S
  | R * S => map f R * map f S
  | star R => star (map f R)

@[simp]
protected theorem map_pow (f : α → β) (P : RegularExpression α) :
    ∀ n : ℕ, map f (P ^ n) = map f P ^ n
  | 0 => by unfold map; rfl
  | n + 1 => (congr_arg (· * map f P) (RegularExpression.map_pow f P n) :)

@[target, simp]
theorem map_id : ∀ P : RegularExpression α, P.map id = P := by sorry

@[target, simp]
theorem map_map (g : β → γ) (f : α → β) : ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f) := by sorry

/-- The language of the map is the map of the language. -/
@[target, simp] theorem matches'_map (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).matches' = Language.map f P.matches'
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | char a => by
    rw [eq_comm]
    exact image_singleton
  | R + S => by simp only [matches'_map, map, matches'_add, map_add]
  | R * S => by simp [matches'_map]
  | star R => by simp [matches'_map]

end RegularExpression
