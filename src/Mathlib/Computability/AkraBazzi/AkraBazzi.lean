import VerifiedAgora.tagger
/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Computability.AkraBazzi.GrowsPolynomially
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Divide-and-conquer recurrences and the Akra-Bazzi theorem

A divide-and-conquer recurrence is a function `T : ℕ → ℝ` that satisfies a recurrence relation of
the form `T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)` for large enough `n`, where `r_i(n)` is some
function where `‖r_i(n) - b_i n‖ ∈ o(n / (log n)^2)` for every `i`, the `a_i`'s are some positive
coefficients, and the `b_i`'s are reals `∈ (0,1)`. (Note that this can be improved to
`O(n / (log n)^(1+ε))`, this is left as future work.) These recurrences arise mainly in the
analysis of divide-and-conquer algorithms such as mergesort or Strassen's algorithm for matrix
multiplication.  This class of algorithms works by dividing an instance of the problem of size `n`,
into `k` smaller instances, where the `i`'th instance is of size roughly `b_i n`, and calling itself
recursively on those smaller instances. `T(n)` then represents the running time of the algorithm,
and `g(n)` represents the running time required to actually divide up the instance and process the
answers that come out of the recursive calls. Since virtually all such algorithms produce instances
that are only approximately of size `b_i n` (they have to round up or down at the very least), we
allow the instance sizes to be given by some function `r_i(n)` that approximates `b_i n`.

The Akra-Bazzi theorem gives the asymptotic order of such a recurrence: it states that
`T(n) ∈ Θ(n^p (1 + ∑_{u=0}^{n-1} g(n) / u^{p+1}))`,
where `p` is the unique real number such that `∑ a_i b_i^p = 1`.

## Main definitions and results

* `AkraBazziRecurrence T g a b r`: the predicate stating that `T : ℕ → ℝ` satisfies an Akra-Bazzi
  recurrence with parameters `g`, `a`, `b` and `r` as above.
* `GrowsPolynomially`: The growth condition that `g` must satisfy for the theorem to apply.
  It roughly states that
  `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for u between b*n and n for any constant `b ∈ (0,1)`.
* `sumTransform`: The transformation which turns a function `g` into
  `n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)`.
* `asympBound`: The asymptotic bound satisfied by an Akra-Bazzi recurrence, namely
  `n^p (1 + ∑ g(u) / u^(p+1))`
* `isTheta_asympBound`: The main result stating that
  `T(n) ∈ Θ(n^p (1 + ∑_{u=0}^{n-1} g(n) / u^{p+1}))`

## Implementation

Note that the original version of the theorem has an integral rather than a sum in the above
expression, and first considers the `T : ℝ → ℝ` case before moving on to `ℕ → ℝ`. We prove the
above version with a sum, as it is simpler and more relevant for algorithms.

## TODO

* Specialize this theorem to the very common case where the recurrence is of the form
`T(n) = ℓT(r_i(n)) + g(n)`
where `g(n) ∈ Θ(n^t)` for some `t`. (This is often called the "master theorem" in the literature.)
* Add the original version of the theorem with an integral instead of a sum.

## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

open Finset Real Filter Asymptotics
open scoped Topology

/-!
#### Definition of Akra-Bazzi recurrences

This section defines the predicate `AkraBazziRecurrence T g a b r` which states that `T`
satisfies the recurrence
`T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)`
with appropriate conditions on the various parameters.
-/

/-- An Akra-Bazzi recurrence is a function that satisfies the recurrence
`T n = (∑ i, a i * T (r i n)) + g n`. -/
structure AkraBazziRecurrence {α : Type*} [Fintype α] [Nonempty α]
    (T : ℕ → ℝ) (g : ℝ → ℝ) (a : α → ℝ) (b : α → ℝ) (r : α → ℕ → ℕ) where
  /-- Point below which the recurrence is in the base case -/
  n₀ : ℕ
  /-- `n₀` is always `> 0` -/
  n₀_gt_zero : 0 < n₀
  /-- The `a`'s are nonzero -/
  a_pos : ∀ i, 0 < a i
  /-- The `b`'s are nonzero -/
  b_pos : ∀ i, 0 < b i
  /-- The b's are less than 1 -/
  b_lt_one : ∀ i, b i < 1
  /-- `g` is nonnegative -/
  g_nonneg : ∀ x ≥ 0, 0 ≤ g x
  /-- `g` grows polynomially -/
  g_grows_poly : AkraBazziRecurrence.GrowsPolynomially g
  /-- The actual recurrence -/
  h_rec (n : ℕ) (hn₀ : n₀ ≤ n) : T n = (∑ i, a i * T (r i n)) + g n
  /-- Base case: `T(n) > 0` whenever `n < n₀` -/
  T_gt_zero' (n : ℕ) (hn : n < n₀) : 0 < T n
  /-- The `r`'s always reduce `n` -/
  r_lt_n : ∀ i n, n₀ ≤ n → r i n < n
  /-- The `r`'s approximate the `b`'s -/
  dist_r_b : ∀ i, (fun n => (r i n : ℝ) - b i * n) =o[atTop] fun n => n / (log n) ^ 2

namespace AkraBazziRecurrence

section min_max

variable {α : Type*} [Finite α] [Nonempty α]

/-- Smallest `b i` -/
noncomputable def min_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_min b

/-- Largest `b i` -/
noncomputable def max_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_max b

@[aesop safe apply]
lemma min_bi_le {b : α → ℝ} (i : α) : b (min_bi b) ≤ b i :=
  Classical.choose_spec (Finite.exists_min b) i

@[target, aesop safe apply]
lemma max_bi_le {b : α → ℝ} (i : α) : b i ≤ b (max_bi b) := by sorry

end min_max

@[target]
lemma isLittleO_self_div_log_id :
    (fun (n : ℕ) => n / log n ^ 2) =o[atTop] (fun (n : ℕ) => (n : ℝ)) := by sorry

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)
section
include R

@[target]
lemma dist_r_b' : ∀ᶠ n in atTop, ∀ i, ‖(r i n : ℝ) - b i * n‖ ≤ n / log n ^ 2 := by sorry

@[target]
lemma eventually_b_le_r : ∀ᶠ (n : ℕ) in atTop, ∀ i, (b i : ℝ) * n - (n / log n ^ 2) ≤ r i n := by sorry

@[target]
lemma eventually_r_le_b : ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n ≤ (b i : ℝ) * n + (n / log n ^ 2) := by sorry

@[target]
lemma eventually_r_lt_n : ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n < n := by sorry

@[target]
lemma eventually_bi_mul_le_r : ∀ᶠ (n : ℕ) in atTop, ∀ i, (b (min_bi b) / 2) * n ≤ r i n := by sorry

lemma bi_min_div_two_lt_one : b (min_bi b) / 2 < 1 := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  calc b (min_bi b) / 2 < b (min_bi b) := by aesop (add safe apply div_two_lt_of_pos)
                      _ < 1 := R.b_lt_one _

@[target]
lemma bi_min_div_two_pos : 0 < b (min_bi b) / 2 := by sorry

@[target]
lemma exists_eventually_const_mul_le_r :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop, ∀ i, c * n ≤ r i n := by sorry

lemma eventually_r_ge (C : ℝ) : ∀ᶠ (n : ℕ) in atTop, ∀ i, C ≤ r i n := by
  obtain ⟨c, hc_mem, hc⟩ := R.exists_eventually_const_mul_le_r
  filter_upwards [eventually_ge_atTop ⌈C / c⌉₊, hc] with n hn₁ hn₂
  have h₁ := hc_mem.1
  intro i
  calc C = c * (C / c) := by
            rw [← mul_div_assoc]
            exact (mul_div_cancel_left₀ _ (by positivity)).symm
       _ ≤ c * ⌈C / c⌉₊ := by gcongr; simp [Nat.le_ceil]
       _ ≤ c * n := by gcongr
       _ ≤ r i n := hn₂ i

@[target]
lemma tendsto_atTop_r (i : α) : Tendsto (r i) atTop atTop := by sorry

@[target]
lemma tendsto_atTop_r_real (i : α) : Tendsto (fun n => (r i n : ℝ)) atTop atTop := by sorry

@[target]
lemma exists_eventually_r_le_const_mul :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n ≤ c * n := by sorry

@[target]
lemma eventually_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < r i n := by sorry

@[target]
lemma eventually_log_b_mul_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < log (b i * n) := by sorry

@[aesop safe apply] lemma T_pos (n : ℕ) : 0 < T n := by
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    cases lt_or_le n R.n₀ with
    | inl hn => exact R.T_gt_zero' n hn -- n < R.n₀
    | inr hn => -- R.n₀ ≤ n
      rw [R.h_rec n hn]
      have := R.g_nonneg
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos ?sum_elems univ_nonempty) (by aesop)
      exact fun i _ => mul_pos (R.a_pos i) <| h_ind _ (R.r_lt_n i _ hn)

@[target, aesop safe apply]
lemma T_nonneg (n : ℕ) : 0 ≤ T n := by sorry

end

/-!
#### Smoothing function

We define `ε` as the "smoothing function" `fun n => 1 / log n`, which will be used in the form of a
factor of `1 ± ε n` needed to make the induction step go through.

This is its own definition to make it easier to switch to a different smoothing function.
For example, choosing `1 / log n ^ δ` for a suitable choice of `δ` leads to a slightly tighter
theorem at the price of a more complicated proof.

This part of the file then proves several properties of this function that will be needed later in
the proof.
-/

/-- The "smoothing function" is defined as `1 / log n`. This is defined as an `ℝ → ℝ` function
as opposed to `ℕ → ℝ` since this is more convenient for the proof, where we need to e.g. take
derivatives. -/
noncomputable def smoothingFn (n : ℝ) : ℝ := 1 / log n

local notation "ε" => smoothingFn

@[target]
lemma one_add_smoothingFn_le_two {x : ℝ} (hx : exp 1 ≤ x) : 1 + ε x ≤ 2 := by sorry

@[target]
lemma isLittleO_smoothingFn_one : ε =o[atTop] (fun _ => (1 : ℝ)) := by sorry

lemma isEquivalent_one_add_smoothingFn_one : (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : ℝ)) :=
  IsEquivalent.add_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

lemma isEquivalent_one_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : ℝ)) :=
  IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

@[target]
lemma growsPolynomially_one_sub_smoothingFn : GrowsPolynomially fun x => 1 - ε x := by sorry

@[target]
lemma growsPolynomially_one_add_smoothingFn : GrowsPolynomially fun x => 1 + ε x := by sorry

@[target]
lemma eventually_one_sub_smoothingFn_gt_const_real (c : ℝ) (hc : c < 1) :
    ∀ᶠ (x : ℝ) in atTop, c < 1 - ε x := by sorry

@[target]
lemma eventually_one_sub_smoothingFn_gt_const (c : ℝ) (hc : c < 1) :
    ∀ᶠ (n : ℕ) in atTop, c < 1 - ε n := by sorry

@[target]
lemma eventually_one_sub_smoothingFn_pos_real : ∀ᶠ (x : ℝ) in atTop, 0 < 1 - ε x := by sorry

@[target]
lemma eventually_one_sub_smoothingFn_pos : ∀ᶠ (n : ℕ) in atTop, 0 < 1 - ε n := by sorry

@[target]
lemma eventually_one_sub_smoothingFn_nonneg : ∀ᶠ (n : ℕ) in atTop, 0 ≤ 1 - ε n := by sorry

@[target]
lemma eventually_one_sub_smoothingFn_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < 1 - ε (r i n) := by sorry

@[target, aesop safe apply]
lemma differentiableAt_smoothingFn {x : ℝ} (hx : 1 < x) : DifferentiableAt ℝ ε x := by sorry

@[target, aesop safe apply]
lemma differentiableAt_one_sub_smoothingFn {x : ℝ} (hx : 1 < x) :
    DifferentiableAt ℝ (fun z => 1 - ε z) x := by sorry

@[target]
lemma differentiableOn_one_sub_smoothingFn : DifferentiableOn ℝ (fun z => 1 - ε z) (Set.Ioi 1) := by sorry

@[target, aesop safe apply]
lemma differentiableAt_one_add_smoothingFn {x : ℝ} (hx : 1 < x) :
    DifferentiableAt ℝ (fun z => 1 + ε z) x := by sorry

@[target]
lemma differentiableOn_one_add_smoothingFn : DifferentiableOn ℝ (fun z => 1 + ε z) (Set.Ioi 1) := by sorry

lemma deriv_smoothingFn {x : ℝ} (hx : 1 < x) : deriv ε x = -x⁻¹ / (log x ^ 2) := by
  have : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  show deriv (fun z => 1 / log z) x = -x⁻¹ / (log x ^ 2)
  rw [deriv_div] <;> aesop

@[target]
lemma isLittleO_deriv_smoothingFn : deriv ε =o[atTop] fun x => x⁻¹ := by sorry

@[target]
lemma eventually_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) := by sorry

@[target]
lemma eventually_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by sorry

@[target]
lemma isLittleO_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =o[atTop] fun (x : ℝ) => x⁻¹ := by sorry

@[target]
lemma isLittleO_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =o[atTop] fun (x : ℝ) => x⁻¹ := by sorry

@[target]
lemma eventually_one_add_smoothingFn_pos : ∀ᶠ (n : ℕ) in atTop, 0 < 1 + ε n := by sorry

@[target]
lemma eventually_one_add_smoothingFn_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < 1 + ε (r i n) := by sorry

lemma eventually_one_add_smoothingFn_nonneg : ∀ᶠ (n : ℕ) in atTop, 0 ≤ 1 + ε n := by
  filter_upwards [eventually_one_add_smoothingFn_pos] with n hn; exact le_of_lt hn

@[target]
lemma strictAntiOn_smoothingFn : StrictAntiOn ε (Set.Ioi 1) := by sorry

@[target]
lemma strictMonoOn_one_sub_smoothingFn :
    StrictMonoOn (fun (x : ℝ) => (1 : ℝ) - ε x) (Set.Ioi 1) := by sorry

@[target]
lemma strictAntiOn_one_add_smoothingFn : StrictAntiOn (fun (x : ℝ) => (1 : ℝ) + ε x) (Set.Ioi 1) := by sorry

section
include R

@[target]
lemma isEquivalent_smoothingFn_sub_self (i : α) :
    (fun (n : ℕ) => ε (b i * n) - ε n) ~[atTop] fun n => -log (b i) / (log n)^2 := by sorry

@[target]
lemma isTheta_smoothingFn_sub_self (i : α) :
    (fun (n : ℕ) => ε (b i * n) - ε n) =Θ[atTop] fun n => 1 / (log n)^2 := by sorry

/-!
#### Akra-Bazzi exponent `p`

Every Akra-Bazzi recurrence has an associated exponent, denoted by `p : ℝ`, such that
`∑ a_i b_i^p = 1`.  This section shows the existence and uniqueness of this exponent `p` for any
`R : AkraBazziRecurrence`, and defines `R.asympBound` to be the asymptotic bound satisfied by `R`,
namely `n^p (1 + ∑_{u < n} g(u) / u^(p+1))`. -/

@[continuity]
lemma continuous_sumCoeffsExp : Continuous (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine continuous_finset_sum Finset.univ fun i _ => Continuous.mul (by continuity) ?_
  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))

lemma strictAnti_sumCoeffsExp : StrictAnti (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  rw [← Finset.sum_fn]
  refine Finset.sum_induction_nonempty _ _ (fun _ _ => StrictAnti.add) univ_nonempty ?terms
  refine fun i _ => StrictAnti.const_mul ?_ (R.a_pos i)
  exact Real.strictAnti_rpow_of_base_lt_one (R.b_pos i) (R.b_lt_one i)

lemma tendsto_zero_sumCoeffsExp : Tendsto (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) atTop (𝓝 0) := by
  have h₁ : Finset.univ.sum (fun _ : α => (0 : ℝ)) = 0 := by simp
  rw [← h₁]
  refine tendsto_finset_sum (univ : Finset α) (fun i _ => ?_)
  rw [← mul_zero (a i)]
  refine Tendsto.mul (by simp) <| tendsto_rpow_atTop_of_base_lt_one _ ?_ (R.b_lt_one i)
  have := R.b_pos i
  linarith

lemma tendsto_atTop_sumCoeffsExp : Tendsto (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) atBot atTop := by
  have h₁ : Tendsto (fun p : ℝ => (a (max_bi b) : ℝ) * b (max_bi b) ^ p) atBot atTop :=
    Tendsto.mul_atTop (R.a_pos (max_bi b)) (by simp)
      <| tendsto_rpow_atBot_of_base_lt_one _
      (by have := R.b_pos (max_bi b); linarith) (R.b_lt_one _)
  refine tendsto_atTop_mono (fun p => ?_) h₁
  refine Finset.single_le_sum (f := fun i => (a i : ℝ) * b i ^ p) (fun i _ => ?_) (mem_univ _)
  have h₁ : 0 < a i := R.a_pos i
  have h₂ : 0 < b i := R.b_pos i
  positivity

lemma one_mem_range_sumCoeffsExp : 1 ∈ Set.range (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine mem_range_of_exists_le_of_exists_ge R.continuous_sumCoeffsExp ?le_one ?ge_one
  case le_one =>
    exact R.tendsto_zero_sumCoeffsExp.eventually_le_const zero_lt_one |>.exists
  case ge_one =>
    exact R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop _ |>.exists

/-- The function x ↦ ∑ a_i b_i^x is injective. This implies the uniqueness of `p`. -/
lemma injective_sumCoeffsExp : Function.Injective (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) :=
    R.strictAnti_sumCoeffsExp.injective

end

variable (a b) in
/-- The exponent `p` associated with a particular Akra-Bazzi recurrence. -/
noncomputable irreducible_def p : ℝ := Function.invFun (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) 1

include R in
@[target, simp]
lemma sumCoeffsExp_p_eq_one : ∑ i, a i * (b i) ^ p a b = 1 := by sorry

/-!
#### The sum transform

This section defines the "sum transform" of a function `g` as
`∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)`,
and uses it to define `asympBound` as the bound satisfied by an Akra-Bazzi recurrence.

Several properties of the sum transform are then proven.
-/

/-- The transformation which turns a function `g` into
`n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)`. -/
noncomputable def sumTransform (p : ℝ) (g : ℝ → ℝ) (n₀ n : ℕ) :=
  n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p + 1)

@[target]
lemma sumTransform_def {p : ℝ} {g : ℝ → ℝ} {n₀ n : ℕ} :
    sumTransform p g n₀ n = n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p + 1) := by sorry

variable (g) (a) (b)
/-- The asymptotic bound satisfied by an Akra-Bazzi recurrence, namely
`n^p (1 + ∑_{u < n} g(u) / u^(p+1))`. -/
noncomputable def asympBound (n : ℕ) : ℝ := n ^ p a b + sumTransform (p a b) g 0 n

@[target]
lemma asympBound_def {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b + sumTransform (p a b) g 0 n := by sorry

variable {g} {a} {b}

@[target]
lemma asympBound_def' {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b * (1 + (∑ u ∈ range n, g u / u ^ (p a b + 1))) := by sorry

section
include R

@[target]
lemma asympBound_pos (n : ℕ) (hn : 0 < n) : 0 < asympBound g a b n := by sorry

@[target]
lemma eventually_asympBound_pos : ∀ᶠ (n : ℕ) in atTop, 0 < asympBound g a b n := by sorry

@[target]
lemma eventually_asympBound_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < asympBound g a b (r i n) := by sorry

@[target]
lemma eventually_atTop_sumTransform_le :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ i, sumTransform (p a b) g (r i n) n ≤ c * g n := by sorry

@[target]
lemma eventually_atTop_sumTransform_ge :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ i, c * g n ≤ sumTransform (p a b) g (r i n) n := by sorry

end

/-!
#### Technical lemmas

The next several lemmas are technical lemmas leading up to `rpow_p_mul_one_sub_smoothingFn_le` and
`rpow_p_mul_one_add_smoothingFn_ge`, which are key steps in the main proof.
-/

lemma eventually_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    deriv (fun z => z ^ p * (1 - ε z))
      =ᶠ[atTop] fun z => p * z ^ (p-1) * (1 - ε z) + z ^ (p-1) / (log z ^ 2) := calc
  deriv (fun x => x ^ p * (1 - ε x))
    =ᶠ[atTop] fun x => deriv (· ^ p) x * (1 - ε x) + x ^ p * deriv (1 - ε ·) x := by
            filter_upwards [eventually_gt_atTop 1] with x hx
            rw [deriv_mul]
            · exact differentiableAt_rpow_const_of_ne _ (by positivity)
            · exact differentiableAt_one_sub_smoothingFn hx
  _ =ᶠ[atTop] fun x => p * x ^ (p-1) * (1 - ε x) + x ^ p * (x⁻¹ / (log x ^ 2)) := by
            filter_upwards [eventually_gt_atTop 1, eventually_deriv_one_sub_smoothingFn]
              with x hx hderiv
            rw [hderiv, Real.deriv_rpow_const (Or.inl <| by positivity)]
  _ =ᶠ[atTop] fun x => p * x ^ (p-1) * (1 - ε x) + x ^ (p-1) / (log x ^ 2) := by
            filter_upwards [eventually_gt_atTop 0] with x hx
            rw [mul_div, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity), sub_eq_add_neg]

@[target]
lemma eventually_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    deriv (fun z => z ^ p * (1 + ε z))
      =ᶠ[atTop] fun z => p * z ^ (p-1) * (1 + ε z) - z ^ (p-1) / (log z ^ 2) := by sorry

@[target]
lemma isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    deriv (fun z => z ^ p * (1 - ε z)) ~[atTop] fun z => p * z ^ (p-1) := by sorry

@[target]
lemma isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    deriv (fun z => z ^ p * (1 + ε z)) ~[atTop] fun z => p * z ^ (p-1) := by sorry

lemma isTheta_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖) =Θ[atTop] fun z => z ^ (p-1) := by
  refine IsTheta.norm_left ?_
  calc (fun x => deriv (fun z => z ^ p * (1 - ε z)) x) =Θ[atTop] fun z => p * z ^ (p-1) :=
            (isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn hp).isTheta
    _ =Θ[atTop] fun z => z ^ (p-1) :=
            IsTheta.const_mul_left hp <| isTheta_refl _ _

lemma isTheta_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖) =Θ[atTop] fun z => z ^ (p-1) := by
  refine IsTheta.norm_left ?_
  calc (fun x => deriv (fun z => z ^ p * (1 + ε z)) x) =Θ[atTop] fun z => p * z ^ (p-1) :=
            (isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn hp).isTheta
    _ =Θ[atTop] fun z => z ^ (p-1) :=
            IsTheta.const_mul_left hp <| isTheta_refl _ _

@[target]
lemma growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    GrowsPolynomially fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖ := by sorry

@[target]
lemma growsPolynomially_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    GrowsPolynomially fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖ := by sorry

@[target]
lemma isBigO_apply_r_sub_b (q : ℝ → ℝ) (hq_diff : DifferentiableOn ℝ q (Set.Ioi 1))
    (hq_poly : GrowsPolynomially fun x => ‖deriv q x‖) (i : α) :
    (fun n => q (r i n) - q (b i * n)) =O[atTop] fun n => (deriv q n) * (r i n - b i * n) := by sorry

@[target]
lemma rpow_p_mul_one_sub_smoothingFn_le :
    ∀ᶠ (n : ℕ) in atTop, ∀ i, (r i n) ^ (p a b) * (1 - ε (r i n))
      ≤ (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n) := by sorry

@[target]
lemma rpow_p_mul_one_add_smoothingFn_ge :
    ∀ᶠ (n : ℕ) in atTop, ∀ i, (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
      ≤ (r i n) ^ (p a b) * (1 + ε (r i n)) := by sorry

/-!
#### Main proof

This final section proves the Akra-Bazzi theorem.
-/

@[target]
lemma base_nonempty {n : ℕ} (hn : 0 < n) : (Finset.Ico (⌊b (min_bi b) / 2 * n⌋₊) n).Nonempty := by sorry

/-- The main proof of the upper bound part of the Akra-Bazzi theorem. The factor
`1 - ε n` does not change the asymptotic order, but is needed for the induction step to go
through. -/
@[target]
lemma T_isBigO_smoothingFn_mul_asympBound :
    T =O[atTop] (fun n => (1 - ε n) * asympBound g a b n) := by sorry

/-- The main proof of the lower bound part of the Akra-Bazzi theorem. The factor
`1 + ε n` does not change the asymptotic order, but is needed for the induction step to go
through. -/
@[target]
lemma smoothingFn_mul_asympBound_isBigO_T :
    (fun (n : ℕ) => (1 + ε n) * asympBound g a b n) =O[atTop] T := by sorry

/-- The **Akra-Bazzi theorem**: `T ∈ O(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
@[target]
theorem isBigO_asympBound : T =O[atTop] asympBound g a b := by sorry

/-- The **Akra-Bazzi theorem**: `T ∈ Ω(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
@[target]
theorem isBigO_symm_asympBound : asympBound g a b =O[atTop] T := by sorry

/-- The **Akra-Bazzi theorem**: `T ∈ Θ(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
@[target]
theorem isTheta_asympBound : T =Θ[atTop] asympBound g a b := by sorry

end AkraBazziRecurrence
