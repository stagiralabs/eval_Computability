import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Set.Subsingleton

/-!
# Computability theory and the halting problem

A universal partial recursive function, Rice's theorem, and the halting problem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

open List (Vector)
open Encodable Denumerable

namespace Nat.Partrec

open Computable Part

@[target]
theorem merge' {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g) :
    ∃ h, Nat.Partrec h ∧
      ∀ a, (∀ x ∈ h a, x ∈ f a ∨ x ∈ g a) ∧ ((h a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by sorry

end Nat.Partrec

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable Part

open Nat.Partrec (Code)

open Nat.Partrec.Code

@[target]
theorem merge' {f g : α →. σ} (hf : Partrec f) (hg : Partrec g) :
    ∃ k : α →. σ,
      Partrec k ∧ ∀ a, (∀ x ∈ k a, x ∈ f a ∨ x ∈ g a) ∧ ((k a).Dom ↔ (f a).Dom ∨ (g a).Dom) := by sorry

@[target]
theorem merge {f g : α →. σ} (hf : Partrec f) (hg : Partrec g)
    (H : ∀ (a), ∀ x ∈ f a, ∀ y ∈ g a, x = y) :
    ∃ k : α →. σ, Partrec k ∧ ∀ a x, x ∈ k a ↔ x ∈ f a ∨ x ∈ g a := by sorry

@[target]
theorem cond {c : α → Bool} {f : α →. σ} {g : α →. σ} (hc : Computable c) (hf : Partrec f)
    (hg : Partrec g) : Partrec fun a => cond (c a) (f a) (g a) := by sorry

-- Deprecated alias removed as the target is sorried
-- @[deprecated (since := "2025-02-21")] alias sum_casesOn := Partrec.sumCasesOn

end Partrec

/-- A computable predicate is one whose indicator function is computable. -/
def ComputablePred {α} [Primcodable α] (p : α → Prop) :=
  ∃ _ : DecidablePred p, Computable fun a => decide (p a)

/-- A recursively enumerable predicate is one which is the domain of a computable partial function.
-/
def REPred {α} [Primcodable α] (p : α → Prop) :=
  Partrec fun a => Part.assert (p a) fun _ => Part.some ()

@[deprecated (since := "2025-02-06")] alias RePred := REPred

@[deprecated (since := "2025-02-06")] alias RePred.of_eq := RePred

theorem REPred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : REPred p) (H : ∀ a, p a ↔ q a) :
    REPred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

@[target]
theorem Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α →. β} (h : Partrec f) :
    REPred fun a => (f a).Dom := by sorry

theorem ComputablePred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : ComputablePred p)
    (H : ∀ a, p a ↔ q a) : ComputablePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

namespace ComputablePred

variable {α : Type*} [Primcodable α]

open Nat.Partrec (Code)

open Nat.Partrec.Code Computable

@[target]
theorem computable_iff {p : α → Prop} :
    ComputablePred p ↔ ∃ f : α → Bool, Computable f ∧ p = fun a => (f a : Prop) := by sorry

protected theorem not {p : α → Prop} (hp : ComputablePred p) : ComputablePred fun a => ¬p a := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  exact
    ⟨by infer_instance,
      (cond hf (const false) (const true)).of_eq fun n => by
        simp only [Bool.not_eq_true]
        cases f n <;> rfl⟩

/-- The computable functions are closed under if-then-else definitions
with computable predicates. -/
@[target]
theorem ite {f₁ f₂ : ℕ → ℕ} (hf₁ : Computable f₁) (hf₂ : Computable f₂)
    {c : ℕ → Prop} [DecidablePred c] (hc : ComputablePred c) :
    Computable fun k ↦ if c k then f₁ k else f₂ k := by sorry

theorem to_re {p : α → Prop} (hp : ComputablePred p) : REPred p := by
  obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp
  unfold REPred
  dsimp only []
  refine
    (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n =>
      Part.ext fun a => ?_
  cases a; cases f n <;> simp

/-- **Rice's Theorem** -/
@[target]
theorem rice (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c => eval c ∈ C) {f g} (hf : Nat.Partrec f)
    (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C := by sorry

@[target]
theorem rice₂ (C : Set Code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ := by sorry

/-- The Halting problem is recursively enumerable -/
@[target]
theorem halting_problem_re (n) : REPred fun c => (eval c n).Dom := by sorry

/-- The **Halting problem** is not computable -/
@[target]
theorem halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom := by sorry

@[target]
theorem computable_iff_re_compl_re {p : α → Prop} [DecidablePred p] :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a := by sorry

@[target]
theorem computable_iff_re_compl_re' {p : α → Prop} :
    ComputablePred p ↔ REPred p ∧ REPred fun a => ¬p a := by sorry

theorem halting_problem_not_re (n) : ¬REPred fun c => ¬(eval c n).Dom
  | h => halting_problem _ <| computable_iff_re_compl_re'.2 ⟨halting_problem_re _, h⟩

end ComputablePred

namespace Nat

open Vector Part

/-- A simplified basis for `Partrec`. -/
inductive Partrec' : ∀ {n}, (List.Vector ℕ n →. ℕ) → Prop
  | prim {n f} : @Primrec' n f → @Partrec' n f
  | comp {m n f} (g : Fin n → List.Vector ℕ m →. ℕ) :
    Partrec' f → (∀ i, Partrec' (g i)) →
      Partrec' fun v => (List.Vector.mOfFn fun i => g i v) >>= f
  | rfind {n} {f : List.Vector ℕ (n + 1) → ℕ} :
    @Partrec' (n + 1) f → Partrec' fun v => rfind fun n => some (f (n ::ᵥ v) = 0)

end Nat

namespace Nat.Partrec'

open List.Vector Partrec Computable

open Nat.Partrec'

@[target]
theorem to_part {n f} (pf : @Partrec' n f) : _root_.Partrec f := by sorry

@[target]
theorem of_eq {n} {f g : List.Vector ℕ n →. ℕ} (hf : Partrec' f) (H : ∀ i, f i = g i) :
    Partrec' g := by sorry

theorem of_prim {n} {f : List.Vector ℕ n → ℕ} (hf : Primrec f) : @Partrec' n f :=
  prim (Nat.Primrec'.of_prim hf)

@[target]
theorem head {n : ℕ} : @Partrec' n.succ (@head ℕ n) := by sorry

@[target]
theorem tail {n f} (hf : @Partrec' n f) : @Partrec' n.succ fun v => f v.tail := by sorry

protected theorem bind {n f g} (hf : @Partrec' n f) (hg : @Partrec' (n + 1) g) :
    @Partrec' n fun v => (f v).bind fun a => g (a ::ᵥ v) :=
  (@comp n (n + 1) g (fun i => Fin.cases f (fun i v => some (v.get i)) i) hg fun i => by
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [*]
      exact prim (Nat.Primrec'.get _)).of_eq
    fun v => by simp [mOfFn, Part.bind_assoc, pure]

protected theorem map {n f} {g : List.Vector ℕ (n + 1) → ℕ} (hf : @Partrec' n f)
    (hg : @Partrec' (n + 1) g) : @Partrec' n fun v => (f v).map fun a => g (a ::ᵥ v) := by
  simpa [(Part.bind_some_eq_map _ _).symm] using hf.bind hg

/-- Analogous to `Nat.Partrec'` for `ℕ`-valued functions, a predicate for partial recursive
  vector-valued functions. -/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) :=
  ∀ i, Partrec' fun v => (f v).get i

nonrec theorem Vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : Vec f := fun i => prim <| hf i

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

protected theorem cons {n m} {f : List.Vector ℕ n → ℕ} {g} (hf : @Partrec' n f)
    (hg : @Vec n m g) : Vec fun v => f v ::ᵥ g v := fun i =>
  Fin.cases (by simpa using hf) (fun i => by simp only [hg i, get_cons_succ]) i

@[target]
theorem idv {n} : @Vec n n id := by sorry

@[target]
theorem comp' {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g) : Partrec' fun v => f (g v) := by sorry

theorem comp₁ {n} (f : ℕ →. ℕ) {g : List.Vector ℕ n → ℕ} (hf : @Partrec' 1 fun v => f v.head)
    (hg : @Partrec' n g) : @Partrec' n fun v => f (g v) := by
  simpa using hf.comp' (Partrec'.cons hg Partrec'.nil)

@[target]
theorem rfindOpt {n} {f : List.Vector ℕ (n + 1) → ℕ} (hf : @Partrec' (n + 1) f) :
    @Partrec' n fun v => Nat.rfindOpt fun a => ofNat (Option ℕ) (f (a ::ᵥ v)) := by sorry

open Nat.Partrec.Code

@[target]
theorem of_part : ∀ {n f}, _root_.Partrec f → @Partrec' n f := by sorry

@[target]
theorem part_iff {n f} : @Partrec' n f ↔ _root_.Partrec f := by sorry

@[target]
theorem part_iff₁ {f : ℕ →. ℕ} : (@Partrec' 1 fun v => f v.head) ↔ _root_.Partrec f := by sorry

@[target]
theorem part_iff₂ {f : ℕ → ℕ →. ℕ} : (@Partrec' 2 fun v => f v.head v.tail.head) ↔ Partrec₂ f := by sorry

@[target]
theorem vec_iff {m n f} : @Vec m n f ↔ Computable f := by sorry

end Nat.Partrec'
