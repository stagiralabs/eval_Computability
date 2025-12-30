import VerifiedAgora.tagger
/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro
-/
import Mathlib.Computability.Halting

/-!
# Strong reducibility and degrees.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notations

This file uses the local notation `⊕'` for `Sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/


universe u v w

open Function

/--
`p` is many-one reducible to `q` if there is a computable function translating questions about `p`
to questions about `q`.
-/
def ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ ∀ a, p a ↔ q (f a)

@[inherit_doc ManyOneReducible]
infixl:1000 " ≤₀ " => ManyOneReducible

@[target]
theorem ManyOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) : (fun a => q (f a)) ≤₀ q := by sorry

@[target, refl]
theorem manyOneReducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₀ p := by sorry

@[target, trans]
theorem ManyOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ q → q ≤₀ r → p ≤₀ r := by sorry

@[target]
theorem reflexive_manyOneReducible {α} [Primcodable α] : Reflexive (@ManyOneReducible α α _ _) := by sorry

@[target]
theorem transitive_manyOneReducible {α} [Primcodable α] : Transitive (@ManyOneReducible α α _ _) := by sorry

/--
`p` is one-one reducible to `q` if there is an injective computable function translating questions
about `p` to questions about `q`.
-/
def OneOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ Injective f ∧ ∀ a, p a ↔ q (f a)

@[inherit_doc OneOneReducible]
infixl:1000 " ≤₁ " => OneOneReducible

@[target]
theorem OneOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) (i : Injective f) : (fun a => q (f a)) ≤₁ q := by sorry

@[target, refl]
theorem oneOneReducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₁ p := by sorry

@[trans]
theorem OneOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : p ≤₁ q → q ≤₁ r → p ≤₁ r
  | ⟨f, c₁, i₁, h₁⟩, ⟨g, c₂, i₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, i₂.comp i₁, fun a =>
      ⟨fun h => by erw [← h₂, ← h₁]; assumption, fun h => by rwa [h₁, h₂]⟩⟩

theorem OneOneReducible.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ q → p ≤₀ q
  | ⟨f, c, _, h⟩ => ⟨f, c, h⟩

@[target]
theorem OneOneReducible.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β → Prop)
    (h : Computable e) : (q ∘ e) ≤₁ q := by sorry

@[target]
theorem OneOneReducible.of_equiv_symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
    (q : β → Prop) (h : Computable e.symm) : q ≤₁ (q ∘ e) := by sorry

@[target]
theorem reflexive_oneOneReducible {α} [Primcodable α] : Reflexive (@OneOneReducible α α _ _) := by sorry

@[target]
theorem transitive_oneOneReducible {α} [Primcodable α] : Transitive (@OneOneReducible α α _ _) := by sorry

namespace ComputablePred

variable {α : Type*} {β : Type*} [Primcodable α] [Primcodable β]

open Computable

@[target]
theorem computable_of_manyOneReducible {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q)
    (h₂ : ComputablePred q) : ComputablePred p := by sorry

@[target]
theorem computable_of_oneOneReducible {p : α → Prop} {q : β → Prop} (h : p ≤₁ q) :
    ComputablePred q → ComputablePred p := by sorry

end ComputablePred

/-- `p` and `q` are many-one equivalent if each one is many-one reducible to the other. -/
def ManyOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₀ q ∧ q ≤₀ p

/-- `p` and `q` are one-one equivalent if each one is one-one reducible to the other. -/
def OneOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₁ q ∧ q ≤₁ p

@[target, refl]
theorem manyOneEquiv_refl {α} [Primcodable α] (p : α → Prop) : ManyOneEquiv p p := by sorry

@[target, symm]
theorem ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    ManyOneEquiv p q → ManyOneEquiv q p := by sorry

@[target, trans]
theorem ManyOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : ManyOneEquiv p q → ManyOneEquiv q r → ManyOneEquiv p r := by sorry

@[target]
theorem equivalence_of_manyOneEquiv {α} [Primcodable α] : Equivalence (@ManyOneEquiv α α _ _) := by sorry

@[target, refl]
theorem oneOneEquiv_refl {α} [Primcodable α] (p : α → Prop) : OneOneEquiv p p := by sorry

@[target, symm]
theorem OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    OneOneEquiv p q → OneOneEquiv q p := by sorry

@[target, trans]
theorem OneOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : OneOneEquiv p q → OneOneEquiv q r → OneOneEquiv p r := by sorry

@[target]
theorem equivalence_of_oneOneEquiv {α} [Primcodable α] : Equivalence (@OneOneEquiv α α _ _) := by sorry

@[target]
theorem OneOneEquiv.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : OneOneEquiv p q → ManyOneEquiv p q := by sorry

/-- a computable bijection -/
nonrec def Equiv.Computable {α β} [Primcodable α] [Primcodable β] (e : α ≃ β) :=
  Computable e ∧ Computable e.symm

@[target]
theorem Equiv.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} :
    e.Computable → e.symm.Computable := by sorry

@[target]
theorem Equiv.Computable.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}
    {e₂ : β ≃ γ} : e₁.Computable → e₂.Computable → (e₁.trans e₂).Computable := by sorry

@[target]
theorem Computable.eqv (α) [Denumerable α] : (Denumerable.eqv α).Computable := by sorry

@[target]
theorem Computable.equiv₂ (α β) [Denumerable α] [Denumerable β] :
    (Denumerable.equiv₂ α β).Computable := by sorry

theorem OneOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : OneOneEquiv (p ∘ e) p :=
  ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩

@[target]
theorem ManyOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : ManyOneEquiv (p ∘ e) p := by sorry

@[target]
theorem ManyOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) : p ≤₀ r ↔ q ≤₀ r := by sorry

@[target]
theorem ManyOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) : p ≤₀ q ↔ p ≤₀ r := by sorry

@[target]
theorem OneOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) : p ≤₁ r ↔ q ≤₁ r := by sorry

@[target]
theorem OneOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) : p ≤₁ q ↔ p ≤₁ r := by sorry

@[target]
theorem ManyOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) :
    ManyOneEquiv p r ↔ ManyOneEquiv q r := by sorry

@[target]
theorem ManyOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) :
    ManyOneEquiv p q ↔ ManyOneEquiv p r := by sorry

@[target]
theorem OneOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) :
    OneOneEquiv p r ↔ OneOneEquiv q r := by sorry

theorem OneOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) :
    OneOneEquiv p q ↔ OneOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left

@[target, simp]
theorem ULower.down_computable {α} [Primcodable α] : (ULower.equiv α).Computable := by sorry

@[target]
theorem manyOneEquiv_up {α} [Primcodable α] {p : α → Prop} : ManyOneEquiv (p ∘ ULower.up) p := by sorry

local infixl:1001 " ⊕' " => Sum.elim

open Nat.Primrec

@[target]
theorem OneOneReducible.disjoin_left {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ p ⊕' q := by sorry

@[target]
theorem OneOneReducible.disjoin_right {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : q ≤₁ p ⊕' q := by sorry

@[target]
theorem disjoin_manyOneReducible {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ r → q ≤₀ r → (p ⊕' q) ≤₀ r := by sorry

@[target]
theorem disjoin_le {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : (p ⊕' q) ≤₀ r ↔ p ≤₀ r ∧ q ≤₀ r := by sorry

variable {α : Type u} [Primcodable α] [Inhabited α] {β : Type v} [Primcodable β] [Inhabited β]

/-- Computable and injective mapping of predicates to sets of natural numbers.
-/
def toNat (p : Set α) : Set ℕ :=
  { n | p ((Encodable.decode (α := α) n).getD default) }

@[target, simp]
theorem toNat_manyOneReducible {p : Set α} : toNat p ≤₀ p := by sorry

@[target, simp]
theorem manyOneReducible_toNat {p : Set α} : p ≤₀ toNat p := by sorry

@[target, simp]
theorem manyOneReducible_toNat_toNat {p : Set α} {q : Set β} : toNat p ≤₀ toNat q ↔ p ≤₀ q := by sorry

@[target, simp]
theorem toNat_manyOneEquiv {p : Set α} : ManyOneEquiv (toNat p) p := by sorry

@[target, simp]
theorem manyOneEquiv_toNat (p : Set α) (q : Set β) :
    ManyOneEquiv (toNat p) (toNat q) ↔ ManyOneEquiv p q := by sorry

/-- A many-one degree is an equivalence class of sets up to many-one equivalence. -/
def ManyOneDegree : Type :=
  Quotient (⟨ManyOneEquiv, equivalence_of_manyOneEquiv⟩ : Setoid (Set ℕ))

namespace ManyOneDegree

/-- The many-one degree of a set on a primcodable type. -/
def of (p : α → Prop) : ManyOneDegree :=
  Quotient.mk'' (toNat p)

@[elab_as_elim]
protected theorem ind_on {C : ManyOneDegree → Prop} (d : ManyOneDegree)
    (h : ∀ p : Set ℕ, C (of p)) : C d :=
  Quotient.inductionOn' d h

/-- Lifts a function on sets of natural numbers to many-one degrees. -/
protected abbrev liftOn {φ} (d : ManyOneDegree) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : φ :=
  Quotient.liftOn' d f h

@[simp]
protected theorem liftOn_eq {φ} (p : Set ℕ) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : (of p).liftOn f h = f p :=
  rfl

/-- Lifts a binary function on sets of natural numbers to many-one degrees. -/
@[reducible, simp]
protected def liftOn₂ {φ} (d₁ d₂ : ManyOneDegree) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) : φ :=
  d₁.liftOn (fun p => d₂.liftOn (f p) fun _ _ hq => h _ _ _ _ (by rfl) hq)
    (by
      intro p₁ p₂ hp
      induction d₂ using ManyOneDegree.ind_on
      apply h
      · assumption
      · rfl)

@[simp]
protected theorem liftOn₂_eq {φ} (p q : Set ℕ) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) :
    (of p).liftOn₂ (of q) f h = f p q :=
  rfl

@[target, simp]
theorem of_eq_of {p : α → Prop} {q : β → Prop} : of p = of q ↔ ManyOneEquiv p q := by sorry

instance instInhabited : Inhabited ManyOneDegree :=
  ⟨of (∅ : Set ℕ)⟩

/-- For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one reducible to the
sets in `d₂`.
-/
instance instLE : LE ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    ManyOneDegree.liftOn₂ d₁ d₂ (· ≤₀ ·) fun _p₁ _p₂ _q₁ _q₂ hp hq =>
      propext (hp.le_congr_left.trans hq.le_congr_right)⟩

@[target, simp]
theorem of_le_of {p : α → Prop} {q : β → Prop} : of p ≤ of q ↔ p ≤₀ q := by sorry

private theorem le_refl (d : ManyOneDegree) : d ≤ d := by
  induction d using ManyOneDegree.ind_on; simp; rfl

private theorem le_antisymm {d₁ d₂ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  intro hp hq
  simp_all only [ManyOneEquiv, of_le_of, of_eq_of, true_and]

private theorem le_trans {d₁ d₂ d₃ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  apply ManyOneReducible.trans

instance instPartialOrder : PartialOrder ManyOneDegree where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

/-- The join of two degrees, induced by the disjoint union of two underlying sets. -/
instance instAdd : Add ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    d₁.liftOn₂ d₂ (fun a b => of (a ⊕' b))
      (by
        rintro a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩
        rw [of_eq_of]
        exact
          ⟨disjoin_manyOneReducible (hl₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hl₂.trans OneOneReducible.disjoin_right.to_many_one),
            disjoin_manyOneReducible (hr₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hr₂.trans OneOneReducible.disjoin_right.to_many_one)⟩)⟩

@[target, simp]
theorem add_of (p : Set α) (q : Set β) : of (p ⊕' q) = of p + of q := by sorry

@[simp]
protected theorem add_le {d₁ d₂ d₃ : ManyOneDegree} : d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  simpa only [← add_of, of_le_of] using disjoin_le

@[simp]
protected theorem le_add_left (d₁ d₂ : ManyOneDegree) : d₁ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (le_refl _)).1

@[simp]
protected theorem le_add_right (d₁ d₂ : ManyOneDegree) : d₂ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (le_refl _)).2

instance instSemilatticeSup : SemilatticeSup ManyOneDegree :=
  { ManyOneDegree.instPartialOrder with
    sup := (· + ·)
    le_sup_left := ManyOneDegree.le_add_left
    le_sup_right := ManyOneDegree.le_add_right
    sup_le := fun _ _ _ h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }

end ManyOneDegree
