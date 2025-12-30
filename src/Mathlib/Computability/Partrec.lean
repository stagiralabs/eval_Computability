import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.Primrec
import Mathlib.Data.Nat.PSub
import Mathlib.Data.PFun

/-!
# The partial recursive functions

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `Part` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

open List (Vector)
open Encodable Denumerable Part

attribute [-simp] not_forall

namespace Nat

section Rfind

variable (p : ℕ →. Bool)

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, false ∈ p k

private def wf_lbp (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom) : WellFounded (lbp p) :=
  ⟨by
    let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction' m with m IH generalizing k <;> refine ⟨_, fun y r => ?_⟩ <;> rcases r with ⟨rfl, a⟩
    · injection mem_unique pn.1 (a _ kn)
    · exact IH _ (by rw [Nat.add_right_comm]; exact kn)⟩

variable (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom)

def rfindX : { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } :=
  suffices ∀ k, (∀ n < k, false ∈ p n) → { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } from
    this 0 fun _ => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ (lbp p) (wf_lbp p H)
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rcases lt_trichotomy m n with (h₃ | h₃ | h₃)
        · exact h₂ _ h₃
        · rw [h₃]
          exact h₁.fst
        · injection mem_unique h₁ (al _ h₃)
      cases e : (p m).get pm
      · suffices ∀ᵉ k ≤ m, false ∈ p k from IH _ ⟨rfl, this⟩ fun n h => this _ (le_of_lt_succ h)
        intro n h
        rcases h.lt_or_eq_dec with h | h
        · exact al _ h
        · rw [h]
          exact ⟨_, e⟩
      · exact ⟨m, ⟨_, e⟩, al⟩)

end Rfind

def rfind (p : ℕ →. Bool) : Part ℕ :=
  ⟨_, fun h => (rfindX p h).1⟩

@[target]
theorem rfind_spec {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : true ∈ p n := by sorry

@[target]
theorem rfind_min {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : ∀ {m : ℕ}, m < n → false ∈ p m := by sorry

@[target, simp]
theorem rfind_dom {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).Dom := by sorry

@[target]
theorem rfind_dom' {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).Dom := by sorry

@[target, simp]
theorem mem_rfind {p : ℕ →. Bool} {n : ℕ} :
    n ∈ rfind p ↔ true ∈ p n ∧ ∀ {m : ℕ}, m < n → false ∈ p m := by sorry

@[target]
theorem rfind_min' {p : ℕ → Bool} {m : ℕ} (pm : p m) : ∃ n ∈ rfind p, n ≤ m := by sorry

@[target]
theorem rfind_zero_none (p : ℕ →. Bool) (p0 : p 0 = Part.none) : rfind p = Part.none := by sorry

def rfindOpt {α} (f : ℕ → Option α) : Part α :=
  (rfind fun n => (f n).isSome).bind fun n => f n

@[target]
theorem rfindOpt_spec {α} {f : ℕ → Option α} {a} (h : a ∈ rfindOpt f) : ∃ n, a ∈ f n := by sorry

@[target]
theorem rfindOpt_dom {α} {f : ℕ → Option α} : (rfindOpt f).Dom ↔ ∃ n a, a ∈ f n := by sorry

@[target]
theorem rfindOpt_mono {α} {f : ℕ → Option α} (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n) {a} :
    a ∈ rfindOpt f ↔ ∃ n, a ∈ f n := by sorry

/-- `PartRec f` means that the partial function `f : ℕ → ℕ` is partially recursive. -/
inductive Partrec : (ℕ →. ℕ) → Prop
  | zero : Partrec (pure 0)
  | succ : Partrec succ
  | left : Partrec ↑fun n : ℕ => n.unpair.1
  | right : Partrec ↑fun n : ℕ => n.unpair.2
  | pair {f g} : Partrec f → Partrec g → Partrec fun n => pair <$> f n <*> g n
  | comp {f g} : Partrec f → Partrec g → Partrec fun n => g n >>= f
  | prec {f g} : Partrec f → Partrec g → Partrec (unpaired fun a n =>
      n.rec (f a) fun y IH => do let i ← IH; g (pair a (pair y i)))
  | rfind {f} : Partrec f → Partrec fun a => rfind fun n => (fun m => m = 0) <$> f (pair a n)

namespace Partrec

@[target]
theorem of_eq {f g : ℕ →. ℕ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g := by sorry

@[target]
theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Partrec g := by sorry

@[target]
theorem of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) : Partrec f := by sorry

protected theorem some : Partrec some :=
  of_primrec Primrec.id

@[target]
theorem none : Partrec fun _ => none := by sorry

@[target]
theorem prec' {f g h} (hf : Partrec f) (hg : Partrec g) (hh : Partrec h) :
    Partrec fun a => (f a).bind fun n => n.rec (g a)
      fun y IH => do {let i ← IH; h (Nat.pair a (Nat.pair y i))} := by sorry

@[target]
theorem ppred : Partrec fun n => ppred n := by sorry

end Partrec

end Nat

/-- Partially recursive partial functions `α → σ` between `Primcodable` types -/
def Partrec {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) :=
  Nat.Partrec fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

/-- Partially recursive partial functions `α → β → σ` between `Primcodable` types -/
def Partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β →. σ) :=
  Partrec fun p : α × β => f p.1 p.2

/-- Computable functions `α → σ` between `Primcodable` types:
  a function is computable if and only if it is partially recursive (as a partial function) -/
def Computable {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) :=
  Partrec (f : α →. σ)

/-- Computable functions `α → β → σ` between `Primcodable` types -/
def Computable₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Computable fun p : α × β => f p.1 p.2

@[target]
theorem Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {f : α → σ} (hf : Primrec f) :
    Computable f := by sorry

protected theorem Computable.partrec {α σ} [Primcodable α] [Primcodable σ] {f : α → σ}
    (hf : Computable f) : Partrec (f : α →. σ) :=
  hf

protected theorem Computable₂.partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Computable₂ f) : Partrec₂ fun a => (f a : β →. σ) :=
  hf

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

@[target]
theorem of_eq {f g : α → σ} (hf : Computable f) (H : ∀ n, f n = g n) : Computable g := by sorry

@[target]
theorem const (s : σ) : Computable fun _ : α => s := by sorry

@[target]
theorem ofOption {f : α → Option β} (hf : Computable f) : Partrec fun a => (f a : Part β) := by sorry

@[target]
theorem to₂ {f : α × β → σ} (hf : Computable f) : Computable₂ fun a b => f (a, b) := by sorry

protected theorem id : Computable (@id α) :=
  Primrec.id.to_comp

@[target]
theorem fst : Computable (@Prod.fst α β) := by sorry

@[target]
theorem snd : Computable (@Prod.snd α β) := by sorry

@[target]
theorem unpair : Computable Nat.unpair := by sorry

@[target]
theorem succ : Computable Nat.succ := by sorry

@[target]
theorem pred : Computable Nat.pred := by sorry

@[target]
theorem nat_bodd : Computable Nat.bodd := by sorry

@[target]
theorem nat_div2 : Computable Nat.div2 := by sorry

@[target]
theorem sumInl : Computable (@Sum.inl α β) := by sorry

theorem sumInr : Computable (@Sum.inr α β) :=
  Primrec.sumInr.to_comp

@[deprecated (since := "2025-02-21")] alias sum_inl := Computable.sumInl
@[deprecated (since := "2025-02-21")] alias sum_inr := Computable.sumInr

theorem list_cons : Computable₂ (@List.cons α) :=
  Primrec.list_cons.to_comp

@[target]
theorem list_reverse : Computable (@List.reverse α) := by sorry

@[target]
theorem list_get? : Computable₂ (@List.get? α) := by sorry

@[target]
theorem list_append : Computable₂ ((· ++ ·) : List α → List α → List α) := by sorry

@[target]
theorem list_concat : Computable₂ fun l (a : α) => l ++ [a] := by sorry

@[target]
theorem list_length : Computable (@List.length α) := by sorry

@[target]
theorem vector_cons {n} : Computable₂ (@List.Vector.cons α n) := by sorry

@[target]
theorem vector_toList {n} : Computable (@List.Vector.toList α n) := by sorry

@[target]
theorem vector_length {n} : Computable (@List.Vector.length α n) := by sorry

@[target]
theorem vector_head {n} : Computable (@List.Vector.head α n) := by sorry

@[target]
theorem vector_tail {n} : Computable (@List.Vector.tail α n) := by sorry

@[target]
theorem vector_get {n} : Computable₂ (@List.Vector.get α n) := by sorry

@[target]
theorem vector_ofFn' {n} : Computable (@List.Vector.ofFn α n) := by sorry

@[target]
theorem fin_app {n} : Computable₂ (@id (Fin n → σ)) := by sorry

protected theorem encode : Computable (@encode α _) :=
  Primrec.encode.to_comp

protected theorem decode : Computable (decode (α := α)) :=
  Primrec.decode.to_comp

protected theorem ofNat (α) [Denumerable α] : Computable (ofNat α) :=
  (Primrec.ofNat _).to_comp

@[target]
theorem encode_iff {f : α → σ} : (Computable fun a => encode (f a)) ↔ Computable f := by sorry

@[target]
theorem option_some : Computable (@Option.some α) := by sorry

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

open Computable

@[target]
theorem of_eq {f g : α →. σ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g := by sorry

@[target]
theorem of_eq_tot {f : α →. σ} {g : α → σ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Computable g := by sorry

@[target]
theorem none : Partrec fun _ : α => @Part.none σ := by sorry

protected theorem some : Partrec (@Part.some α) :=
  Computable.id

@[target]
theorem _root_.Decidable.Partrec.const' (s : Part σ) [Decidable s.Dom] : Partrec fun _ : α => s := by sorry

@[target]
theorem const' (s : Part σ) : Partrec fun _ : α => s := by sorry

protected theorem bind {f : α →. β} {g : α → β →. σ} (hf : Partrec f) (hg : Partrec₂ g) :
    Partrec fun a => (f a).bind (g a) :=
  (hg.comp (Nat.Partrec.some.pair hf)).of_eq fun n => by
    simp [Seq.seq]; rcases e : decode (α := α) n with - | a <;> simp [e, encodek]

@[target]
theorem map {f : α →. β} {g : α → β → σ} (hf : Partrec f) (hg : Computable₂ g) :
    Partrec fun a => (f a).map (g a) := by sorry

@[target]
theorem to₂ {f : α × β →. σ} (hf : Partrec f) : Partrec₂ fun a b => f (a, b) := by sorry

@[target]
theorem nat_rec {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ} (hf : Computable f) (hg : Partrec g)
    (hh : Partrec₂ h) : Partrec fun a => (f a).rec (g a) fun y IH => IH.bind fun i => h a (y, i) := by sorry

@[target]
theorem nat_iff {f : ℕ →. ℕ} : Partrec f ↔ Nat.Partrec f := by sorry

theorem map_encode_iff {f : α →. σ} : (Partrec fun a => (f a).map encode) ↔ Partrec f :=
  Iff.rfl

end Partrec

namespace Partrec₂

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

@[target]
theorem unpaired {f : ℕ → ℕ →. α} : Partrec (Nat.unpaired f) ↔ Partrec₂ f := by sorry

@[target]
theorem unpaired' {f : ℕ → ℕ →. ℕ} : Nat.Partrec (Nat.unpaired f) ↔ Partrec₂ f := by sorry

@[target]
theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ} (hf : Partrec₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Partrec₂ fun a b => f (g a b) (h a b) := by sorry

end Partrec₂

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

@[target]
nonrec theorem comp {f : β → σ} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f (g a) := by sorry

@[target]
theorem comp₂ {f : γ → σ} {g : α → β → γ} (hf : Computable f) (hg : Computable₂ g) :
    Computable₂ fun a b => f (g a b) := by sorry

end Computable

namespace Computable₂

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

@[target]
theorem mk {f : α → β → σ} (hf : Computable fun p : α × β => f p.1 p.2) : Computable₂ f := by sorry

@[target]
theorem comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Computable₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Computable₂ fun a b => f (g a b) (h a b) := by sorry

end Computable₂

namespace Partrec

variable {α : Type*} {σ : Type*} [Primcodable α] [Primcodable σ]

open Computable

@[target]
theorem rfind {p : α → ℕ →. Bool} (hp : Partrec₂ p) : Partrec fun a => Nat.rfind (p a) := by sorry

@[target]
theorem rfindOpt {f : α → ℕ → Option σ} (hf : Computable₂ f) :
    Partrec fun a => Nat.rfindOpt (f a) := by sorry

@[target]
theorem nat_casesOn_right {f : α → ℕ} {g : α → σ} {h : α → ℕ →. σ} (hf : Computable f)
    (hg : Computable g) (hh : Partrec₂ h) : Partrec fun a => (f a).casesOn (some (g a)) (h a) := by sorry

@[target]
theorem bind_decode₂_iff {f : α →. σ} :
    Partrec f ↔ Nat.Partrec fun n => Part.bind (decode₂ α n) fun a => (f a).map encode := by sorry

@[target]
theorem vector_mOfFn :
    ∀ {n} {f : Fin n → α →. σ},
      (∀ i, Partrec (f i)) → Partrec fun a : α => Vector.mOfFn fun i => f i a := by sorry

end Partrec

@[target, simp]
theorem Vector.mOfFn_part_some {α n} :
    ∀ f : Fin n → α,
      (List.Vector.mOfFn fun i => Part.some (f i)) = Part.some (List.Vector.ofFn f) := by sorry

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

@[target]
theorem option_some_iff {f : α → σ} : (Computable fun a => Option.some (f a)) ↔ Computable f := by sorry

@[target]
theorem bind_decode_iff {f : α → β → Option σ} :
    (Computable₂ fun a n => (decode (α := β) n).bind (f a)) ↔ Computable₂ f := by sorry

@[target]
theorem map_decode_iff {f : α → β → σ} :
    (Computable₂ fun a n => (decode (α := β) n).map (f a)) ↔ Computable₂ f := by sorry

@[target]
theorem nat_rec {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) :
    Computable fun a => Nat.rec (motive := fun _ => σ) (g a) (fun y IH => h a (y, IH)) (f a) := by sorry

@[target]
theorem nat_casesOn {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) :
    Computable fun a => Nat.casesOn (motive := fun _ => σ) (f a) (g a) (h a) := by sorry

@[target]
theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Computable c) (hf : Computable f)
    (hg : Computable g) : Computable fun a => cond (c a) (f a) (g a) := by sorry

@[target]
theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Computable o)
    (hf : Computable f) (hg : Computable₂ g) :
    @Computable _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) := by sorry

@[target]
theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).bind (g a) := by sorry

@[target]
theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) := by sorry

@[target]
theorem option_getD {f : α → Option β} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a).getD (g a) := by sorry

@[target]
theorem subtype_mk {f : α → β} {p : β → Prop} [DecidablePred p] {h : ∀ a, p (f a)}
    (hp : PrimrecPred p) (hf : Computable f) :
    @Computable _ _ _ (Primcodable.subtype hp) fun a => (⟨f a, h a⟩ : Subtype p) := by sorry

@[target]
theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Computable₂ h) :
    @Computable _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) := by sorry

@[deprecated (since := "2025-02-21")] alias sum_casesOn := sumCasesOn

@[target]
theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Computable₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = Option.some (f a n)) : Computable₂ f := by sorry

@[target]
theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ},
      (∀ i, Computable (f i)) → Computable fun a => List.ofFn fun i => f i a := by sorry

@[target]
theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Computable (f i)) :
    Computable fun a => List.Vector.ofFn fun i => f i a := by sorry

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

@[target]
theorem option_some_iff {f : α →. σ} : (Partrec fun a => (f a).map Option.some) ↔ Partrec f := by sorry

@[target]
theorem optionCasesOn_right {o : α → Option β} {f : α → σ} {g : α → β →. σ} (ho : Computable o)
    (hf : Computable f) (hg : Partrec₂ g) :
    @Partrec _ σ _ _ fun a => Option.casesOn (o a) (Part.some (f a)) (g a) := by sorry

@[deprecated (since := "2025-02-21")] alias option_casesOn_right := optionCasesOn_right

theorem sumCasesOn_right {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ →. σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Partrec₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (fun b => Part.some (g a b)) (h a) :=
  have :
    Partrec fun a =>
      (Option.casesOn (Sum.casesOn (f a) (fun _ => Option.none) Option.some : Option γ)
          (some (Sum.casesOn (f a) (fun b => some (g a b)) fun _ => Option.none)) fun c =>
          (h a c).map Option.some :
        Part (Option σ)) :=
    optionCasesOn_right (g := fun a n => Part.map Option.some (h a n))
      (sumCasesOn hf (const Option.none).to₂ (option_some.comp snd).to₂)
      (sumCasesOn (g := fun a n => Option.some (g a n)) hf (option_some.comp hg)
        (const Option.none).to₂)
      (option_some_iff.2 hh)
  option_some_iff.1 <| this.of_eq fun a => by cases f a <;> simp

@[target]
theorem sumCasesOn_left {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Computable₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) fun c => Part.some (h a c) := by sorry

@[deprecated (since := "2025-02-21")] alias sum_casesOn_left := sumCasesOn_left
@[deprecated (since := "2025-02-21")] alias sum_casesOn_right := sumCasesOn_right

theorem fix_aux {α σ} (f : α →. σ ⊕ α) (a : α) (b : σ) :
    let F : α → ℕ →. σ ⊕ α := fun a n =>
      n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
    (∃ n : ℕ,
        ((∃ b' : σ, Sum.inl b' ∈ F a n) ∧ ∀ {m : ℕ}, m < n → ∃ b : α, Sum.inr b ∈ F a m) ∧
          Sum.inl b ∈ F a n) ↔
      b ∈ PFun.fix f a := by
  intro F; refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨n, ⟨_x, h₁⟩, h₂⟩
    have : ∀ m a', Sum.inr a' ∈ F a m → b ∈ PFun.fix f a' → b ∈ PFun.fix f a := by
      intro m a' am ba
      induction' m with m IH generalizing a' <;> simp [F] at am
      · rwa [← am]
      rcases am with ⟨a₂, am₂, fa₂⟩
      exact IH _ am₂ (PFun.mem_fix_iff.2 (Or.inr ⟨_, fa₂, ba⟩))
    cases n <;> simp [F] at h₂
    rcases h₂ with (h₂ | ⟨a', am', fa'⟩)
    · obtain ⟨a', h⟩ := h₁ (Nat.lt_succ_self _)
      injection mem_unique h h₂
    · exact this _ _ am' (PFun.mem_fix_iff.2 (Or.inl fa'))
  · suffices ∀ a', b ∈ PFun.fix f a' → ∀ k, Sum.inr a' ∈ F a k →
        ∃ n, Sum.inl b ∈ F a n ∧ ∀ m < n, k ≤ m → ∃ a₂, Sum.inr a₂ ∈ F a m by
      rcases this _ h 0 (by simp [F]) with ⟨n, hn₁, hn₂⟩
      exact ⟨_, ⟨⟨_, hn₁⟩, fun {m} mn => hn₂ m mn (Nat.zero_le _)⟩, hn₁⟩
    intro a₁ h₁
    apply @PFun.fixInduction _ _ _ _ _ _ h₁
    intro a₂ h₂ IH k hk
    rcases PFun.mem_fix_iff.1 h₂ with (h₂ | ⟨a₃, am₃, _⟩)
    · refine ⟨k.succ, ?_, fun m mk km => ⟨a₂, ?_⟩⟩
      · simpa [F] using Or.inr ⟨_, hk, h₂⟩
      · rwa [le_antisymm (Nat.le_of_lt_succ mk) km]
    · rcases IH _ am₃ k.succ (by simpa [F] using ⟨_, hk, am₃⟩) with ⟨n, hn₁, hn₂⟩
      refine ⟨n, hn₁, fun m mn km => ?_⟩
      rcases km.lt_or_eq_dec with km | km
      · exact hn₂ _ mn km
      · exact km ▸ ⟨_, hk⟩

@[target]
theorem fix {f : α →. σ ⊕ α} (hf : Partrec f) : Partrec (PFun.fix f) := by sorry

end Partrec
