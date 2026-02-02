import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Function.Iterate

/-!
# The primitive recursive functions

The primitive recursive functions are the least collection of functions
`ℕ → ℕ` which are closed under projections (using the `pair`
pairing function), composition, zero, successor, and primitive recursion
(i.e. `Nat.rec` where the motive is `C n := ℕ`).

We can extend this definition to a large class of basic types by
using canonical encodings of types as natural numbers (Gödel numbering),
which we implement through the type class `Encodable`. (More precisely,
we need that the composition of encode with decode yields a
primitive recursive function, so we have the `Primcodable` type class
for this.)

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

open List (Vector)
open Denumerable Encodable Function

namespace Nat

/-- Calls the given function on a pair of entries `n`, encoded via the pairing function. -/
@[simp, reducible]
def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f n.unpair.1 n.unpair.2

/-- The primitive recursive functions `ℕ → ℕ`. -/
protected inductive Primrec : (ℕ → ℕ) → Prop
  | zero : Nat.Primrec fun _ => 0
  | protected succ : Nat.Primrec succ
  | left : Nat.Primrec fun n => n.unpair.1
  | right : Nat.Primrec fun n => n.unpair.2
  | pair {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => pair (f n) (g n)
  | comp {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => f (g n)
  | prec {f g} :
      Nat.Primrec f →
        Nat.Primrec g →
          Nat.Primrec (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

namespace Primrec

@[target]
theorem of_eq {f g : ℕ → ℕ} (hf : Nat.Primrec f) (H : ∀ n, f n = g n) : Nat.Primrec g := by sorry

@[target]
theorem const : ∀ n : ℕ, Nat.Primrec fun _ => n := by sorry

@[target]

protected theorem id : Nat.Primrec id :=
  (left.pair right).of_eq fun n => by simp

@[target]
theorem prec1 {f} (m : ℕ) (hf : Nat.Primrec f) :
    Nat.Primrec fun n => n.rec m fun y IH => f <| Nat.pair y IH := by sorry

@[target]
theorem casesOn1 {f} (m : ℕ) (hf : Nat.Primrec f) : Nat.Primrec (Nat.casesOn · m f) := by sorry

@[target]
theorem casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair z y) := by sorry

protected theorem swap : Nat.Primrec (unpaired (swap Nat.pair)) :=
  (pair right left).of_eq fun n => by simp

theorem swap' {f} (hf : Nat.Primrec (unpaired f)) : Nat.Primrec (unpaired (swap f)) :=
  (hf.comp .swap).of_eq fun n => by simp

@[target]
theorem pred : Nat.Primrec pred := by sorry

@[target]
theorem add : Nat.Primrec (unpaired (· + ·)) := by sorry

@[target]
theorem sub : Nat.Primrec (unpaired (· - ·)) := by sorry

@[target]
theorem mul : Nat.Primrec (unpaired (· * ·)) := by sorry

@[target]
theorem pow : Nat.Primrec (unpaired (· ^ ·)) := by sorry

end Primrec

end Nat

/-- A `Primcodable` type is an `Encodable` type for which
  the encode/decode functions are primitive recursive. -/
class Primcodable (α : Type*) extends Encodable α where
  -- Porting note: was `prim [] `.
  -- This means that `prim` does not take the type explicitly in Lean 4
  prim : Nat.Primrec fun n => Encodable.encode (decode n)

namespace Primcodable

open Nat.Primrec

instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α :=
  ⟨Nat.Primrec.succ.of_eq <| by simp⟩

/-- Builds a `Primcodable` instance from an equivalence to a `Primcodable` type. -/
@[target]
def ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β :=
  { __ := Encodable.ofEquiv α e
    prim := (@Primcodable.prim α _).of_eq fun n => by
      rw [decode_ofEquiv]
      cases (@decode α _ n) <;>
        simp [encode_ofEquiv] }

instance empty : Primcodable Empty :=
  ⟨zero⟩

instance unit : Primcodable PUnit :=
  ⟨(casesOn1 1 zero).of_eq fun n => by cases n <;> simp⟩

instance option {α : Type*} [h : Primcodable α] : Primcodable (Option α) :=
  ⟨(casesOn1 1 ((casesOn1 0 (.comp .succ .succ)).comp (@Primcodable.prim α _))).of_eq fun n => by
    cases n with
      | zero => rfl
      | succ n =>
        rw [decode_option_succ]
        cases H : @decode α _ n <;> simp [H]⟩

instance bool : Primcodable Bool :=
  ⟨(casesOn1 1 (casesOn1 2 zero)).of_eq fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) => by rw [decode_ge_two] <;> simp⟩

end Primcodable

/-- `Primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
def Primrec {α β} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Nat.Primrec fun n => encode ((@decode α _ n).map f)

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

@[target]

protected theorem encode : Primrec (@encode α _) :=
  (@Primcodable.prim α _).of_eq fun n => by cases @decode α _ n <;> rfl

@[target]

protected theorem decode : Primrec (@decode α _) :=
  Nat.Primrec.succ.comp (@Primcodable.prim α _)

@[target]
theorem dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n)) := by sorry

@[target]
theorem nat_iff {f : ℕ → ℕ} : Primrec f ↔ Nat.Primrec f := by sorry

@[target]
theorem encdec : Primrec fun n => encode (@decode α _ n) := by sorry

@[target]
theorem option_some : Primrec (@some α) := by sorry

@[target]
theorem of_eq {f g : α → σ} (hf : Primrec f) (H : ∀ n, f n = g n) : Primrec g := by sorry

@[target]
theorem const (x : σ) : Primrec fun _ : α => x := by sorry

protected theorem id : Primrec (@id α) :=
  (@Primcodable.prim α).of_eq <| by simp

@[target]
theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) := by sorry

@[target]
theorem succ : Primrec Nat.succ := by sorry

@[target]
theorem pred : Primrec Nat.pred := by sorry

@[target]
theorem encode_iff {f : α → σ} : (Primrec fun a => encode (f a)) ↔ Primrec f := by sorry

@[target]
theorem ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Primrec fun n => f (ofNat α n) := by sorry

@[target]

protected theorem ofNat (α) [Denumerable α] : Primrec (ofNat α) :=
  ofNat_iff.1 Primrec.id

@[target]
theorem option_some_iff {f : α → σ} : (Primrec fun a => some (f a)) ↔ Primrec f := by sorry

@[target]
theorem of_equiv {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e := by sorry

@[target]
theorem of_equiv_symm {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e.symm := by sorry

@[target]
theorem of_equiv_iff {β} (e : β ≃ α) {f : σ → β} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f := by sorry

@[target]
theorem of_equiv_symm_iff {β} (e : β ≃ α) {f : σ → α} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f := by sorry

end Primrec

namespace Primcodable

open Nat.Primrec

instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) :=
  ⟨((casesOn' zero ((casesOn' zero .succ).comp (pair right ((@Primcodable.prim β).comp left)))).comp
          (pair right ((@Primcodable.prim α).comp left))).of_eq
      fun n => by
      simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
      cases @decode α _ n.unpair.1; · simp
      cases @decode β _ n.unpair.2 <;> simp⟩

end Primcodable

namespace Primrec

variable {α : Type*} [Primcodable α]

open Nat.Primrec

@[target]
theorem fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.fst α β) := by sorry

@[target]
theorem snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.snd α β) := by sorry

@[target]
theorem pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => (f a, g a) := by sorry

@[target]
theorem unpair : Primrec Nat.unpair := by sorry

@[target]
theorem list_get?₁ : ∀ l : List α, Primrec l.get? := by sorry

end Primrec

/-- `Primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
def Primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Primrec fun p : α × β => f p.1 p.2

/-- `PrimrecPred p` means `p : α → Prop` is a (decidable)
  primitive recursive predicate, which is to say that
  `decide ∘ p : α → Bool` is primitive recursive. -/
def PrimrecPred {α} [Primcodable α] (p : α → Prop) [DecidablePred p] :=
  Primrec fun a => decide (p a)

/-- `PrimrecRel p` means `p : α → β → Prop` is a (decidable)
  primitive recursive relation, which is to say that
  `decide ∘ p : α → β → Bool` is primitive recursive. -/
def PrimrecRel {α β} [Primcodable α] [Primcodable β] (s : α → β → Prop)
    [∀ a b, Decidable (s a b)] :=
  Primrec₂ fun a b => decide (s a b)

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

@[target]
theorem mk {f : α → β → σ} (hf : Primrec fun p : α × β => f p.1 p.2) : Primrec₂ f := by sorry

@[target]
theorem of_eq {f g : α → β → σ} (hg : Primrec₂ f) (H : ∀ a b, f a b = g a b) : Primrec₂ g := by sorry

@[target]
theorem const (x : σ) : Primrec₂ fun (_ : α) (_ : β) => x := by sorry

protected theorem pair : Primrec₂ (@Prod.mk α β) :=
  Primrec.pair .fst .snd

@[target]
theorem left : Primrec₂ fun (a : α) (_ : β) => a := by sorry

@[target]
theorem right : Primrec₂ fun (_ : α) (b : β) => b := by sorry

@[target]
theorem natPair : Primrec₂ Nat.pair := by sorry

@[target]
theorem unpaired {f : ℕ → ℕ → α} : Primrec (Nat.unpaired f) ↔ Primrec₂ f := by sorry

@[target]
theorem unpaired' {f : ℕ → ℕ → ℕ} : Nat.Primrec (Nat.unpaired f) ↔ Primrec₂ f := by sorry

@[target]
theorem encode_iff {f : α → β → σ} : (Primrec₂ fun a b => encode (f a b)) ↔ Primrec₂ f := by sorry

@[target]
theorem option_some_iff {f : α → β → σ} : (Primrec₂ fun a b => some (f a b)) ↔ Primrec₂ f := by sorry

@[target]
theorem ofNat_iff {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α → β → σ} :
    Primrec₂ f ↔ Primrec₂ fun m n : ℕ => f (ofNat α m) (ofNat β n) := by sorry

@[target]
theorem uncurry {f : α → β → σ} : Primrec (Function.uncurry f) ↔ Primrec₂ f := by sorry

@[target]
theorem curry {f : α × β → σ} : Primrec₂ (Function.curry f) ↔ Primrec f := by sorry

end Primrec₂

section Comp

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem Primrec.comp₂ {f : γ → σ} {g : α → β → γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a b => f (g a b) :=
  hf.comp hg

@[target]
theorem Primrec₂.comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Primrec₂ f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => f (g a) (h a) := by sorry

@[target]
theorem Primrec₂.comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Primrec₂ f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fun a b => f (g a b) (h a b) := by sorry

@[target]
theorem PrimrecPred.comp {p : β → Prop} [DecidablePred p] {f : α → β} :
    PrimrecPred p → Primrec f → PrimrecPred fun a => p (f a) := by sorry

@[target]
theorem PrimrecRel.comp {R : β → γ → Prop} [∀ a b, Decidable (R a b)] {f : α → β} {g : α → γ} :
    PrimrecRel R → Primrec f → Primrec g → PrimrecPred fun a => R (f a) (g a) := by sorry

@[target]
theorem PrimrecRel.comp₂ {R : γ → δ → Prop} [∀ a b, Decidable (R a b)] {f : α → β → γ}
    {g : α → β → δ} :
    PrimrecRel R → Primrec₂ f → Primrec₂ g → PrimrecRel fun a b => R (f a b) (g a b) := by sorry

end Comp

@[target]
theorem PrimrecPred.of_eq {α} [Primcodable α] {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecPred p) (H : ∀ a, p a ↔ q a) : PrimrecPred q := by sorry

@[target]
theorem PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β] {r s : α → β → Prop}
    [∀ a b, Decidable (r a b)] [∀ a b, Decidable (s a b)] (hr : PrimrecRel r)
    (H : ∀ a b, r a b ↔ s a b) : PrimrecRel s := by sorry

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

@[target]
theorem swap {f : α → β → σ} (h : Primrec₂ f) : Primrec₂ (swap f) := by sorry

@[target]
theorem nat_iff {f : α → β → σ} : Primrec₂ f ↔ Nat.Primrec
    (.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map (f a)) := by sorry

@[target]
theorem nat_iff' {f : α → β → σ} :
    Primrec₂ f ↔
      Primrec₂ fun m n : ℕ => (@decode α _ m).bind fun a => Option.map (f a) (@decode β _ n) := by sorry

end Primrec₂

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

@[target]
theorem to₂ {f : α × β → σ} (hf : Primrec f) : Primrec₂ fun a b => f (a, b) := by sorry

@[target]
theorem nat_rec {f : α → β} {g : α → ℕ × β → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => n.rec (motive := fun _ => β) (f a) fun n IH => g a (n, IH) := by sorry

@[target]
theorem nat_rec' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).rec (motive := fun _ => β) (g a) fun n IH => h a (n, IH) := by sorry

@[target]
theorem nat_rec₁ {f : ℕ → α → α} (a : α) (hf : Primrec₂ f) : Primrec (Nat.rec a f) := by sorry

@[target]
theorem nat_casesOn' {f : α → β} {g : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => (n.casesOn (f a) (g a) : β) := by sorry

@[target]
theorem nat_casesOn {f : α → ℕ} {g : α → β} {h : α → ℕ → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => ((f a).casesOn (g a) (h a) : β) := by sorry

@[target]
theorem nat_casesOn₁ {f : ℕ → α} (a : α) (hf : Primrec f) :
    Primrec (fun (n : ℕ) => (n.casesOn a f : α)) := by sorry

@[target]
theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (h a)^[f a] (g a) := by sorry

@[target]
theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec₂ g) :
    @Primrec _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) := by sorry

@[target]
theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).bind (g a) := by sorry

@[target]
theorem option_bind₁ {f : α → Option σ} (hf : Primrec f) : Primrec fun o => Option.bind o f := by sorry

@[target]
theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) := by sorry

@[target]
theorem option_map₁ {f : α → σ} (hf : Primrec f) : Primrec (Option.map f) := by sorry

@[target]
theorem option_iget [Inhabited α] : Primrec (@Option.iget α _) := by sorry

@[target]
theorem option_isSome : Primrec (@Option.isSome α) := by sorry

@[target]
theorem option_getD : Primrec₂ (@Option.getD α) := by sorry

@[target]
theorem bind_decode_iff {f : α → β → Option σ} :
    (Primrec₂ fun a n => (@decode β _ n).bind (f a)) ↔ Primrec₂ f := by sorry

@[target]
theorem map_decode_iff {f : α → β → σ} :
    (Primrec₂ fun a n => (@decode β _ n).map (f a)) ↔ Primrec₂ f := by sorry

@[target]
theorem nat_add : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ) := by sorry

@[target]
theorem nat_sub : Primrec₂ ((· - ·) : ℕ → ℕ → ℕ) := by sorry

@[target]
theorem nat_mul : Primrec₂ ((· * ·) : ℕ → ℕ → ℕ) := by sorry

@[target]
theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) else (g a) := by sorry

@[target]
theorem ite {c : α → Prop} [DecidablePred c] {f : α → σ} {g : α → σ} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a else g a := by sorry

@[target]
theorem nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop) := by sorry

@[target]

theorem nat_min : Primrec₂ (@min ℕ _) :=
  ite nat_le fst snd

@[target]
theorem nat_max : Primrec₂ (@max ℕ _) := by sorry

@[target]

theorem dom_bool (f : Bool → α) : Primrec f :=
  (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl

@[target]
theorem dom_bool₂ (f : Bool → Bool → α) : Primrec₂ f := by sorry

@[target]

protected theorem not : Primrec not :=
  dom_bool _

@[target]

protected theorem and : Primrec₂ and :=
  dom_bool₂ _

@[target]

protected theorem or : Primrec₂ or :=
  dom_bool₂ _

@[target]
theorem _root_.PrimrecPred.not {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    PrimrecPred fun a => ¬p a := by sorry

@[target]
theorem _root_.PrimrecPred.and {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a => p a ∧ q a := by sorry

@[target]
theorem _root_.PrimrecPred.or {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a => p a ∨ q a := by sorry

@[target]

protected theorem beq [DecidableEq α] : Primrec₂ (@BEq.beq α _) :=
  have : PrimrecRel fun a b : ℕ => a = b :=
    (PrimrecPred.and nat_le nat_le.swap).of_eq fun a => by simp [le_antisymm_iff]
  (this.comp₂ (Primrec.encode.comp₂ Primrec₂.left) (Primrec.encode.comp₂ Primrec₂.right)).of_eq
    fun _ _ => encode_injective.eq_iff

@[target]

protected theorem eq [DecidableEq α] : PrimrecRel (@Eq α) := Primrec.beq

@[target]
theorem nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop) := by sorry

@[target]
theorem option_guard {p : α → β → Prop} [∀ a b, Decidable (p a b)] (hp : PrimrecRel p) {f : α → β}
    (hf : Primrec f) : Primrec fun a => Option.guard (p a) (f a) := by sorry

@[target]
theorem option_orElse : Primrec₂ ((· <|> ·) : Option α → Option α → Option α) := by sorry

@[target]

protected theorem decode₂ : Primrec (decode₂ α) :=
  option_bind .decode <|
    option_guard (Primrec.beq.comp₂ (by exact encode_iff.mpr snd) (by exact fst.comp fst)) snd

@[target]
theorem list_findIdx₁ {p : α → β → Bool} (hp : Primrec₂ p) :
    ∀ l : List β, Primrec fun a => l.findIdx (p a) := by sorry

@[target]
theorem list_idxOf₁ [DecidableEq α] (l : List α) : Primrec fun a => l.idxOf a := by sorry

@[deprecated (since := "2025-01-30")] alias list_indexOf₁ := list_idxOf₁

@[target]

theorem dom_fintype [Finite α] (f : α → σ) : Primrec f :=
  let ⟨l, _, m⟩ := Finite.exists_univ_list α
  option_some_iff.1 <| by
    haveI := decidableEqOfEncodable α
    refine ((list_get?₁ (l.map f)).comp (list_idxOf₁ l)).of_eq fun a => ?_
    rw [List.get?_eq_getElem?, List.getElem?_map, List.getElem?_idxOf (m a), Option.map_some']

-- Porting note: These are new lemmas
-- I added it because it actually simplified the proofs
-- and because I couldn't understand the original proof
/-- A function is `PrimrecBounded` if its size is bounded by a primitive recursive function -/
@[target]
def PrimrecBounded (f : α → β) : Prop :=
  ∃ g : α → ℕ, Primrec g ∧ ∀ x, encode (f x) ≤ g x

@[target]
theorem nat_findGreatest {f : α → ℕ} {p : α → ℕ → Prop} [∀ x n, Decidable (p x n)]
    (hf : Primrec f) (hp : PrimrecRel p) : Primrec fun x => (f x).findGreatest (p x) := by sorry

/-- To show a function `f : α → ℕ` is primitive recursive, it is enough to show that the function
  is bounded by a primitive recursive function and that its graph is primitive recursive -/
@[target]
theorem of_graph {f : α → ℕ} (h₁ : PrimrecBounded f)
    (h₂ : PrimrecRel fun a b => f a = b) : Primrec f := by sorry

@[target]
theorem nat_div : Primrec₂ ((· / ·) : ℕ → ℕ → ℕ) := by sorry

@[target]
theorem nat_mod : Primrec₂ ((· % ·) : ℕ → ℕ → ℕ) := by sorry

@[target]
theorem nat_bodd : Primrec Nat.bodd := by sorry

@[target]
theorem nat_div2 : Primrec Nat.div2 := by sorry

@[target]
theorem nat_double : Primrec (fun n : ℕ => 2 * n) := by sorry

@[target]
theorem nat_double_succ : Primrec (fun n : ℕ => 2 * n + 1) := by sorry

end Primrec

section

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]
variable (H : Nat.Primrec fun n => Encodable.encode (@decode (List β) _ n))

open Primrec

private def prim : Primcodable (List β) := ⟨H⟩

private theorem list_casesOn' {f : α → List β} {g : α → σ} {h : α → β × List β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
      to₂ <|
        option_casesOn snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)).comp
      .id (encode_iff.2 hf)
  option_some_iff.1 <| this.of_eq fun a => by rcases f a with - | ⟨b, l⟩ <;> simp [encodek]

private theorem list_foldl' {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : haveI := prim H; Primrec f) (hg : Primrec g) (hh : haveI := prim H; Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  letI := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  have hG : Primrec₂ G := list_casesOn' H (snd.comp snd) snd <|
    to₂ <|
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fun (a : α) (n : ℕ) => (G a)^[n] (g a, f a)
  have hF : Primrec fun a => (F a (encode (f a))).1 :=
    (fst.comp <|
      nat_iterate (encode_iff.2 hf) (pair hg hf) <|
      hG)
  suffices ∀ a n, F a n = (((f a).take n).foldl (fun s b => h a (s, b)) (g a), (f a).drop n) by
    refine hF.of_eq fun a => ?_
    rw [this, List.take_of_length_le (length_le_encode _)]
  introv
  dsimp only [F]
  generalize f a = l
  generalize g a = x
  induction n generalizing l x with
  | zero => rfl
  | succ n IH =>
    simp only [iterate_succ, comp_apply]
    rcases l with - | ⟨b, l⟩ <;> simp [G, IH]

private theorem list_cons' : (haveI := prim H; Primrec₂ (@List.cons β)) :=
  letI := prim H
  encode_iff.1 (succ.comp <| Primrec₂.natPair.comp (encode_iff.2 fst) (encode_iff.2 snd))

private theorem list_reverse' :
    haveI := prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H .id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices ∀ l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction l <;> simp [*, List.reverseAux])

end

namespace Primcodable

variable {α : Type*} {β : Type*}
variable [Primcodable α] [Primcodable β]

open Primrec

instance sum : Primcodable (α ⊕ β) :=
  ⟨Primrec.nat_iff.1 <|
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
                to₂ <| nat_double_succ.comp (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
                to₂ <| nat_double.comp (Primrec.encode.comp snd)))).of_eq
        fun n =>
        show _ = encode (decodeSum n) by
          simp only [decodeSum, Nat.boddDiv2_eq]
          cases Nat.bodd n <;> simp [decodeSum]
          · cases @decode α _ n.div2 <;> rfl
          · cases @decode β _ n.div2 <;> rfl⟩

instance list : Primcodable (List α) :=
  ⟨letI H := @Primcodable.prim (List ℕ) _
    have : Primrec₂ fun (a : α) (o : Option (List ℕ)) => o.map (List.cons (encode a)) :=
      option_map snd <| (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (ofNat (List ℕ) n).reverse.foldl
          (fun o m => (@decode α _ m).bind fun a => o.map (List.cons (encode a))) (some []) :=
      list_foldl' H ((list_reverse' H).comp (.ofNat (List ℕ))) (const (some []))
        (Primrec.comp₂ (bind_decode_iff.2 <| .swap this) Primrec₂.right)
    nat_iff.1 <|
      (encode_iff.2 this).of_eq fun n => by
        rw [List.foldl_reverse]
        apply Nat.case_strong_induction_on n; · simp
        intro n IH; simp
        rcases @decode α _ n.unpair.1 with - | a; · rfl
        simp only [decode_eq_ofNat, Option.some.injEq, Option.some_bind, Option.map_some']
        suffices ∀ (o : Option (List ℕ)) (p), encode o = encode p →
            encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons a) p) from
          this _ _ (IH _ (Nat.unpair_right_le n))
        intro o p IH
        cases o <;> cases p
        · rfl
        · injection IH
        · injection IH
        · exact congr_arg (fun k => (Nat.pair (encode a) k).succ.succ) (Nat.succ.inj IH)⟩
end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

@[target]
theorem sumInl : Primrec (@Sum.inl α β) := by sorry

@[target]
theorem sumInr : Primrec (@Sum.inr α β) := by sorry

@[deprecated (since := "2025-02-21")] alias sum_inl := Primrec.sumInl
@[deprecated (since := "2025-02-21")] alias sum_inr := Primrec.sumInr

@[target]

theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by rcases f a with b | c <;> simp [Nat.div2_val, encodek]

@[deprecated (since := "2025-02-21")] alias sum_casesOn := Primrec.sumCasesOn

@[target]

theorem list_cons : Primrec₂ (@List.cons α) :=
  list_cons' Primcodable.prim

@[target]
theorem list_casesOn {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    Primrec f →
      Primrec g →
        Primrec₂ h → @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) := by sorry

@[target]
theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    Primrec f →
      Primrec g → Primrec₂ h → Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by sorry

@[target]
theorem list_reverse : Primrec (@List.reverse α) := by sorry

@[target]
theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldr (fun b s => h a (b, s)) (g a) := by sorry

@[target]
theorem list_head? : Primrec (@List.head? α) := by sorry

@[target]
theorem list_headI [Inhabited α] : Primrec (@List.headI α _) := by sorry

@[target]
theorem list_tail : Primrec (@List.tail α) := by sorry

@[target]
theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) := by sorry

@[target]
theorem list_get? : Primrec₂ (@List.get? α) := by sorry

@[target]
theorem list_getElem? : Primrec₂ (fun (l : List α) (n : ℕ) => l[n]?) := by sorry

@[target]

theorem list_getD (d : α) : Primrec₂ fun l n => List.getD l n d := by
  simp only [List.getD_eq_getElem?_getD]
  exact option_getD.comp₂ list_getElem? (const _)

@[target]
theorem list_getI [Inhabited α] : Primrec₂ (@List.getI α _) := by sorry

@[target]
theorem list_append : Primrec₂ ((· ++ ·) : List α → List α → List α) := by sorry

@[target]
theorem list_concat : Primrec₂ fun l (a : α) => l ++ [a] := by sorry

@[target]
theorem list_map {f : α → List β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) := by sorry

@[target]
theorem list_range : Primrec List.range := by sorry

@[target]
theorem list_flatten : Primrec (@List.flatten α) := by sorry

@[deprecated (since := "2024-10-15")] alias list_join := list_flatten

@[target]

theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).flatMap (g a)) := list_flatten.comp (list_map hf hg)

@[deprecated (since := "2024-10-16")] alias list_bind := list_flatMap

@[target]

theorem optionToList : Primrec (Option.toList : Option α → List α) :=
  (option_casesOn Primrec.id (const [])
    ((list_cons.comp Primrec.id (const [])).comp₂ Primrec₂.right)).of_eq
  (fun o => by rcases o <;> simp)

@[target]
theorem listFilterMap {f : α → List β} {g : α → β → Option σ}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).filterMap (g a) := by sorry

@[target]
theorem list_length : Primrec (@List.length α) := by sorry

@[target]
theorem list_findIdx {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a) := by sorry

@[target]
theorem list_idxOf [DecidableEq α] : Primrec₂ (@List.idxOf α _) := by sorry

@[deprecated (since := "2025-01-30")] alias list_indexOf := list_idxOf

@[target]

theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Primrec₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f :=
  suffices Primrec₂ fun a n => (List.range n).map (f a) from
    Primrec₂.option_some_iff.1 <|
      (list_get?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp [List.getElem?_range (Nat.lt_succ_self n)]
  Primrec₂.option_some_iff.1 <|
    (nat_rec (const (some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      induction n with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]

@[target]
theorem listLookup [DecidableEq α] : Primrec₂ (List.lookup : α → List (α × β) → Option β) := by sorry

@[target]
theorem nat_omega_rec' (f : β → σ) {m : β → ℕ} {l : β → List β} {g : β → List σ → Option σ}
    (hm : Primrec m) (hl : Primrec l) (hg : Primrec₂ g)
    (Ord : ∀ b, ∀ b' ∈ l b, m b' < m b)
    (H : ∀ b, g b ((l b).map f) = some (f b)) : Primrec f := by sorry

@[target]
theorem nat_omega_rec (f : α → β → σ) {m : α → β → ℕ}
    {l : α → β → List β} {g : α → β × List σ → Option σ}
    (hm : Primrec₂ m) (hl : Primrec₂ l) (hg : Primrec₂ g)
    (Ord : ∀ a b, ∀ b' ∈ l a b, m a b' < m a b)
    (H : ∀ a b, g a (b, (l a b).map (f a)) = some (f a b)) : Primrec₂ f := by sorry

end Primrec

namespace Primcodable

variable {α : Type*} [Primcodable α]

open Primrec

/-- A subtype of a primitive recursive predicate is `Primcodable`. -/
@[target]
def subtype {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) : Primcodable (Subtype p) :=
  ⟨have : Primrec fun n => (@decode α _ n).bind fun a => Option.guard p a :=
    option_bind .decode (option_guard (hp.comp snd).to₂ snd)
  nat_iff.1 <| (encode_iff.2 this).of_eq fun n =>
    show _ = encode ((@decode α _ n).bind fun _ => _) by
      rcases @decode α _ n with - | a; · rfl
      dsimp [Option.guard]
      by_cases h : p a <;> simp [h]; rfl⟩

instance fin {n} : Primcodable (Fin n) :=
  @ofEquiv _ _ (subtype <| nat_lt.comp .id (const n)) Fin.equivSubtype

instance vector {n} : Primcodable (List.Vector α n) :=
  subtype ((@Primrec.eq ℕ _ _).comp list_length (const _))

instance finArrow {n} : Primcodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm


section ULower

attribute [local instance] Encodable.decidableRangeEncode Encodable.decidableEqOfEncodable

@[target]
theorem mem_range_encode : PrimrecPred (fun n => n ∈ Set.range (encode : α → ℕ)) := by sorry

instance ulower : Primcodable (ULower α) :=
  Primcodable.subtype mem_range_encode

end ULower

end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

@[target]
theorem subtype_val {p : α → Prop} [DecidablePred p] {hp : PrimrecPred p} :
    haveI := Primcodable.subtype hp
    Primrec (@Subtype.val α p) := by sorry

@[target]
theorem subtype_val_iff {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → Subtype p} :
    haveI := Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f := by sorry

@[target]
theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
    {h : ∀ a, p (f a)} (hf : Primrec f) :
    haveI := Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) := by sorry

@[target]
theorem option_get {f : α → Option β} {h : ∀ a, (f a).isSome} :
    Primrec f → Primrec fun a => (f a).get (h a) := by sorry

@[target]
theorem ulower_down : Primrec (ULower.down : α → ULower α) := by sorry

@[target]
theorem ulower_up : Primrec (ULower.up : ULower α → α) := by sorry

@[target]
theorem fin_val_iff {n} {f : α → Fin n} : (Primrec fun a => (f a).1) ↔ Primrec f := by sorry

@[target]
theorem fin_val {n} : Primrec (fun (i : Fin n) => (i : ℕ)) := by sorry

@[target]
theorem fin_succ {n} : Primrec (@Fin.succ n) := by sorry

@[target]
theorem vector_toList {n} : Primrec (@List.Vector.toList α n) := by sorry

@[target]
theorem vector_toList_iff {n} {f : α → List.Vector β n} :
    (Primrec fun a => (f a).toList) ↔ Primrec f := by sorry

@[target]
theorem vector_cons {n} : Primrec₂ (@List.Vector.cons α n) := by sorry

@[target]
theorem vector_length {n} : Primrec (@List.Vector.length α n) := by sorry

@[target]
theorem vector_head {n} : Primrec (@List.Vector.head α n) := by sorry

@[target]
theorem vector_tail {n} : Primrec (@List.Vector.tail α n) := by sorry

@[target]
theorem vector_get {n} : Primrec₂ (@List.Vector.get α n) := by sorry

@[target]
theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ}, (∀ i, Primrec (f i)) → Primrec fun a => List.ofFn fun i => f i a := by sorry

@[target]
theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Primrec (f i)) :
    Primrec fun a => List.Vector.ofFn fun i => f i a := by sorry

@[target]
theorem vector_get' {n} : Primrec (@List.Vector.get α n) := by sorry

@[target]
theorem vector_ofFn' {n} : Primrec (@List.Vector.ofFn α n) := by sorry

@[target]
theorem fin_app {n} : Primrec₂ (@id (Fin n → σ)) := by sorry

@[target]
theorem fin_curry₁ {n} {f : Fin n → α → σ} : Primrec₂ f ↔ ∀ i, Primrec (f i) := by sorry

@[target]
theorem fin_curry {n} {f : α → Fin n → σ} : Primrec f ↔ Primrec₂ f := by sorry

end Primrec

namespace Nat

open List.Vector

/-- An alternative inductive definition of `Primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
inductive Primrec' : ∀ {n}, (List.Vector ℕ n → ℕ) → Prop
  | zero : @Primrec' 0 fun _ => 0
  | succ : @Primrec' 1 fun v => succ v.head
  | get {n} (i : Fin n) : Primrec' fun v => v.get i
  | comp {m n f} (g : Fin n → List.Vector ℕ m → ℕ) :
      Primrec' f → (∀ i, Primrec' (g i)) → Primrec' fun a => f (List.Vector.ofFn fun i => g i a)
  | prec {n f g} :
      @Primrec' n f →
        @Primrec' (n + 2) g →
          Primrec' fun v : List.Vector ℕ (n + 1) =>
            v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)

end Nat

namespace Nat.Primrec'

open List.Vector Primrec

@[target]
theorem to_prim {n f} (pf : @Nat.Primrec' n f) : Primrec f := by sorry

@[target]
theorem of_eq {n} {f g : List.Vector ℕ n → ℕ} (hf : Primrec' f) (H : ∀ i, f i = g i) :
    Primrec' g := by sorry

@[target]
theorem const {n} : ∀ m, @Primrec' n fun _ => m := by sorry

@[target]
theorem head {n : ℕ} : @Primrec' n.succ head := by sorry

@[target]
theorem tail {n f} (hf : @Primrec' n f) : @Primrec' n.succ fun v => f v.tail := by sorry

/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) : Prop :=
  ∀ i, Primrec' fun v => (f v).get i

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

protected theorem cons {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

@[target]
theorem idv {n} : @Vec n n id := by sorry

@[target]
theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) := by sorry

@[target]
theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g) :
    Primrec' fun v => f (g v) := by sorry

@[target]
theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
    (hg : @Primrec' n g) (hh : @Primrec' n h) : Primrec' fun v => f (g v) (h v) := by sorry

@[target]
theorem prec' {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h) :
    @Primrec' n fun v => (f v).rec (g v) fun y IH : ℕ => h (y ::ᵥ IH ::ᵥ v) := by sorry

@[target]
theorem pred : @Primrec' 1 fun v => v.head.pred := by sorry

@[target]
theorem add : @Primrec' 2 fun v => v.head + v.tail.head := by sorry

@[target]
theorem sub : @Primrec' 2 fun v => v.head - v.tail.head := by sorry

@[target]
theorem mul : @Primrec' 2 fun v => v.head * v.tail.head := by sorry

@[target]
theorem if_lt {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
    (hg : @Primrec' n g) : @Primrec' n fun v => if a v < b v then f v else g v := by sorry

@[target]
theorem natPair : @Primrec' 2 fun v => v.head.pair v.tail.head := by sorry

protected theorem encode : ∀ {n}, @Primrec' n encode
  | 0 => (const 0).of_eq fun v => by rw [v.eq_nil]; rfl
  | _ + 1 =>
    (succ.comp₁ _ (natPair.comp₂ _ head (tail Primrec'.encode))).of_eq fun ⟨_ :: _, _⟩ => rfl

@[target]
theorem sqrt : @Primrec' 1 fun v => v.head.sqrt := by sorry

@[target]
theorem unpair₁ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.1 := by sorry

@[target]
theorem unpair₂ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.2 := by sorry

@[target]
theorem of_prim {n f} : Primrec f → @Primrec' n f := by sorry

@[target]
theorem prim_iff {n f} : @Primrec' n f ↔ Primrec f := by sorry

@[target]
theorem prim_iff₁ {f : ℕ → ℕ} : (@Primrec' 1 fun v => f v.head) ↔ Primrec f := by sorry

@[target]
theorem prim_iff₂ {f : ℕ → ℕ → ℕ} : (@Primrec' 2 fun v => f v.head v.tail.head) ↔ Primrec₂ f := by sorry

@[target]
theorem vec_iff {m n f} : @Vec m n f ↔ Primrec f := by sorry

end Nat.Primrec'

@[target]
theorem Primrec.nat_sqrt : Primrec Nat.sqrt := by sorry
