import VerifiedAgora.tagger
/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Tactic.DeriveFintype

/-!
# Modelling partial recursive functions using Turing machines

The files `TMConfig` and `TMToPartrec` define a simplified basis for partial recursive functions,
and a `Turing.TM2` model
Turing machine for evaluating these functions. This amounts to a constructive proof that every
`Partrec` function can be evaluated by a Turing machine.

## Main definitions

* `ToPartrec.Code`: a simplified basis for partial recursive functions, valued in
  `List ℕ →. List ℕ`.
  * `ToPartrec.Code.eval`: semantics for a `ToPartrec.Code` program
-/

open List (Vector)

open Function (update)

open Relation

namespace Turing

/-!
## A simplified basis for partrec

This section constructs the type `Code`, which is a data type of programs with `List ℕ` input and
output, with enough expressivity to write any partial recursive function. The primitives are:

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `Nat.casesOn`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)

This basis is convenient because it is closer to the Turing machine model - the key operations are
splitting and merging of lists of unknown length, while the messy `n`-ary composition operation
from the traditional basis for partial recursive functions is absent - but it retains a
compositional semantics. The first step in transitioning to Turing machines is to make a sequential
evaluator for this basis, which we take up in the next section.
-/


namespace ToPartrec

/-- The type of codes for primitive recursive functions. Unlike `Nat.Partrec.Code`, this uses a set
of operations on `List ℕ`. See `Code.eval` for a description of the behavior of the primitives. -/
inductive Code
  | zero'
  | succ
  | tail
  | cons : Code → Code → Code
  | comp : Code → Code → Code
  | case : Code → Code → Code
  | fix : Code → Code
  deriving DecidableEq, Inhabited

/-- The semantics of the `Code` primitives, as partial functions `List ℕ →. List ℕ`. By convention
we functions that return a single result return a singleton `[n]`, or in some cases `n :: v` where
`v` will be ignored by a subsequent function.

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `Nat.casesOn`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)
-/
def Code.eval : Code → List ℕ →. List ℕ
  | Code.zero' => fun v => pure (0 :: v)
  | Code.succ => fun v => pure [v.headI.succ]
  | Code.tail => fun v => pure v.tail
  | Code.cons f fs => fun v => do
    let n ← Code.eval f v
    let ns ← Code.eval fs v
    pure (n.headI :: ns)
  | Code.comp f g => fun v => g.eval v >>= f.eval
  | Code.case f g => fun v => v.headI.rec (f.eval v.tail) fun y _ => g.eval (y::v.tail)
  | Code.fix f =>
    PFun.fix fun v => (f.eval v).map fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail

namespace Code

@[target, simp]
theorem zero'_eval : zero'.eval = fun v => pure (0 :: v) := by sorry

@[target, simp]
theorem succ_eval : succ.eval = fun v => pure [v.headI.succ] := by sorry

@[target, simp]
theorem tail_eval : tail.eval = fun v => pure v.tail := by sorry

@[target, simp]
theorem cons_eval (f fs) : (cons f fs).eval = fun v => do {
    let n ← Code.eval f v
    let ns ← Code.eval fs v
    pure (n.headI :: ns) } := by sorry

@[target, simp]
theorem comp_eval (f g) : (comp f g).eval = fun v => g.eval v >>= f.eval := by sorry

@[target, simp]
theorem case_eval (f g) :
    (case f g).eval = fun v => v.headI.rec (f.eval v.tail) fun y _ => g.eval (y::v.tail) := by sorry

@[target, simp]
theorem fix_eval (f) : (fix f).eval =
    PFun.fix fun v => (f.eval v).map fun v =>
      if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail := by sorry

/-- `nil` is the constant nil function: `nil v = []`. -/
def nil : Code :=
  tail.comp succ

@[target, simp]
theorem nil_eval (v) : nil.eval v = pure [] := by sorry

/-- `id` is the identity function: `id v = v`. -/
def id : Code :=
  tail.comp zero'

@[simp]
theorem id_eval (v) : id.eval v = pure v := by simp [id]

/-- `head` gets the head of the input list: `head [] = [0]`, `head (n :: v) = [n]`. -/
def head : Code :=
  cons id nil

@[target, simp]
theorem head_eval (v) : head.eval v = pure [v.headI] := by sorry

/-- `zero` is the constant zero function: `zero v = [0]`. -/
def zero : Code :=
  cons zero' nil

@[simp]
theorem zero_eval (v) : zero.eval v = pure [0] := by simp [zero]

/-- `pred` returns the predecessor of the head of the input:
`pred [] = [0]`, `pred (0 :: v) = [0]`, `pred (n+1 :: v) = [n]`. -/
def pred : Code :=
  case zero head

@[simp]
theorem pred_eval (v) : pred.eval v = pure [v.headI.pred] := by
  simp [pred]; cases v.headI <;> simp

/-- `rfind f` performs the function of the `rfind` primitive of partial recursive functions.
`rfind f v` returns the smallest `n` such that `(f (n :: v)).head = 0`.

It is implemented as:

    rfind f v = pred (fix (fun (n::v) => f (n::v) :: n+1 :: v) (0 :: v))

The idea is that the initial state is `0 :: v`, and the `fix` keeps `n :: v` as its internal state;
it calls `f (n :: v)` as the exit test and `n+1 :: v` as the next state. At the end we get
`n+1 :: v` where `n` is the desired output, and `pred (n+1 :: v) = [n]` returns the result.
-/
def rfind (f : Code) : Code :=
  comp pred <| comp (fix <| cons f <| cons succ tail) zero'

/-- `prec f g` implements the `prec` (primitive recursion) operation of partial recursive
functions. `prec f g` evaluates as:

* `prec f g [] = [f []]`
* `prec f g (0 :: v) = [f v]`
* `prec f g (n+1 :: v) = [g (n :: prec f g (n :: v) :: v)]`

It is implemented as:

    G (a :: b :: IH :: v) = (b :: a+1 :: b-1 :: g (a :: IH :: v) :: v)
    F (0 :: f_v :: v) = (f_v :: v)
    F (n+1 :: f_v :: v) = (fix G (0 :: n :: f_v :: v)).tail.tail
    prec f g (a :: v) = [(F (a :: f v :: v)).head]

Because `fix` always evaluates its body at least once, we must special case the `0` case to avoid
calling `g` more times than necessary (which could be bad if `g` diverges). If the input is
`0 :: v`, then `F (0 :: f v :: v) = (f v :: v)` so we return `[f v]`. If the input is `n+1 :: v`,
we evaluate the function from the bottom up, with initial state `0 :: n :: f v :: v`. The first
number counts up, providing arguments for the applications to `g`, while the second number counts
down, providing the exit condition (this is the initial `b` in the return value of `G`, which is
stripped by `fix`). After the `fix` is complete, the final state is `n :: 0 :: res :: v` where
`res` is the desired result, and the rest reduces this to `[res]`. -/
def prec (f g : Code) : Code :=
  let G :=
    cons tail <|
      cons succ <|
        cons (comp pred tail) <|
          cons (comp g <| cons id <| comp tail tail) <| comp tail <| comp tail tail
  let F := case id <| comp (comp (comp tail tail) (fix G)) zero'
  cons (comp F (cons head <| cons (comp f tail) tail)) nil

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

theorem exists_code.comp {m n} {f : List.Vector ℕ n →. ℕ} {g : Fin n → List.Vector ℕ m →. ℕ}
    (hf : ∃ c : Code, ∀ v : List.Vector ℕ n, c.eval v.1 = pure <$> f v)
    (hg : ∀ i, ∃ c : Code, ∀ v : List.Vector ℕ m, c.eval v.1 = pure <$> g i v) :
    ∃ c : Code, ∀ v : List.Vector ℕ m,
      c.eval v.1 = pure <$> ((List.Vector.mOfFn fun i => g i v) >>= f) := by
  rsuffices ⟨cg, hg⟩ :
    ∃ c : Code, ∀ v : List.Vector ℕ m,
      c.eval v.1 = Subtype.val <$> List.Vector.mOfFn fun i => g i v
  · obtain ⟨cf, hf⟩ := hf
    exact
      ⟨cf.comp cg, fun v => by
        simp [hg, hf, map_bind, seq_bind_eq, Function.comp_def]
        rfl⟩
  clear hf f; induction' n with n IH
  · exact ⟨nil, fun v => by simp [Vector.mOfFn, Bind.bind]; rfl⟩
  · obtain ⟨cg, hg₁⟩ := hg 0
    obtain ⟨cl, hl⟩ := IH fun i => hg i.succ
    exact
      ⟨cons cg cl, fun v => by
        simp [Vector.mOfFn, hg₁, map_bind, seq_bind_eq, bind_assoc, (· ∘ ·), hl]
        rfl⟩

@[target]
theorem exists_code {n} {f : List.Vector ℕ n →. ℕ} (hf : Nat.Partrec' f) :
    ∃ c : Code, ∀ v : List.Vector ℕ n, c.eval v.1 = pure <$> f v := by sorry

end Code

/-!
## From compositional semantics to sequential semantics

Our initial sequential model is designed to be as similar as possible to the compositional
semantics in terms of its primitives, but it is a sequential semantics, meaning that rather than
defining an `eval c : List ℕ →. List ℕ` function for each program, defined by recursion on
programs, we have a type `Cfg` with a step function `step : Cfg → Option cfg` that provides a
deterministic evaluation order. In order to do this, we introduce the notion of a *continuation*,
which can be viewed as a `Code` with a hole in it where evaluation is currently taking place.
Continuations can be assigned a `List ℕ →. List ℕ` semantics as well, with the interpretation
being that given a `List ℕ` result returned from the code in the hole, the remainder of the
program will evaluate to a `List ℕ` final value.

The continuations are:

* `halt`: the empty continuation: the hole is the whole program, whatever is returned is the
  final result. In our notation this is just `_`.
* `cons₁ fs v k`: evaluating the first part of a `cons`, that is `k (_ :: fs v)`, where `k` is the
  outer continuation.
* `cons₂ ns k`: evaluating the second part of a `cons`: `k (ns.headI :: _)`. (Technically we don't
  need to hold on to all of `ns` here since we are already committed to taking the head, but this
  is more regular.)
* `comp f k`: evaluating the first part of a composition: `k (f _)`.
* `fix f k`: waiting for the result of `f` in a `fix f` expression:
  `k (if _.headI = 0 then _.tail else fix f (_.tail))`

The type `Cfg` of evaluation states is:

* `ret k v`: we have received a result, and are now evaluating the continuation `k` with result
  `v`; that is, `k v` where `k` is ready to evaluate.
* `halt v`: we are done and the result is `v`.

The main theorem of this section is that for each code `c`, the state `stepNormal c halt v` steps
to `v'` in finitely many steps if and only if `Code.eval c v = some v'`.
-/


/-- The type of continuations, built up during evaluation of a `Code` expression. -/
inductive Cont
  | halt
  | cons₁ : Code → List ℕ → Cont → Cont
  | cons₂ : List ℕ → Cont → Cont
  | comp : Code → Cont → Cont
  | fix : Code → Cont → Cont
  deriving Inhabited

/-- The semantics of a continuation. -/
def Cont.eval : Cont → List ℕ →. List ℕ
  | Cont.halt => pure
  | Cont.cons₁ fs as k => fun v => do
    let ns ← Code.eval fs as
    Cont.eval k (v.headI :: ns)
  | Cont.cons₂ ns k => fun v => Cont.eval k (ns.headI :: v)
  | Cont.comp f k => fun v => Code.eval f v >>= Cont.eval k
  | Cont.fix f k => fun v => if v.headI = 0 then k.eval v.tail else f.fix.eval v.tail >>= k.eval

/-- The set of configurations of the machine:

* `halt v`: The machine is about to stop and `v : List ℕ` is the result.
* `ret k v`: The machine is about to pass `v : List ℕ` to continuation `k : Cont`.

We don't have a state corresponding to normal evaluation because these are evaluated immediately
to a `ret` "in zero steps" using the `stepNormal` function. -/
inductive Cfg
  | halt : List ℕ → Cfg
  | ret : Cont → List ℕ → Cfg
  deriving Inhabited

/-- Evaluating `c : Code` in a continuation `k : Cont` and input `v : List ℕ`. This goes by
recursion on `c`, building an augmented continuation and a value to pass to it.

* `zero' v = 0 :: v` evaluates immediately, so we return it to the parent continuation
* `succ v = [v.headI.succ]` evaluates immediately, so we return it to the parent continuation
* `tail v = v.tail` evaluates immediately, so we return it to the parent continuation
* `cons f fs v = (f v).headI :: fs v` requires two sub-evaluations, so we evaluate
  `f v` in the continuation `k (_.headI :: fs v)` (called `Cont.cons₁ fs v k`)
* `comp f g v = f (g v)` requires two sub-evaluations, so we evaluate
  `g v` in the continuation `k (f _)` (called `Cont.comp f k`)
* `case f g v = v.head.casesOn (f v.tail) (fun n => g (n :: v.tail))` has the information needed
  to evaluate the case statement, so we do that and transition to either
  `f v` or `g (n :: v.tail)`.
* `fix f v = let v' := f v; if v'.headI = 0 then k v'.tail else fix f v'.tail`
  needs to first evaluate `f v`, so we do that and leave the rest for the continuation (called
  `Cont.fix f k`)
-/
def stepNormal : Code → Cont → List ℕ → Cfg
  | Code.zero' => fun k v => Cfg.ret k (0::v)
  | Code.succ => fun k v => Cfg.ret k [v.headI.succ]
  | Code.tail => fun k v => Cfg.ret k v.tail
  | Code.cons f fs => fun k v => stepNormal f (Cont.cons₁ fs v k) v
  | Code.comp f g => fun k v => stepNormal g (Cont.comp f k) v
  | Code.case f g => fun k v =>
    v.headI.rec (stepNormal f k v.tail) fun y _ => stepNormal g k (y::v.tail)
  | Code.fix f => fun k v => stepNormal f (Cont.fix f k) v

/-- Evaluating a continuation `k : Cont` on input `v : List ℕ`. This is the second part of
evaluation, when we receive results from continuations built by `stepNormal`.

* `Cont.halt v = v`, so we are done and transition to the `Cfg.halt v` state
* `Cont.cons₁ fs as k v = k (v.headI :: fs as)`, so we evaluate `fs as` now with the continuation
  `k (v.headI :: _)` (called `cons₂ v k`).
* `Cont.cons₂ ns k v = k (ns.headI :: v)`, where we now have everything we need to evaluate
  `ns.headI :: v`, so we return it to `k`.
* `Cont.comp f k v = k (f v)`, so we call `f v` with `k` as the continuation.
* `Cont.fix f k v = k (if v.headI = 0 then k v.tail else fix f v.tail)`, where `v` is a value,
  so we evaluate the if statement and either call `k` with `v.tail`, or call `fix f v` with `k` as
  the continuation (which immediately calls `f` with `Cont.fix f k` as the continuation).
-/
def stepRet : Cont → List ℕ → Cfg
  | Cont.halt, v => Cfg.halt v
  | Cont.cons₁ fs as k, v => stepNormal fs (Cont.cons₂ v k) as
  | Cont.cons₂ ns k, v => stepRet k (ns.headI :: v)
  | Cont.comp f k, v => stepNormal f k v
  | Cont.fix f k, v => if v.headI = 0 then stepRet k v.tail else stepNormal f (Cont.fix f k) v.tail

/-- If we are not done (in `Cfg.halt` state), then we must be still stuck on a continuation, so
this main loop calls `stepRet` with the new continuation. The overall `step` function transitions
from one `Cfg` to another, only halting at the `Cfg.halt` state. -/
def step : Cfg → Option Cfg
  | Cfg.halt _ => none
  | Cfg.ret k v => some (stepRet k v)

/-- In order to extract a compositional semantics from the sequential execution behavior of
configurations, we observe that continuations have a monoid structure, with `Cont.halt` as the unit
and `Cont.then` as the multiplication. `Cont.then k₁ k₂` runs `k₁` until it halts, and then takes
the result of `k₁` and passes it to `k₂`.

We will not prove it is associative (although it is), but we are instead interested in the
associativity law `k₂ (eval c k₁) = eval c (k₁.then k₂)`. This holds at both the sequential and
compositional levels, and allows us to express running a machine without the ambient continuation
and relate it to the original machine's evaluation steps. In the literature this is usually
where one uses Turing machines embedded inside other Turing machines, but this approach allows us
to avoid changing the ambient type `Cfg` in the middle of the recursion.
-/
def Cont.then : Cont → Cont → Cont
  | Cont.halt => fun k' => k'
  | Cont.cons₁ fs as k => fun k' => Cont.cons₁ fs as (k.then k')
  | Cont.cons₂ ns k => fun k' => Cont.cons₂ ns (k.then k')
  | Cont.comp f k => fun k' => Cont.comp f (k.then k')
  | Cont.fix f k => fun k' => Cont.fix f (k.then k')

@[target]
theorem Cont.then_eval {k k' : Cont} {v} : (k.then k').eval v = k.eval v >>= k'.eval := by sorry

/-- The `then k` function is a "configuration homomorphism". Its operation on states is to append
`k` to the continuation of a `Cfg.ret` state, and to run `k` on `v` if we are in the `Cfg.halt v`
state. -/
def Cfg.then : Cfg → Cont → Cfg
  | Cfg.halt v => fun k' => stepRet k' v
  | Cfg.ret k v => fun k' => Cfg.ret (k.then k') v

/-- The `stepNormal` function respects the `then k'` homomorphism. Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state. -/
@[target]
theorem stepNormal_then (c) (k k' : Cont) (v) :
    stepNormal c (k.then k') v = (stepNormal c k v).then k' := by sorry

/-- The `stepRet` function respects the `then k'` homomorphism. Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state. -/
theorem stepRet_then {k k' : Cont} {v} : stepRet (k.then k') v = (stepRet k v).then k' := by
  induction k generalizing v with simp only [Cont.then, stepRet, *]
  | cons₁ =>
    rw [← stepNormal_then]
    rfl
  | comp =>
    rw [← stepNormal_then]
  | fix _ _ k_ih =>
    split_ifs
    · rw [← k_ih]
    · rw [← stepNormal_then]
      rfl
  | _ => simp only [Cfg.then]

/-- This is a temporary definition, because we will prove in `code_is_ok` that it always holds.
It asserts that `c` is semantically correct; that is, for any `k` and `v`,
`eval (stepNormal c k v) = eval (Cfg.ret k (Code.eval c v))`, as an equality of partial values
(so one diverges iff the other does).

In particular, we can let `k = Cont.halt`, and then this asserts that `stepNormal c Cont.halt v`
evaluates to `Cfg.halt (Code.eval c v)`. -/
def Code.Ok (c : Code) :=
  ∀ k v, Turing.eval step (stepNormal c k v) =
    Code.eval c v >>= fun v => Turing.eval step (Cfg.ret k v)

@[target]
theorem Code.Ok.zero {c} (h : Code.Ok c) {v} :
    Turing.eval step (stepNormal c Cont.halt v) = Cfg.halt <$> Code.eval c v := by sorry

@[target]
theorem stepNormal.is_ret (c k v) : ∃ k' v', stepNormal c k v = Cfg.ret k' v' := by sorry

theorem cont_eval_fix {f k v} (fok : Code.Ok f) :
    Turing.eval step (stepNormal f (Cont.fix f k) v) =
      f.fix.eval v >>= fun v => Turing.eval step (Cfg.ret k v) := by
  refine Part.ext fun x => ?_
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · suffices ∀ c, x ∈ eval step c → ∀ v c', c = Cfg.then c' (Cont.fix f k) →
      Reaches step (stepNormal f Cont.halt v) c' →
        ∃ v₁ ∈ f.eval v, ∃ v₂ ∈ if List.headI v₁ = 0 then pure v₁.tail else f.fix.eval v₁.tail,
          x ∈ eval step (Cfg.ret k v₂) by
      intro h
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (stepNormal_then _ Cont.halt _ _) ReflTransGen.refl
      refine ⟨v₂, PFun.mem_fix_iff.2 ?_, h₃⟩
      simp only [Part.eq_some_iff.2 hv₁, Part.map_some]
      split_ifs at hv₂ ⊢
      · rw [Part.mem_some_iff.1 hv₂]
        exact Or.inl (Part.mem_some _)
      · exact Or.inr ⟨_, Part.mem_some _, hv₂⟩
    refine fun c he => evalInduction he fun y h IH => ?_
    rintro v (⟨v'⟩ | ⟨k', v'⟩) rfl hr <;> rw [Cfg.then] at h IH <;> simp only [] at h IH
    · have := mem_eval.2 ⟨hr, rfl⟩
      rw [fok, Part.bind_eq_bind, Part.mem_bind_iff] at this
      obtain ⟨v'', h₁, h₂⟩ := this
      rw [reaches_eval] at h₂
      swap
      · exact ReflTransGen.single rfl
      cases Part.mem_unique h₂ (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
      refine ⟨v', h₁, ?_⟩
      rw [stepRet] at h
      revert h
      by_cases he : v'.headI = 0 <;> simp only [exists_prop, if_pos, if_false, he] <;> intro h
      · refine ⟨_, Part.mem_some _, ?_⟩
        rw [reaches_eval]
        · exact h
        exact ReflTransGen.single rfl
      · obtain ⟨k₀, v₀, e₀⟩ := stepNormal.is_ret f Cont.halt v'.tail
        have e₁ := stepNormal_then f Cont.halt (Cont.fix f k) v'.tail
        rw [e₀, Cont.then, Cfg.then] at e₁
        simp only [] at e₁
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (stepRet (k₀.then (Cont.fix f k)) v₀) (by rw [stepRet, if_neg he, e₁]; rfl)
            v'.tail _ stepRet_then (by apply ReflTransGen.single; rw [e₀]; rfl)
        refine ⟨_, PFun.mem_fix_iff.2 ?_, h₃⟩
        simp only [Part.eq_some_iff.2 hv₁, Part.map_some, Part.mem_some_iff]
        split_ifs at hv₂ ⊢ <;> [exact Or.inl (congr_arg Sum.inl (Part.mem_some_iff.1 hv₂));
          exact Or.inr ⟨_, rfl, hv₂⟩]
    · exact IH _ rfl _ _ stepRet_then (ReflTransGen.tail hr rfl)
  · rintro ⟨v', he, hr⟩
    rw [reaches_eval] at hr
    swap
    · exact ReflTransGen.single rfl
    refine PFun.fixInduction he fun v (he : v' ∈ f.fix.eval v) IH => ?_
    rw [fok, Part.bind_eq_bind, Part.mem_bind_iff]
    obtain he | ⟨v'', he₁', _⟩ := PFun.mem_fix_iff.1 he
    · obtain ⟨v', he₁, he₂⟩ := (Part.mem_map_iff _).1 he
      split_ifs at he₂ with h; cases he₂
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rwa [stepRet, if_pos h]
    · obtain ⟨v₁, he₁, he₂⟩ := (Part.mem_map_iff _).1 he₁'
      split_ifs at he₂ with h; cases he₂
      clear he₁'
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rw [stepRet, if_neg h]
      exact IH v₁.tail ((Part.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩)

@[target]
theorem code_is_ok (c) : Code.Ok c := by sorry

@[target]
theorem stepNormal_eval (c v) : eval step (stepNormal c Cont.halt v) = Cfg.halt <$> c.eval v := by sorry

@[target]
theorem stepRet_eval {k v} : eval step (stepRet k v) = Cfg.halt <$> k.eval v := by sorry

end ToPartrec

end Turing
