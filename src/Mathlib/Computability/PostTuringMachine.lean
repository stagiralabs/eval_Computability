import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.Tape
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Option
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.PFun

/-!
# Turing machines

The files `PostTuringMachine.lean` and `TuringMachine.lean` define
a sequence of simple machine languages, starting with Turing machines and working
up to more complex languages based on Wang B-machines.

`PostTuringMachine.lean` covers the TM0 model and TM1 model;
`TuringMachine.lean` adds the TM2 model.

## Naming conventions

Each model of computation in this file shares a naming convention for the elements of a model of
computation. These are the parameters for the language:

* `Γ` is the alphabet on the tape.
* `Λ` is the set of labels, or internal machine states.
* `σ` is the type of internal memory, not on the tape. This does not exist in the TM0 model, and
  later models achieve this by mixing it into `Λ`.
* `K` is used in the TM2 model, which has multiple stacks, and denotes the number of such stacks.

All of these variables denote "essentially finite" types, but for technical reasons it is
convenient to allow them to be infinite anyway. When using an infinite type, we will be interested
to prove that only finitely many values of the type are ever interacted with.

Given these parameters, there are a few common structures for the model that arise:

* `Stmt` is the set of all actions that can be performed in one step. For the TM0 model this set is
  finite, and for later models it is an infinite inductive type representing "possible program
  texts".
* `Cfg` is the set of instantaneous configurations, that is, the state of the machine together with
  its environment.
* `Machine` is the set of all machines in the model. Usually this is approximately a function
  `Λ → Stmt`, although different models have different ways of halting and other actions.
* `step : Cfg → Option Cfg` is the function that describes how the state evolves over one step.
  If `step c = none`, then `c` is a terminal state, and the result of the computation is read off
  from `c`. Because of the type of `step`, these models are all deterministic by construction.
* `init : Input → Cfg` sets up the initial state. The type `Input` depends on the model;
  in most cases it is `List Γ`.
* `eval : Machine → Input → Part Output`, given a machine `M` and input `i`, starts from
  `init i`, runs `step` until it reaches an output, and then applies a function `Cfg → Output` to
  the final state to obtain the result. The type `Output` depends on the model.
* `Supports : Machine → Finset Λ → Prop` asserts that a machine `M` starts in `S : Finset Λ`, and
  can only ever jump to other states inside `S`. This implies that the behavior of `M` on any input
  cannot depend on its values outside `S`. We use this to allow `Λ` to be an infinite set when
  convenient, and prove that only finitely many of these states are actually accessible. This
  formalizes "essentially finite" mentioned above.
-/

assert_not_exists MonoidWithZero

open List (Vector)
open Relation

open Nat (iterate)

open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'
  iterate_zero_apply)

namespace Turing

/-- Run a state transition function `σ → Option σ` "to completion". The return value is the last
state returned before a `none` result. If the state transition function always returns `some`,
then the computation diverges, returning `Part.none`. -/
def eval {σ} (f : σ → Option σ) : σ → Part σ :=
  PFun.fix fun s ↦ Part.some <| (f s).elim (Sum.inl s) Sum.inr

/-- The reflexive transitive closure of a state transition function. `Reaches f a b` means
there is a finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation permits zero steps of the state transition function. -/
def Reaches {σ} (f : σ → Option σ) : σ → σ → Prop :=
  ReflTransGen fun a b ↦ b ∈ f a

/-- The transitive closure of a state transition function. `Reaches₁ f a b` means there is a
nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation does not permit zero steps of the state transition function. -/
def Reaches₁ {σ} (f : σ → Option σ) : σ → σ → Prop :=
  TransGen fun a b ↦ b ∈ f a

@[target]
theorem reaches₁_eq {σ} {f : σ → Option σ} {a b c} (h : f a = f b) :
    Reaches₁ f a c ↔ Reaches₁ f b c := by sorry

@[target]
theorem reaches_total {σ} {f : σ → Option σ} {a b c} (hab : Reaches f a b) (hac : Reaches f a c) :
    Reaches f b c ∨ Reaches f c b := by sorry

@[target]
theorem reaches₁_fwd {σ} {f : σ → Option σ} {a b c} (h₁ : Reaches₁ f a c) (h₂ : b ∈ f a) :
    Reaches f b c := by sorry

/-- A variation on `Reaches`. `Reaches₀ f a b` holds if whenever `Reaches₁ f b c` then
`Reaches₁ f a c`. This is a weaker property than `Reaches` and is useful for replacing states with
equivalent states without taking a step. -/
def Reaches₀ {σ} (f : σ → Option σ) (a b : σ) : Prop :=
  ∀ c, Reaches₁ f b c → Reaches₁ f a c

@[target]
theorem Reaches₀.trans {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b)
    (h₂ : Reaches₀ f b c) : Reaches₀ f a c := by sorry

@[target, refl]
theorem Reaches₀.refl {σ} {f : σ → Option σ} (a : σ) : Reaches₀ f a a := by sorry

@[target]
theorem Reaches₀.single {σ} {f : σ → Option σ} {a b : σ} (h : b ∈ f a) : Reaches₀ f a b := by sorry

@[target]
theorem Reaches₀.head {σ} {f : σ → Option σ} {a b c : σ} (h : b ∈ f a) (h₂ : Reaches₀ f b c) :
    Reaches₀ f a c := by sorry

@[target]
theorem Reaches₀.tail {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b) (h : c ∈ f b) :
    Reaches₀ f a c := by sorry

@[target]
theorem reaches₀_eq {σ} {f : σ → Option σ} {a b} (e : f a = f b) : Reaches₀ f a b := by sorry

@[target]
theorem Reaches₁.to₀ {σ} {f : σ → Option σ} {a b : σ} (h : Reaches₁ f a b) : Reaches₀ f a b := by sorry

@[target]
theorem Reaches.to₀ {σ} {f : σ → Option σ} {a b : σ} (h : Reaches f a b) : Reaches₀ f a b := by sorry

@[target]
theorem Reaches₀.tail' {σ} {f : σ → Option σ} {a b c : σ} (h : Reaches₀ f a b) (h₂ : c ∈ f b) :
    Reaches₁ f a c := by sorry

/-- (co-)Induction principle for `eval`. If a property `C` holds of any point `a` evaluating to `b`
which is either terminal (meaning `a = b`) or where the next point also satisfies `C`, then it
holds of any point where `eval f a` evaluates to `b`. This formalizes the notion that if
`eval f a` evaluates to `b` then it reaches terminal state `b` in finitely many steps. -/
@[elab_as_elim]
def evalInduction {σ} {f : σ → Option σ} {b : σ} {C : σ → Sort*} {a : σ}
    (h : b ∈ eval f a) (H : ∀ a, b ∈ eval f a → (∀ a', f a = some a' → C a') → C a) : C a :=
  PFun.fixInduction h fun a' ha' h' ↦
    H _ ha' fun b' e ↦ h' _ <| Part.mem_some_iff.2 <| by rw [e]; rfl

@[target]
theorem mem_eval {σ} {f : σ → Option σ} {a b} : b ∈ eval f a ↔ Reaches f a b ∧ f b = none := by sorry

@[target]
theorem eval_maximal₁ {σ} {f : σ → Option σ} {a b} (h : b ∈ eval f a) (c) : ¬Reaches₁ f b c := by sorry

@[target]
theorem eval_maximal {σ} {f : σ → Option σ} {a b} (h : b ∈ eval f a) {c} : Reaches f b c ↔ c = b := by sorry

@[target]
theorem reaches_eval {σ} {f : σ → Option σ} {a b} (ab : Reaches f a b) : eval f a = eval f b := by sorry

/-- Given a relation `tr : σ₁ → σ₂ → Prop` between state spaces, and state transition functions
`f₁ : σ₁ → Option σ₁` and `f₂ : σ₂ → Option σ₂`, `Respects f₁ f₂ tr` means that if `tr a₁ a₂` holds
initially and `f₁` takes a step to `a₂` then `f₂` will take one or more steps before reaching a
state `b₂` satisfying `tr a₂ b₂`, and if `f₁ a₁` terminates then `f₂ a₂` also terminates.
Such a relation `tr` is also known as a refinement. -/
def Respects {σ₁ σ₂} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂ → Prop) :=
  ∀ ⦃a₁ a₂⦄, tr a₁ a₂ → (match f₁ a₁ with
    | some b₁ => ∃ b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    | none => f₂ a₂ = none : Prop)

@[target]
theorem tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches₁ f₁ a₁ b₁) : ∃ b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂ := by sorry

@[target]
theorem tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches f₁ a₁ b₁) : ∃ b₂, tr b₁ b₂ ∧ Reaches f₂ a₂ b₂ := by sorry

@[target]
theorem tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₂} (ab : Reaches f₂ a₂ b₂) :
    ∃ c₁ c₂, Reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁ := by sorry

theorem tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₁ a₂}
    (aa : tr a₁ a₂) (ab : b₁ ∈ eval f₁ a₁) : ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ := by
  obtain ⟨ab, b0⟩ := mem_eval.1 ab
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩
  refine ⟨_, bb, mem_eval.2 ⟨ab, ?_⟩⟩
  have := H bb; rwa [b0] at this

@[target]
theorem tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂}
    (aa : tr a₁ a₂) (ab : b₂ ∈ eval f₂ a₂) : ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ := by sorry

theorem tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) : (eval f₂ a₂).Dom ↔ (eval f₁ a₁).Dom :=
  ⟨fun h ↦
    let ⟨_, _, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩
    h,
    fun h ↦
    let ⟨_, _, h, _⟩ := tr_eval H aa ⟨h, rfl⟩
    h⟩

/-- A simpler version of `Respects` when the state transition relation `tr` is a function. -/
def FRespects {σ₁ σ₂} (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂) (a₂ : σ₂) : Option σ₁ → Prop
  | some b₁ => Reaches₁ f₂ a₂ (tr b₁)
  | none => f₂ a₂ = none

@[target]
theorem frespects_eq {σ₁ σ₂} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂} {a₂ b₂} (h : f₂ a₂ = f₂ b₂) :
    ∀ {b₁}, FRespects f₂ tr a₂ b₁ ↔ FRespects f₂ tr b₂ b₁ := by sorry

@[target]
theorem fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂} :
    (Respects f₁ f₂ fun a b ↦ tr a = b) ↔ ∀ ⦃a₁⦄, FRespects f₂ tr (tr a₁) (f₁ a₁) := by sorry

@[target]
theorem tr_eval' {σ₁ σ₂} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂)
    (H : Respects f₁ f₂ fun a b ↦ tr a = b) (a₁) : eval f₂ (tr a₁) = tr <$> eval f₁ a₁ := by sorry

/-!
## The TM0 model

A TM0 Turing machine is essentially a Post-Turing machine, adapted for type theory.

A Post-Turing machine with symbol type `Γ` and label type `Λ` is a function
`Λ → Γ → Option (Λ × Stmt)`, where a `Stmt` can be either `move left`, `move right` or `write a`
for `a : Γ`. The machine works over a "tape", a doubly-infinite sequence of elements of `Γ`, and
an instantaneous configuration, `Cfg`, is a label `q : Λ` indicating the current internal state of
the machine, and a `Tape Γ` (which is essentially `ℤ →₀ Γ`). The evolution is described by the
`step` function:

* If `M q T.head = none`, then the machine halts.
* If `M q T.head = some (q', s)`, then the machine performs action `s : Stmt` and then transitions
  to state `q'`.

The initial state takes a `List Γ` and produces a `Tape Γ` where the head of the list is the head
of the tape and the rest of the list extends to the right, with the left side all blank. The final
state takes the entire right side of the tape right or equal to the current position of the
machine. (This is actually a `ListBlank Γ`, not a `List Γ`, because we don't know, at this level
of generality, where the output ends. If equality to `default : Γ` is decidable we can trim the list
to remove the infinite tail of blanks.)
-/


namespace TM0

section

-- type of tape symbols
variable (Γ : Type*)

-- type of "labels" or TM states
variable (Λ : Type*)

/-- A Turing machine "statement" is just a command to either move
  left or right, or write a symbol on the tape. -/
inductive Stmt
  | move : Dir → Stmt
  | write : Γ → Stmt

instance Stmt.inhabited [Inhabited Γ] : Inhabited (Stmt Γ) :=
  ⟨Stmt.write default⟩

/-- A Post-Turing machine with symbol type `Γ` and label type `Λ`
  is a function which, given the current state `q : Λ` and
  the tape head `a : Γ`, either halts (returns `none`) or returns
  a new state `q' : Λ` and a `Stmt` describing what to do,
  either a move left or right, or a write command.

  Both `Λ` and `Γ` are required to be inhabited; the default value
  for `Γ` is the "blank" tape value, and the default value of `Λ` is
  the initial state. -/
@[nolint unusedArguments] -- this is a deliberate addition, see comment
def Machine [Inhabited Λ] :=
  Λ → Γ → Option (Λ × (Stmt Γ))

instance Machine.inhabited [Inhabited Λ] : Inhabited (Machine Γ Λ) := by
  unfold Machine; infer_instance

/-- The configuration state of a Turing machine during operation
  consists of a label (machine state), and a tape.
  The tape is represented in the form `(a, L, R)`, meaning the tape looks like `L.rev ++ [a] ++ R`
  with the machine currently reading the `a`. The lists are
  automatically extended with blanks as the machine moves around. -/
structure Cfg [Inhabited Γ] where
  /-- The current machine state. -/
  q : Λ
  /-- The current state of the tape: current symbol, left and right parts. -/
  Tape : Tape Γ

variable {Γ Λ}
variable [Inhabited Λ]

section
variable [Inhabited Γ]

instance Cfg.inhabited : Inhabited (Cfg Γ Λ) := ⟨⟨default, default⟩⟩

/-- Execution semantics of the Turing machine. -/
def step (M : Machine Γ Λ) : Cfg Γ Λ → Option (Cfg Γ Λ) :=
  fun ⟨q, T⟩ ↦ (M q T.1).map fun ⟨q', a⟩ ↦ ⟨q', match a with
    | Stmt.move d => T.move d
    | Stmt.write a => T.write a⟩

/-- The statement `Reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def Reaches (M : Machine Γ Λ) : Cfg Γ Λ → Cfg Γ Λ → Prop := ReflTransGen fun a b ↦ b ∈ step M a

/-- The initial configuration. -/
def init (l : List Γ) : Cfg Γ Λ := ⟨default, Tape.mk₁ l⟩

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : Machine Γ Λ) (l : List Γ) : Part (ListBlank Γ) :=
  (Turing.eval (step M) (init l)).map fun c ↦ c.Tape.right₀

/-- The raw definition of a Turing machine does not require that
  `Γ` and `Λ` are finite, and in practice we will be interested
  in the infinite `Λ` case. We recover instead a notion of
  "effectively finite" Turing machines, which only make use of a
  finite subset of their states. We say that a set `S ⊆ Λ`
  supports a Turing machine `M` if `S` is closed under the
  transition function and contains the initial state. -/
def Supports (M : Machine Γ Λ) (S : Set Λ) :=
  default ∈ S ∧ ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S

@[target]
theorem step_supports (M : Machine Γ Λ) {S : Set Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg Γ Λ}, c' ∈ step M c → c.q ∈ S → c'.q ∈ S := by sorry

end

@[target]
theorem univ_supports (M : Machine Γ Λ) : Supports M Set.univ := by sorry

end

section

variable {Γ : Type*} [Inhabited Γ]
variable {Γ' : Type*} [Inhabited Γ']
variable {Λ : Type*} [Inhabited Λ]
variable {Λ' : Type*} [Inhabited Λ']

/-- Map a TM statement across a function. This does nothing to move statements and maps the write
values. -/
def Stmt.map (f : PointedMap Γ Γ') : Stmt Γ → Stmt Γ'
  | Stmt.move d => Stmt.move d
  | Stmt.write a => Stmt.write (f a)

/-- Map a configuration across a function, given `f : Γ → Γ'` a map of the alphabets and
`g : Λ → Λ'` a map of the machine states. -/
def Cfg.map (f : PointedMap Γ Γ') (g : Λ → Λ') : Cfg Γ Λ → Cfg Γ' Λ'
  | ⟨q, T⟩ => ⟨g q, T.map f⟩

variable (M : Machine Γ Λ) (f₁ : PointedMap Γ Γ') (f₂ : PointedMap Γ' Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ)

/-- Because the state transition function uses the alphabet and machine states in both the input
and output, to map a machine from one alphabet and machine state space to another we need functions
in both directions, essentially an `Equiv` without the laws. -/
def Machine.map : Machine Γ' Λ'
  | q, l => (M (g₂ q) (f₂ l)).map (Prod.map g₁ (Stmt.map f₁))

@[target]
theorem Machine.map_step {S : Set Λ} (f₂₁ : Function.RightInverse f₁ f₂)
    (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
    ∀ c : Cfg Γ Λ,
      c.q ∈ S → (step M c).map (Cfg.map f₁ g₁) = step (M.map f₁ f₂ g₁ g₂) (Cfg.map f₁ g₁ c) := by sorry

@[target]
theorem map_init (g₁ : PointedMap Λ Λ') (l : List Γ) : (init l).map f₁ g₁ = init (l.map f₁) := by sorry

@[target]
theorem Machine.map_respects (g₁ : PointedMap Λ Λ') (g₂ : Λ' → Λ) {S} (ss : Supports M S)
    (f₂₁ : Function.RightInverse f₁ f₂) (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
    Respects (step M) (step (M.map f₁ f₂ g₁ g₂)) fun a b ↦ a.q ∈ S ∧ Cfg.map f₁ g₁ a = b := by sorry

end

end TM0

/-!
## The TM1 model

The TM1 model is a simplification and extension of TM0 (Post-Turing model) in the direction of
Wang B-machines. The machine's internal state is extended with a (finite) store `σ` of variables
that may be accessed and updated at any time.

A machine is given by a `Λ` indexed set of procedures or functions. Each function has a body which
is a `Stmt`. Most of the regular commands are allowed to use the current value `a` of the local
variables and the value `T.head` on the tape to calculate what to write or how to change local
state, but the statements themselves have a fixed structure. The `Stmt`s can be as follows:

* `move d q`: move left or right, and then do `q`
* `write (f : Γ → σ → Γ) q`: write `f a T.head` to the tape, then do `q`
* `load (f : Γ → σ → σ) q`: change the internal state to `f a T.head`
* `branch (f : Γ → σ → Bool) qtrue qfalse`: If `f a T.head` is true, do `qtrue`, else `qfalse`
* `goto (f : Γ → σ → Λ)`: Go to label `f a T.head`
* `halt`: Transition to the halting state, which halts on the following step

Note that here most statements do not have labels; `goto` commands can only go to a new function.
Only the `goto` and `halt` statements actually take a step; the rest is done by recursion on
statements and so take 0 steps. (There is a uniform bound on how many statements can be executed
before the next `goto`, so this is an `O(1)` speedup with the constant depending on the machine.)

The `halt` command has a one step stutter before actually halting so that any changes made before
the halt have a chance to be "committed", since the `eval` relation uses the final configuration
before the halt as the output, and `move` and `write` etc. take 0 steps in this model.
-/


namespace TM1


section

variable (Γ : Type*)

-- Type of tape symbols
variable (Λ : Type*)

-- Type of function labels
variable (σ : Type*)

-- Type of variable settings
/-- The TM1 model is a simplification and extension of TM0
  (Post-Turing model) in the direction of Wang B-machines. The machine's
  internal state is extended with a (finite) store `σ` of variables
  that may be accessed and updated at any time.
  A machine is given by a `Λ` indexed set of procedures or functions.
  Each function has a body which is a `Stmt`, which can either be a
  `move` or `write` command, a `branch` (if statement based on the
  current tape value), a `load` (set the variable value),
  a `goto` (call another function), or `halt`. Note that here
  most statements do not have labels; `goto` commands can only
  go to a new function. All commands have access to the variable value
  and current tape value. -/
inductive Stmt
  | move : Dir → Stmt → Stmt
  | write : (Γ → σ → Γ) → Stmt → Stmt
  | load : (Γ → σ → σ) → Stmt → Stmt
  | branch : (Γ → σ → Bool) → Stmt → Stmt → Stmt
  | goto : (Γ → σ → Λ) → Stmt
  | halt : Stmt

open Stmt

instance Stmt.inhabited : Inhabited (Stmt Γ Λ σ) := ⟨halt⟩

/-- The configuration of a TM1 machine is given by the currently
  evaluating statement, the variable store value, and the tape. -/
structure Cfg [Inhabited Γ] where
  /-- The statement (if any) which is currently evaluated -/
  l : Option Λ
  /-- The current value of the variable store -/
  var : σ
  /-- The current state of the tape -/
  Tape : Tape Γ

instance Cfg.inhabited [Inhabited Γ] [Inhabited σ] : Inhabited (Cfg Γ Λ σ) :=
  ⟨⟨default, default, default⟩⟩

variable {Γ Λ σ}

/-- The semantics of TM1 evaluation. -/
def stepAux [Inhabited Γ] : Stmt Γ Λ σ → σ → Tape Γ → Cfg Γ Λ σ
  | move d q, v, T => stepAux q v (T.move d)
  | write a q, v, T => stepAux q v (T.write (a T.1 v))
  | load s q, v, T => stepAux q (s T.1 v) T
  | branch p q₁ q₂, v, T => cond (p T.1 v) (stepAux q₁ v T) (stepAux q₂ v T)
  | goto l, v, T => ⟨some (l T.1 v), v, T⟩
  | halt, v, T => ⟨none, v, T⟩

/-- The state transition function. -/
def step [Inhabited Γ] (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Option (Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, T⟩ => some (stepAux (M l) v T)

/-- A set `S` of labels supports the statement `q` if all the `goto`
  statements in `q` refer only to other functions in `S`. -/
def SupportsStmt (S : Finset Λ) : Stmt Γ Λ σ → Prop
  | move _ q => SupportsStmt S q
  | write _ q => SupportsStmt S q
  | load _ q => SupportsStmt S q
  | branch _ q₁ q₂ => SupportsStmt S q₁ ∧ SupportsStmt S q₂
  | goto l => ∀ a v, l a v ∈ S
  | halt => True

open scoped Classical in
/-- The subterm closure of a statement. -/
noncomputable def stmts₁ : Stmt Γ Λ σ → Finset (Stmt Γ Λ σ)
  | Q@(move _ q) => insert Q (stmts₁ q)
  | Q@(write _ q) => insert Q (stmts₁ q)
  | Q@(load _ q) => insert Q (stmts₁ q)
  | Q@(branch _ q₁ q₂) => insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
  | Q => {Q}

@[target]
theorem stmts₁_self {q : Stmt Γ Λ σ} : q ∈ stmts₁ q := by sorry

@[target]
theorem stmts₁_trans {q₁ q₂ : Stmt Γ Λ σ} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := by sorry

@[target]
theorem stmts₁_supportsStmt_mono {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h : q₁ ∈ stmts₁ q₂)
    (hs : SupportsStmt S q₂) : SupportsStmt S q₁ := by sorry

open scoped Classical in
/-- The set of all statements in a Turing machine, plus one extra value `none` representing the
halt state. This is used in the TM1 to TM0 reduction. -/
noncomputable def stmts (M : Λ → Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ)) :=
  Finset.insertNone (S.biUnion fun q ↦ stmts₁ (M q))

@[target]
theorem stmts_trans {M : Λ → Stmt Γ Λ σ} {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h₁ : q₁ ∈ stmts₁ q₂) :
    some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := by sorry

variable [Inhabited Λ]

/-- A set `S` of labels supports machine `M` if all the `goto`
  statements in the functions in `S` refer only to other functions
  in `S`. -/
def Supports (M : Λ → Stmt Γ Λ σ) (S : Finset Λ) :=
  default ∈ S ∧ ∀ q ∈ S, SupportsStmt S (M q)

@[target]
theorem stmts_supportsStmt {M : Λ → Stmt Γ Λ σ} {S : Finset Λ} {q : Stmt Γ Λ σ}
    (ss : Supports M S) : some q ∈ stmts M S → SupportsStmt S q := by sorry

variable [Inhabited Γ]

@[target]
theorem step_supports (M : Λ → Stmt Γ Λ σ) {S : Finset Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg Γ Λ σ}, c' ∈ step M c → c.l ∈ Finset.insertNone S → c'.l ∈ Finset.insertNone S := by sorry

variable [Inhabited σ]

/-- The initial state, given a finite input that is placed on the tape starting at the TM head and
going to the right. -/
def init (l : List Γ) : Cfg Γ Λ σ :=
  ⟨some default, default, Tape.mk₁ l⟩

/-- Evaluate a TM to completion, resulting in an output list on the tape (with an indeterminate
number of blanks on the end). -/
def eval (M : Λ → Stmt Γ Λ σ) (l : List Γ) : Part (ListBlank Γ) :=
  (Turing.eval (step M) (init l)).map fun c ↦ c.Tape.right₀

end

end TM1

/-!
## TM1 emulator in TM0

To prove that TM1 computable functions are TM0 computable, we need to reduce each TM1 program to a
TM0 program. So suppose a TM1 program is given. We take the following:

* The alphabet `Γ` is the same for both TM1 and TM0
* The set of states `Λ'` is defined to be `Option Stmt₁ × σ`, that is, a TM1 statement or `none`
  representing halt, and the possible settings of the internal variables.
  Note that this is an infinite set, because `Stmt₁` is infinite. This is okay because we assume
  that from the initial TM1 state, only finitely many other labels are reachable, and there are
  only finitely many statements that appear in all of these functions.

Even though `Stmt₁` contains a statement called `halt`, we must separate it from `none`
(`some halt` steps to `none` and `none` actually halts) because there is a one step stutter in the
TM1 semantics.
-/


namespace TM1to0

variable {Γ : Type*}
variable {Λ : Type*} [Inhabited Λ]
variable {σ : Type*} [Inhabited σ]

variable (M : Λ → TM1.Stmt Γ Λ σ)

set_option linter.unusedVariables false in
/-- The base machine state space is a pair of an `Option Stmt₁` representing the current program
to be executed, or `none` for the halt state, and a `σ` which is the local state (stored in the TM,
not the tape). Because there are an infinite number of programs, this state space is infinite, but
for a finitely supported TM1 machine and a finite type `σ`, only finitely many of these states are
reachable. -/
@[nolint unusedArguments] -- We need the M assumption
def Λ' (M : Λ → TM1.Stmt Γ Λ σ) :=
  Option (TM1.Stmt Γ Λ σ) × σ

instance : Inhabited (Λ' M) :=
  ⟨(some (M default), default)⟩

open TM0.Stmt

/-- The core TM1 → TM0 translation function. Here `s` is the current value on the tape, and the
`Stmt₁` is the TM1 statement to translate, with local state `v : σ`. We evaluate all regular
instructions recursively until we reach either a `move` or `write` command, or a `goto`; in the
latter case we emit a dummy `write s` step and transition to the new target location. -/
def trAux (s : Γ) : TM1.Stmt Γ Λ σ → σ → Λ' M × TM0.Stmt Γ
  | TM1.Stmt.move d q, v => ((some q, v), move d)
  | TM1.Stmt.write a q, v => ((some q, v), write (a s v))
  | TM1.Stmt.load a q, v => trAux s q (a s v)
  | TM1.Stmt.branch p q₁ q₂, v => cond (p s v) (trAux s q₁ v) (trAux s q₂ v)
  | TM1.Stmt.goto l, v => ((some (M (l s v)), v), write s)
  | TM1.Stmt.halt, v => ((none, v), write s)

/-- The translated TM0 machine (given the TM1 machine input). -/
def tr : TM0.Machine Γ (Λ' M)
  | (none, _), _ => none
  | (some q, v), s => some (trAux M s q v)

/-- Translate configurations from TM1 to TM0. -/
def trCfg [Inhabited Γ] : TM1.Cfg Γ Λ σ → TM0.Cfg Γ (Λ' M)
  | ⟨l, v, T⟩ => ⟨(l.map M, v), T⟩

@[target]
theorem tr_respects [Inhabited Γ] :
    Respects (TM1.step M) (TM0.step (tr M))
      fun (c₁ : TM1.Cfg Γ Λ σ) (c₂ : TM0.Cfg Γ (Λ' M)) ↦ trCfg M c₁ = c₂ := by sorry

@[target]
theorem tr_eval [Inhabited Γ] (l : List Γ) : TM0.eval (tr M) l = TM1.eval M l := by sorry

variable [Fintype σ]

/-- Given a finite set of accessible `Λ` machine states, there is a finite set of accessible
machine states in the target (even though the type `Λ'` is infinite). -/
noncomputable def trStmts (S : Finset Λ) : Finset (Λ' M) :=
  (TM1.stmts M S) ×ˢ Finset.univ

attribute [local simp] TM1.stmts₁_self

@[target]
theorem tr_supports {S : Finset Λ} (ss : TM1.Supports M S) :
    TM0.Supports (tr M) ↑(trStmts M S) := by sorry

end TM1to0

/-!
## TM1(Γ) emulator in TM1(Bool)

The most parsimonious Turing machine model that is still Turing complete is `TM0` with `Γ = Bool`.
Because our construction in the previous section reducing `TM1` to `TM0` doesn't change the
alphabet, we can do the alphabet reduction on `TM1` instead of `TM0` directly.

The basic idea is to use a bijection between `Γ` and a subset of `Vector Bool n`, where `n` is a
fixed constant. Each tape element is represented as a block of `n` bools. Whenever the machine
wants to read a symbol from the tape, it traverses over the block, performing `n` `branch`
instructions to each any of the `2^n` results.

For the `write` instruction, we have to use a `goto` because we need to follow a different code
path depending on the local state, which is not available in the TM1 model, so instead we jump to
a label computed using the read value and the local state, which performs the writing and returns
to normal execution.

Emulation overhead is `O(1)`. If not for the above `write` behavior it would be 1-1 because we are
exploiting the 0-step behavior of regular commands to avoid taking steps, but there are
nevertheless a bounded number of `write` calls between `goto` statements because TM1 statements are
finitely long.
-/


namespace TM1to1

open TM1
variable {Γ : Type*}

@[target]
theorem exists_enc_dec [Inhabited Γ] [Finite Γ] :
    ∃ (n : ℕ) (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ),
      enc default = Vector.replicate n false ∧ ∀ a, dec (enc a) = a := by sorry

variable (Γ)
variable (Λ σ : Type*)

/-- The configuration state of the TM. -/
inductive Λ'
  | normal : Λ → Λ'
  | write : Γ → Stmt Γ Λ σ → Λ'

variable {Γ Λ σ}

instance [Inhabited Λ] : Inhabited (Λ' Γ Λ σ) :=
  ⟨Λ'.normal default⟩

/-- Read a vector of length `n` from the tape. -/
def readAux : ∀ n, (List.Vector Bool n → Stmt Bool (Λ' Γ Λ σ) σ) → Stmt Bool (Λ' Γ Λ σ) σ
  | 0, f => f Vector.nil
  | i + 1, f =>
    Stmt.branch (fun a _ ↦ a) (Stmt.move Dir.right <| readAux i fun v ↦ f (true ::ᵥ v))
      (Stmt.move Dir.right <| readAux i fun v ↦ f (false ::ᵥ v))

variable (n : ℕ) (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)

/-- A move left or right corresponds to `n` moves across the super-cell. -/
def move (d : Dir) (q : Stmt Bool (Λ' Γ Λ σ) σ) : Stmt Bool (Λ' Γ Λ σ) σ :=
  (Stmt.move d)^[n] q

variable {n}

/-- To read a symbol from the tape, we use `readAux` to traverse the symbol,
then return to the original position with `n` moves to the left. -/
def read (f : Γ → Stmt Bool (Λ' Γ Λ σ) σ) : Stmt Bool (Λ' Γ Λ σ) σ :=
  readAux n fun v ↦ move n Dir.left <| f (dec v)

/-- Write a list of bools on the tape. -/
def write : List Bool → Stmt Bool (Λ' Γ Λ σ) σ → Stmt Bool (Λ' Γ Λ σ) σ
  | [], q => q
  | a :: l, q => (Stmt.write fun _ _ ↦ a) <| Stmt.move Dir.right <| write l q

/-- Translate a normal instruction. For the `write` command, we use a `goto` indirection so that
we can access the current value of the tape. -/
def trNormal : Stmt Γ Λ σ → Stmt Bool (Λ' Γ Λ σ) σ
  | Stmt.move d q => move n d <| trNormal q
  | Stmt.write f q => read dec fun a ↦ Stmt.goto fun _ s ↦ Λ'.write (f a s) q
  | Stmt.load f q => read dec fun a ↦ (Stmt.load fun _ s ↦ f a s) <| trNormal q
  | Stmt.branch p q₁ q₂ =>
    read dec fun a ↦ Stmt.branch (fun _ s ↦ p a s) (trNormal q₁) (trNormal q₂)
  | Stmt.goto l => read dec fun a ↦ Stmt.goto fun _ s ↦ Λ'.normal (l a s)
  | Stmt.halt => Stmt.halt

@[target]
theorem stepAux_move (d : Dir) (q : Stmt Bool (Λ' Γ Λ σ) σ) (v : σ) (T : Tape Bool) :
    stepAux (move n d q) v T = stepAux q v ((Tape.move d)^[n] T) := by sorry

@[target]
theorem supportsStmt_move {S : Finset (Λ' Γ Λ σ)} {d : Dir} {q : Stmt Bool (Λ' Γ Λ σ) σ} :
    SupportsStmt S (move n d q) = SupportsStmt S q := by sorry

@[target]
theorem supportsStmt_write {S : Finset (Λ' Γ Λ σ)} {l : List Bool} {q : Stmt Bool (Λ' Γ Λ σ) σ} :
    SupportsStmt S (write l q) = SupportsStmt S q := by sorry

@[target]
theorem supportsStmt_read {S : Finset (Λ' Γ Λ σ)} :
    ∀ {f : Γ → Stmt Bool (Λ' Γ Λ σ) σ}, (∀ a, SupportsStmt S (f a)) →
      SupportsStmt S (read dec f) := by sorry

variable (M : Λ → TM1.Stmt Γ Λ σ)

section
variable [Inhabited Γ] (enc0 : enc default = Vector.replicate n false)

section
variable {enc}

/-- The low level tape corresponding to the given tape over alphabet `Γ`. -/
def trTape' (L R : ListBlank Γ) : Tape Bool := by
  refine
      Tape.mk' (L.flatMap (fun x ↦ (enc x).toList.reverse) ⟨n, ?_⟩)
        (R.flatMap (fun x ↦ (enc x).toList) ⟨n, ?_⟩) <;>
    simp only [enc0, Vector.replicate, List.reverse_replicate, Bool.default_bool, Vector.toList_mk]

/-- The low level tape corresponding to the given tape over alphabet `Γ`. -/
def trTape (T : Tape Γ) : Tape Bool :=
  trTape' enc0 T.left T.right₀

@[target]
theorem trTape_mk' (L R : ListBlank Γ) : trTape enc0 (Tape.mk' L R) = trTape' enc0 L R := by sorry

end

/-- The top level program. -/
def tr : Λ' Γ Λ σ → Stmt Bool (Λ' Γ Λ σ) σ
  | Λ'.normal l => trNormal dec (M l)
  | Λ'.write a q => write (enc a).toList <| move n Dir.left <| trNormal dec q

/-- The machine configuration translation. -/
def trCfg : Cfg Γ Λ σ → Cfg Bool (Λ' Γ Λ σ) σ
  | ⟨l, v, T⟩ => ⟨l.map Λ'.normal, v, trTape enc0 T⟩

variable {enc}

@[target]
theorem trTape'_move_left (L R : ListBlank Γ) :
    (Tape.move Dir.left)^[n] (trTape' enc0 L R) = trTape' enc0 L.tail (R.cons L.head) := by sorry

@[target]
theorem trTape'_move_right (L R : ListBlank Γ) :
    (Tape.move Dir.right)^[n] (trTape' enc0 L R) = trTape' enc0 (L.cons R.head) R.tail := by sorry

@[target]
theorem stepAux_write (q : Stmt Bool (Λ' Γ Λ σ) σ) (v : σ) (a b : Γ) (L R : ListBlank Γ) :
    stepAux (write (enc a).toList q) v (trTape' enc0 L (ListBlank.cons b R)) =
      stepAux q v (trTape' enc0 (ListBlank.cons a L) R) := by sorry

variable (encdec : ∀ a, dec (enc a) = a)
include encdec

@[target]
theorem stepAux_read (f : Γ → Stmt Bool (Λ' Γ Λ σ) σ) (v : σ) (L R : ListBlank Γ) :
    stepAux (read dec f) v (trTape' enc0 L R) = stepAux (f R.head) v (trTape' enc0 L R) := by sorry

variable {enc0} in
@[target]
theorem tr_respects :
    Respects (step M) (step (tr enc dec M)) fun c₁ c₂ ↦ trCfg enc enc0 c₁ = c₂ := by sorry

end


variable [Fintype Γ]

open scoped Classical in
/-- The set of accessible `Λ'.write` machine states. -/
noncomputable def writes : Stmt Γ Λ σ → Finset (Λ' Γ Λ σ)
  | Stmt.move _ q => writes q
  | Stmt.write _ q => (Finset.univ.image fun a ↦ Λ'.write a q) ∪ writes q
  | Stmt.load _ q => writes q
  | Stmt.branch _ q₁ q₂ => writes q₁ ∪ writes q₂
  | Stmt.goto _ => ∅
  | Stmt.halt => ∅

open scoped Classical in
/-- The set of accessible machine states, assuming that the input machine is supported on `S`,
are the normal states embedded from `S`, plus all write states accessible from these states. -/
noncomputable def trSupp (S : Finset Λ) : Finset (Λ' Γ Λ σ) :=
  S.biUnion fun l ↦ insert (Λ'.normal l) (writes (M l))

open scoped Classical in
@[target]
theorem tr_supports [Inhabited Λ] {S : Finset Λ} (ss : Supports M S) :
    Supports (tr enc dec M) (trSupp M S) := by sorry

end TM1to1

/-!
## TM0 emulator in TM1

To establish that TM0 and TM1 are equivalent computational models, we must also have a TM0 emulator
in TM1. The main complication here is that TM0 allows an action to depend on the value at the head
and local state, while TM1 doesn't (in order to have more programming language-like semantics).
So we use a computed `goto` to go to a state that performs the desired action and then returns to
normal execution.

One issue with this is that the `halt` instruction is supposed to halt immediately, not take a step
to a halting state. To resolve this we do a check for `halt` first, then `goto` (with an
unreachable branch).
-/


namespace TM0to1

variable (Γ : Type*) [Inhabited Γ]
variable (Λ : Type*) [Inhabited Λ]

/-- The machine states for a TM1 emulating a TM0 machine. States of the TM0 machine are embedded
as `normal q` states, but the actual operation is split into two parts, a jump to `act s q`
followed by the action and a jump to the next `normal` state. -/
inductive Λ'
  | normal : Λ → Λ'
  | act : TM0.Stmt Γ → Λ → Λ'

variable {Γ Λ}

instance : Inhabited (Λ' Γ Λ) :=
  ⟨Λ'.normal default⟩

variable (M : TM0.Machine Γ Λ)

open TM1.Stmt

/-- The program. -/
def tr : Λ' Γ Λ → TM1.Stmt Γ (Λ' Γ Λ) Unit
  | Λ'.normal q =>
    branch (fun a _ ↦ (M q a).isNone) halt <|
      goto fun a _ ↦ match M q a with
      | none => default -- unreachable
      | some (q', s) => Λ'.act s q'
  | Λ'.act (TM0.Stmt.move d) q => move d <| goto fun _ _ ↦ Λ'.normal q
  | Λ'.act (TM0.Stmt.write a) q => (write fun _ _ ↦ a) <| goto fun _ _ ↦ Λ'.normal q

/-- The configuration translation. -/
def trCfg : TM0.Cfg Γ Λ → TM1.Cfg Γ (Λ' Γ Λ) Unit
  | ⟨q, T⟩ => ⟨cond (M q T.1).isSome (some (Λ'.normal q)) none, (), T⟩

@[target]
theorem tr_respects : Respects (TM0.step M) (TM1.step (tr M)) fun a b ↦ trCfg M a = b := by sorry

end TM0to1

end Turing
