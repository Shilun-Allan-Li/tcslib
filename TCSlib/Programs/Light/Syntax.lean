/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Vendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder
`3sum-apsp`, file `ThreeSumApsp/Lang/Syntax.lean`, at commit e1a4e6508154ea59f030480661590a9fe3018011 (2026-10-05).
Local modifications (see policy.md §2, vendored code, and the repository NOTICE):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* moved to `TCSlib/Programs/Light/Syntax.lean`, with imports remapped;
* added a `## References` section citing [AFM26];
* added the repository-standard `set_option` header;
* appended reading lemmas (`rfl`/`Iff.rfl` restatements of definitions) for TCSlib's own
  proofs, which do not unfold vendored definitions.
* added input, output, coin and halving constructs, and threaded output and coin indices
  through the affected syntax, semantics and run witnesses.
The remaining content is unchanged.
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The light language

A small imperative language with procedures and recursion, in which the paper's procedures can be
written almost as printed.  It is a proof device: a program of this language is compiled
(`compileProgram`) to the word RAM of the end statement, and the compiler is proved to keep results
and, up to a constant factor that depends on the program text only, step counts.

* A program is a finite piece of data: a list of procedure bodies.  It contains no Lean functions.
* The memory is an array of integers addressed by natural numbers.  Each running procedure has local
  variables 0, 1, 2, ….
* Arithmetic: +, −, ×, and halving rounded down. Input reads, output and coins are explicit.  Comparisons (<, =) occur as the tests of if and
  while.
* Every executed operation costs one step: each constant, variable, operation and load of an
  expression, each comparison, assignment, store, branch, call and return.
* A run is subject to limits: it forms no value of absolute value above `word`, touches no cell at
  an address ≥ `space`, and nests calls at most `depth` deep.  A run that would break a limit does
  not exist.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of this file.
-/

section

namespace Light

/-- The operations on two words. -/
inductive Op : Type
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The result of an operation. -/
def Op.eval : Op → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- Expressions: constants, local variables, operations, and the content of the memory cell at an
address. -/
inductive Expr : Type
  | const (n : ℕ)
  | var (x : ℕ)
  | op (o : Op) (a b : Expr)
  | load (a : Expr)
  deriving Repr

/-- Tests. -/
inductive Cond : Type
  | lt (a b : Expr)
  | eq (a b : Expr)
  deriving Repr

/-- Statements.  `call p args x` runs procedure number p on the values of args and puts its result
into x. -/
inductive Stmt : Type
  | skip
  | set (x : ℕ) (e : Expr)
  | store (a e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (c : Cond) (s₁ s₂ : Stmt)
  | while (c : Cond) (s : Stmt)
  | call (p : ℕ) (args : List Expr) (x : ℕ)
  | inBit (x : ℕ) (e : Expr)
  | emit (e : Expr)
  | coin (x : ℕ)
  | half (x : ℕ) (e : Expr)
  deriving Repr

/-- A program: the bodies of its procedures, numbered from 0. -/
abbrev Program : Type := List Stmt

/-- What a running procedure sees: its local variables and the memory. -/
structure State : Type where
  loc : ℕ → ℤ
  mem : ℕ → ℤ

/-- The limits on a run: largest absolute value of a word, number of memory cells, nesting depth of
calls. -/
structure Limits : Type where
  word : ℤ
  space : ℕ
  depth : ℕ
  /-- The input string read by `inBit`. -/
  input : List Bool

/-- The value of the input bit at position `p`: `1` if `0 ≤ p` and the bit there is `true`,
`0` otherwise (in particular off the input). -/
def inBitVal (x : List Bool) (p : ℤ) : ℤ := if 0 ≤ p ∧ x.getD p.toNat false = true then 1 else 0

/-- Reading `inBitVal`: `1` exactly at a nonnegative position holding `true`. -/
theorem inBitVal_eq (x : List Bool) (p : ℤ) :
    inBitVal x p = if 0 ≤ p ∧ x.getD p.toNat false = true then 1 else 0 := rfl

/-- The value of an expression. -/
def Expr.val (s : State) : Expr → ℤ
  | .const n => n
  | .var x => s.loc x
  | .op o a b => o.eval (a.val s) (b.val s)
  | .load a => s.mem (a.val s).toNat

/-- The number of steps that evaluating an expression takes: one for each of its constants,
variables, operations, loads. -/
def Expr.cost : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => a.cost + b.cost + 1
  | .load a => a.cost + 1

/-- An address within the limits. -/
def Limits.Addr (lim : Limits) (a : ℤ) : Prop := 0 ≤ a ∧ a < lim.space

/-- The evaluation of an expression stays within the limits: every value that is formed fits in a
word, and every address that is read is within the memory. -/
def Expr.Safe (lim : Limits) (s : State) : Expr → Prop
  | .const n => (n : ℤ) ≤ lim.word
  | .var _ => True
  | .op o a b => a.Safe lim s ∧ b.Safe lim s ∧ |o.eval (a.val s) (b.val s)| ≤ lim.word
  | .load a => a.Safe lim s ∧ lim.Addr (a.val s)

/-- Whether a test holds. -/
def Cond.Holds (s : State) : Cond → Prop
  | .lt a b => a.val s < b.val s
  | .eq a b => a.val s = b.val s

/-- The number of steps of a test: its two sides and the comparison. -/
def Cond.cost : Cond → ℕ
  | .lt a b => a.cost + b.cost + 1
  | .eq a b => a.cost + b.cost + 1

/-- The evaluation of a test stays within the limits. -/
def Cond.Safe (lim : Limits) (s : State) : Cond → Prop
  | .lt a b => a.Safe lim s ∧ b.Safe lim s
  | .eq a b => a.Safe lim s ∧ b.Safe lim s

/-- The local variables of a procedure that has just been called: the arguments in 0, 1, …, and 0 in
all others. -/
def frame (args : List ℤ) : ℕ → ℤ := fun i => args.getD i 0

/-- The memory that holds the list ws in the cells 0, 1, 2, … and 0 elsewhere. -/
def memOf (ws : List ℤ) : ℕ → ℤ := fun a => ws.getD a 0

/-- `Exec lim P d s σ σ' o r c`: within the limits `lim`, at call depth `d`, the statement
`s`, started in `σ`, ends in `σ'` after exactly `c` steps, emitting `o` and consuming `r`. -/
inductive Exec (lim : Limits) (P : Program) :
    ℕ → Stmt → State → State → List Bool → List Bool → ℕ → Prop
  | skip {d σ} : Exec lim P d .skip σ σ [] [] 0
  | set {d σ x e} : e.Safe lim σ →
      Exec lim P d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) } [] []
        (e.cost + 1)
  | store {d σ a e} : a.Safe lim σ → e.Safe lim σ →
      lim.Addr (a.val σ) →
      Exec lim P d (.store a e) σ
        { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } [] []
        (a.cost + e.cost + 1)
  | seq {d σ σ' σ'' s₁ s₂ o₁ o₂ r₁ r₂ c₁ c₂} : Exec lim P d s₁ σ σ' o₁ r₁ c₁ →
      Exec lim P d s₂ σ' σ'' o₂ r₂ c₂ →
      Exec lim P d (.seq s₁ s₂) σ σ'' (o₁ ++ o₂) (r₁ ++ r₂) (c₁ + c₂)
  | iteTrue {d σ σ' c s₁ s₂ o r k} : c.Safe lim σ → c.Holds σ →
      Exec lim P d s₁ σ σ' o r k → Exec lim P d (.ite c s₁ s₂) σ σ' o r (c.cost + 1 + k)
  | iteFalse {d σ σ' c s₁ s₂ o r k} : c.Safe lim σ → ¬ c.Holds σ →
      Exec lim P d s₂ σ σ' o r k → Exec lim P d (.ite c s₁ s₂) σ σ' o r (c.cost + 1 + k)
  | whileFalse {d σ c s} : c.Safe lim σ → ¬ c.Holds σ →
      Exec lim P d (.while c s) σ σ [] [] (c.cost + 1)
  | whileTrue {d σ σ' σ'' c s o₁ o₂ r₁ r₂ k₁ k₂} : c.Safe lim σ → c.Holds σ →
      Exec lim P d s σ σ' o₁ r₁ k₁ → Exec lim P d (.while c s) σ' σ'' o₂ r₂ k₂ →
      Exec lim P d (.while c s) σ σ'' (o₁ ++ o₂) (r₁ ++ r₂) (c.cost + 1 + k₁ + k₂)
  | call {d σ σ' p args x body o r k} : (∀ e ∈ args, e.Safe lim σ) → P[p]? = some body →
      d < lim.depth → Exec lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' o r k →
      Exec lim P d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩ o r
        ((args.map Expr.cost).sum + 2 + k)
  | inBit {d σ x e} : e.Safe lim σ →
      Exec lim P d (.inBit x e) σ
        { σ with loc := Function.update σ.loc x (inBitVal lim.input (e.val σ)) } [] [] (e.cost + 1)
  | emit {d σ e} : e.Safe lim σ →
      Exec lim P d (.emit e) σ σ [decide (e.val σ ≠ 0)] [] (e.cost + 1)
  | coin {d σ x} (b : Bool) :
      Exec lim P d (.coin x) σ { σ with loc := Function.update σ.loc x (if b then 1 else 0) } []
        [b] 1
  | half {d σ x e} : e.Safe lim σ →
      Exec lim P d (.half x e) σ { σ with loc := Function.update σ.loc x (e.val σ / 2) } [] []
        (e.cost + 1)

/-- Everything held in a variable or in a cell fits in a word. -/
def State.Bounded (lim : Limits) (σ : State) : Prop :=
  (∀ x, |σ.loc x| ≤ lim.word) ∧ ∀ a, |σ.mem a| ≤ lim.word

/-- Reading boundedness: every local and memory cell fits the word limit. -/
theorem State.bounded_iff (lim : Limits) (σ : State) :
    σ.Bounded lim ↔ (∀ x, |σ.loc x| ≤ lim.word) ∧ ∀ a, |σ.mem a| ≤ lim.word := Iff.rfl

/-! ## Equations for reading expressions and tests -/

/-- The add operation evaluates its two integer operands. -/
theorem Op.eval_add (a b : ℤ) :
    Op.eval .add a b = a + b := rfl

/-- The sub operation evaluates its two integer operands. -/
theorem Op.eval_sub (a b : ℤ) :
    Op.eval .sub a b = a - b := rfl

/-- The mul operation evaluates its two integer operands. -/
theorem Op.eval_mul (a b : ℤ) :
    Op.eval .mul a b = a * b := rfl

/-- Expression evaluation reads the const constructor. -/
theorem Expr.val_const (σ : State) (n : ℕ) :
    Expr.val σ (.const n) = (n : ℤ) := rfl

/-- Expression evaluation reads the var constructor. -/
theorem Expr.val_var (σ : State) (x : ℕ) :
    Expr.val σ (.var x) = σ.loc x := rfl

/-- Expression evaluation reads the op constructor. -/
theorem Expr.val_op (σ : State) (o : Op) (a b : Expr) :
    Expr.val σ (.op o a b) = o.eval (a.val σ) (b.val σ) := rfl

/-- Expression evaluation reads the load constructor. -/
theorem Expr.val_load (σ : State) (a : Expr) :
    Expr.val σ (.load a) = σ.mem (a.val σ).toNat := rfl

/-- The cost of the const expression constructor. -/
theorem Expr.cost_const (n : ℕ) :
    Expr.cost (.const n) = 1 := rfl

/-- The cost of the var expression constructor. -/
theorem Expr.cost_var (x : ℕ) :
    Expr.cost (.var x) = 1 := rfl

/-- The cost of the op expression constructor. -/
theorem Expr.cost_op (o : Op) (a b : Expr) :
    Expr.cost (.op o a b) = a.cost + b.cost + 1 := rfl

/-- Address safety means nonnegativity and strict containment in the memory. -/
theorem Limits.addr_iff (lim : Limits) (a : ℤ) :
    lim.Addr a ↔ 0 ≤ a ∧ a < lim.space := Iff.rfl

/-- Safety of the const expression constructor. -/
theorem Expr.safe_const_iff (lim : Limits) (σ : State) (n : ℕ) :
    Expr.Safe lim σ (.const n) ↔ (n : ℤ) ≤ lim.word := Iff.rfl

/-- Safety of the var expression constructor. -/
theorem Expr.safe_var_iff (lim : Limits) (σ : State) (x : ℕ) :
    Expr.Safe lim σ (.var x) ↔ True := Iff.rfl

/-- Safety of the op expression constructor. -/
theorem Expr.safe_op_iff (lim : Limits) (σ : State) (o : Op) (a b : Expr) :
    Expr.Safe lim σ (.op o a b) ↔ a.Safe lim σ ∧ b.Safe lim σ ∧ |o.eval (a.val σ) (b.val σ)| ≤ lim.word := Iff.rfl

/-- Safety of the load expression constructor. -/
theorem Expr.safe_load_iff (lim : Limits) (σ : State) (a : Expr) :
    Expr.Safe lim σ (.load a) ↔ a.Safe lim σ ∧ lim.Addr (a.val σ) := Iff.rfl

/-- The lt test holds when its evaluated operands satisfy the comparison. -/
theorem Cond.holds_lt_iff (σ : State) (a b : Expr) :
    Cond.Holds σ (.lt a b) ↔ a.val σ < b.val σ := Iff.rfl

/-- The lt test costs its two operands and one comparison. -/
theorem Cond.cost_lt (a b : Expr) :
    Cond.cost (.lt a b) = a.cost + b.cost + 1 := rfl

/-- The lt test is safe exactly when both operands are safe. -/
theorem Cond.safe_lt_iff (lim : Limits) (σ : State) (a b : Expr) :
    Cond.Safe lim σ (.lt a b) ↔ a.Safe lim σ ∧ b.Safe lim σ := Iff.rfl

/-- The eq test holds when its evaluated operands satisfy the comparison. -/
theorem Cond.holds_eq_iff (σ : State) (a b : Expr) :
    Cond.Holds σ (.eq a b) ↔ a.val σ = b.val σ := Iff.rfl

/-- The eq test is safe exactly when both operands are safe. -/
theorem Cond.safe_eq_iff (lim : Limits) (σ : State) (a b : Expr) :
    Cond.Safe lim σ (.eq a b) ↔ a.Safe lim σ ∧ b.Safe lim σ := Iff.rfl

/-- A called procedure's local is the corresponding argument, or zero if absent. -/
theorem frame_apply (args : List ℤ) (i : ℕ) :
    frame args i = args.getD i 0 := rfl

end Light
end
