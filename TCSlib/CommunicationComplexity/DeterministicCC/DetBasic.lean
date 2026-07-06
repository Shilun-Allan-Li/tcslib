/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.Tactic.Common

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Communication Protocol

## Main results

- `Protocol.run`: Execute a protocol on inputs `x : X` and `y : Y`, returning the output value
- `Protocol.complexity`: Worst-case number of bits exchanged by a protocol
- `Protocol.comap`: Pull back a protocol along input-transforming functions
- `Protocol.swap`: Swap the roles of Alice and Bob in a protocol

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Deterministic

/-- A deterministic two-party communication protocol where Alice holds input `x : X`,
Bob holds input `y : Y`, and the protocol computes a value of type `α`.
At each step, either Alice or Bob sends a single bit based on their input,
and the protocol branches accordingly. -/
inductive Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice (f : X → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α
  | bob (f : Y → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α

namespace Protocol

variable {X Y α : Type*}

/-- Executes the protocol on inputs `x` and `y`, returning the output value. -/
def run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | .output val => val
  | .alice f P => (P (f x)).run x y
  | .bob f P => (P (f y)).run x y

/-- The communication complexity of a protocol, i.e. the worst-case number of bits exchanged. -/
def complexity : Protocol X Y α → ℕ
  | .output _ => 0
  | .alice _ P => 1 + max (P false).complexity (P true).complexity
  | .bob _ P => 1 + max (P false).complexity (P true).complexity

/-- Two protocols are equivalent if they produce the same output on all inputs. -/
def Equiv (p q : Protocol X Y α) : Prop :=
  p.run = q.run

/-- A protocol computes a function `f` if it produces `f x y` on all inputs `(x, y)`. -/
def Computes (p : Protocol X Y α) (f : X → Y → α) : Prop :=
  p.run = f

/-- Swaps the roles of Alice and Bob, producing a protocol on `Y × X` from one on `X × Y`.
Alice nodes become bob nodes and vice versa. -/
def swap : Protocol X Y α → Protocol Y X α
  | .output val => .output val
  | .alice f P => .bob f (fun b => (P b).swap)
  | .bob f P => .alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol X Y α) (x : X) (y : Y) :
    p.swap.run y x = p.run x y := by
  induction p <;> simp [swap, run, *]

@[simp]
theorem swap_complexity (p : Protocol X Y α) :
    p.swap.complexity = p.complexity := by
  induction p <;> simp [swap, complexity, *]

/-- Swapping Alice and Bob twice returns the original protocol. -/
@[simp]
theorem swap_swap (p : Protocol X Y α) :
    p.swap.swap = p := by
  induction p <;> simp [swap, *]

/-- An alice protocol on `X × Y` can be converted into a bob protocol on `Y × X`
with the same run behavior (up to argument swap) and complexity.
Useful for reducing the bob case to the alice case in inductive proofs. -/
theorem alice_to_bob (f : X → Bool) (P : Bool → Protocol X Y α) :
    ∃ q : Protocol Y X α,
      (∀ x y, q.run y x = (alice f P).run x y) ∧
      q.complexity = (alice f P).complexity :=
  ⟨(alice f P).swap, fun x y => swap_run _ x y, swap_complexity _⟩

/-- A bob protocol on `X × Y` can be converted into an alice protocol on `Y × X`
with the same run behavior (up to argument swap) and complexity.
Useful for reducing the alice case to the bob case in inductive proofs. -/
theorem bob_to_alice (f : Y → Bool) (P : Bool → Protocol X Y α) :
    ∃ q : Protocol Y X α,
      (∀ x y, q.run y x = (bob f P).run x y) ∧
      q.complexity = (bob f P).complexity :=
  ⟨(bob f P).swap, fun x y => swap_run _ x y, swap_complexity _⟩

/-- Pull back a protocol along functions `fX : X' → X` and `fY : Y' → Y`.
The resulting protocol over `X' × Y'` simulates the original by applying
`fX` and `fY` to the inputs before each message function. -/
def comap {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) : Protocol X' Y' α :=
  match p with
  | .output val => .output val
  | .alice f P => .alice (f ∘ fX) (fun b => (P b).comap fX fY)
  | .bob f P => .bob (f ∘ fY) (fun b => (P b).comap fX fY)

@[simp]
theorem comap_run {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    (p.comap fX fY).run x' y' = p.run (fX x') (fY y') := by
  induction p <;> simp [comap, run, *]

@[simp]
theorem comap_complexity {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    (p.comap fX fY).complexity = p.complexity := by
  induction p <;> simp [comap, complexity, *]

end Protocol

end Deterministic

end CommunicationComplexity
