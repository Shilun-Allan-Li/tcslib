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

The two-party deterministic model of Yao [RY20, Ch. 1]: a protocol is a binary tree whose
internal nodes are owned by Alice or Bob and send one bit computed from the owner's input;
its complexity is the depth of the tree.

## Main definitions

- `Protocol`: deterministic two-party protocols as an inductive tree with `output`, `alice`
  and `bob` nodes
- `Protocol.run`: execute a protocol on inputs `x : X` and `y : Y`, returning the output value
- `Protocol.complexity`: worst-case number of bits exchanged by a protocol
- `Protocol.Equiv`, `Protocol.Computes`: extensional equality of protocols and the predicate
  "protocol `p` computes `f`"
- `Protocol.comap`: pull back a protocol along input-transforming functions
- `Protocol.swap`: swap the roles of Alice and Bob in a protocol

## Main results

- `Protocol.swap_run`, `Protocol.swap_complexity`, `Protocol.swap_swap`: swapping preserves
  the outcome (with arguments exchanged) and the complexity, and is an involution
- `Protocol.comap_run`, `Protocol.comap_complexity`: pulling back preserves the outcome
  (composed with the input maps) and the complexity

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.
* [Yao79] A. C.-C. Yao, "Some complexity questions related to distributive computing",
  *STOC 1979*, pp. 209–213.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Deterministic

/-- A deterministic two-party communication protocol where Alice holds input `x : X`,
Bob holds input `y : Y`, and the protocol computes a value of type `α`.
At each step, either Alice or Bob sends a single bit based on their input,
and the protocol branches accordingly. [RY20, Ch. 1, Definition (2-party deterministic
protocol)]. The tree is represented inductively: a leaf carries the output value, and an
internal node carries its owner's message function together with the two subtrees. -/
inductive Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice (f : X → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α
  | bob (f : Y → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α

namespace Protocol

variable {X Y α : Type*}

/-- Executes the protocol on inputs `x` and `y`, returning the output value: starting at
the root, the owner of the current node evaluates its message function on its own input and
both parties descend to the indicated child, until a leaf is reached.
[RY20, Ch. 1, Definition (outcome)]. -/
def run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | .output val => val
  | .alice f P => (P (f x)).run x y
  | .bob f P => (P (f y)).run x y

/-- The communication complexity of a protocol, i.e. the worst-case number of bits exchanged,
which is the depth of the protocol tree.
[RY20, Ch. 1, Definition (computing a function, complexity, rounds)]. -/
def complexity : Protocol X Y α → ℕ
  | .output _ => 0
  | .alice _ P => 1 + max (P false).complexity (P true).complexity
  | .bob _ P => 1 + max (P false).complexity (P true).complexity

/-- Two protocols are equivalent if they produce the same output on all inputs. -/
def Equiv (p q : Protocol X Y α) : Prop :=
  p.run = q.run

/-- A protocol computes a function `f` if it produces `f x y` on all inputs `(x, y)`.
[RY20, Ch. 1, Definition (computing a function, complexity, rounds)]. Deviation: the output
type `α` is arbitrary rather than Boolean, and the leaf must output `f x y` itself rather
than merely determine it. -/
def Computes (p : Protocol X Y α) (f : X → Y → α) : Prop :=
  p.run = f

/-- Swaps the roles of Alice and Bob, producing a protocol on `Y × X` from one on `X × Y`.
Alice nodes become bob nodes and vice versa. -/
def swap : Protocol X Y α → Protocol Y X α
  | .output val => .output val
  | .alice f P => .bob f (fun b => (P b).swap)
  | .bob f P => .alice f (fun b => (P b).swap)

/-- Running the swapped protocol on `(y, x)` gives the same output as running the original
protocol on `(x, y)`. -/
@[simp]
theorem swap_run (p : Protocol X Y α) (x : X) (y : Y) :
    p.swap.run y x = p.run x y := by
  induction p <;> simp [swap, run, *]

/-- Swapping the roles of Alice and Bob does not change the complexity of a protocol. -/
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

/-- Running the pulled-back protocol on `(x', y')` gives the same output as running the
original protocol on `(fX x', fY y')`. -/
@[simp]
theorem comap_run {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    (p.comap fX fY).run x' y' = p.run (fX x') (fY y') := by
  induction p <;> simp [comap, run, *]

/-- Pulling a protocol back along input maps does not change its complexity. -/
@[simp]
theorem comap_complexity {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    (p.comap fX fY).complexity = p.complexity := by
  induction p <;> simp [comap, complexity, *]

end Protocol

end Deterministic

end CommunicationComplexity
