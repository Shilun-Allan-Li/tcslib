/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The 3SAT → 3COL gadget graph on `Fin N`

The graph of the course reduction from 3SAT to 3-colouring (`SATtoColor.ReductionGraph`,
`Complexity/NPReductions/ThreeSATToColoring.lean`, course material of CS 294-268, UC Berkeley,
Spring 2026) laid out on the vertex set `{0, …, N - 1}` so that a Turing machine can print its
adjacency matrix. For `K` variables, literal codes are `ℓ < 2K` (variable `ℓ / 2`, positive iff
`ℓ` is even), clause codes are `c < (2K)³` (the three literals `c % 2K`, `(c / 2K) % 2K`,
`c / (2K)²`), and the vertices are

* the palette `0, 1, 2` (base, true, false);
* the literal nodes `3 + ℓ` for `ℓ < 2K`;
* the six gadget nodes `3 + 2K + 6c + i` (`i < 6`) of **every** clause code `c < (2K)³`,

`N = 3 + 2K + 6(2K)³` in all, one vertex for each vertex of `ReductionGraph` over `Fin K` (whose
vertex type has a gadget for every clause, present in the formula or not). The edges are those of
the course reduction: the palette triangle; the base to every literal; each positive literal to
its negation; the gadget triangles `{0,1,2}`, `{3,4,5}` and the edge `{2,3}` inside the gadget of
each clause **of the formula** (the test `mem`); gadget nodes `0, 1, 4` to the clause's first,
second and third literal; gadget node `5` to the base and to the false node.

This is the graph of Stockmeyer's reduction from 3SAT [St73, proof of the Theorem, part 1),
p. 22, Fig. 1 p. 24] in the course material's variant: gadget nodes `0, …, 5` are [St73]'s
`v₁, v₂, v₄, v₅, v₃, v₆`, with the literals attached at `0, 1, 4` as at `v₁, v₂, v₃`; the
palette is a triangle (base, true, false) instead of [St73]'s arc `{t₁, t₂}` (base, false), and
gadget node `5` is joined to the base as well as to the false node, which [St73] does not do.

## Main definitions

* `TCSlib.Cryptography.LevinHardness.gadgetN` — the number of vertices `N = 3 + 2K + 6(2K)³`.
* `TCSlib.Cryptography.LevinHardness.clauseLit` — the `j`-th literal code of a clause code.
* `TCSlib.Cryptography.LevinHardness.litVal`, `TCSlib.Cryptography.LevinHardness.clauseSat` — the
  truth value of a literal code and of a clause code under an assignment.
* `TCSlib.Cryptography.LevinHardness.gadgetEdge` — the directed edge relation (one orientation).
* `TCSlib.Cryptography.LevinHardness.gadgetAdj` — the symmetric loopless adjacency.
* `TCSlib.Cryptography.LevinHardness.gadgetGraph` — the graph on `Fin (gadgetN K)`.

## Main results

* readers `gadgetN_eq`, `clauseLit_eq`, `litVal_eq`, `clauseSat_eq`, `gadgetEdge_eq`,
  `gadgetAdj_eq`, `gadgetGraph_apply`;
* `gadgetAdj_comm`, `gadgetAdj_self` — symmetry and looplessness.

## References

* CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT → 3-colouring
  reduction as formalized in `Complexity/NPReductions/ThreeSATToColoring.lean`.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009.
* [St73] L. Stockmeyer, *Planar 3-Colorability is Polynomial Complete*, ACM SIGACT News 5(3),
  July 1973, pp. 19–25. (Theorem, p. 22; proof pp. 21–22; Fig. 1, p. 24. The printed pages of
  this issue are bound out of order: the proof of part 1), the reduction from 3SAT, runs from
  p. 22 back to p. 21.)
-/

namespace TCSlib.Cryptography.LevinHardness

/-- **The number of vertices of the gadget graph** for `K` variables:
`gadgetN K = 3 + 2K + 6 (2K)³` (palette, literal nodes, six nodes per clause code). -/
def gadgetN (K : ℕ) : ℕ := 3 + 2 * K + 6 * (2 * K) ^ 3

/-- The defining equation of `gadgetN`: `gadgetN K = 3 + 2K + 6 (2K)³`. -/
theorem gadgetN_eq (K : ℕ) : gadgetN K = 3 + 2 * K + 6 * (2 * K) ^ 3 := rfl

/-- **The `j`-th literal code of the clause code `c`** for `K` variables (`j = 0, 1, 2`):
`clauseLit K c j = (c / (2K)^j) % 2K` for `j < 2` and `c / (2K)²` for `j = 2`. -/
def clauseLit (K c : ℕ) (j : Fin 3) : ℕ :=
  if j = 2 then c / (2 * K) ^ 2 else c / (2 * K) ^ (j : ℕ) % (2 * K)

/-- The defining equation of `clauseLit`. -/
theorem clauseLit_eq (K c : ℕ) (j : Fin 3) :
    clauseLit K c j = if j = 2 then c / (2 * K) ^ 2 else c / (2 * K) ^ (j : ℕ) % (2 * K) := rfl

/-- **The truth value of a literal code** under the assignment `val`: the code `ℓ` is the variable
`ℓ / 2`, positive iff `ℓ` is even, so `litVal val ℓ = val (ℓ / 2)` for even `ℓ` and
`!val (ℓ / 2)` for odd `ℓ`. -/
def litVal (val : ℕ → Bool) (ℓ : ℕ) : Bool :=
  if ℓ % 2 = 0 then val (ℓ / 2) else !val (ℓ / 2)

/-- The defining equation of `litVal`. -/
theorem litVal_eq (val : ℕ → Bool) (ℓ : ℕ) :
    litVal val ℓ = if ℓ % 2 = 0 then val (ℓ / 2) else !val (ℓ / 2) := rfl

/-- **A clause code is satisfied** by `val` when one of its three literal codes is true:
`clauseSat K val c = litVal val (clauseLit K c 0) || litVal val (clauseLit K c 1) ||
litVal val (clauseLit K c 2)`. -/
def clauseSat (K : ℕ) (val : ℕ → Bool) (c : ℕ) : Bool :=
  litVal val (clauseLit K c 0) || litVal val (clauseLit K c 1) || litVal val (clauseLit K c 2)

/-- The defining equation of `clauseSat`. -/
theorem clauseSat_eq (K : ℕ) (val : ℕ → Bool) (c : ℕ) :
    clauseSat K val c = (litVal val (clauseLit K c 0) || litVal val (clauseLit K c 1) ||
      litVal val (clauseLit K c 2)) := rfl

/-- **One orientation of the edges of the gadget graph** on vertices `t, t'` (natural numbers),
for `K` variables and the clause-membership test `mem` on clause codes, following the edge relation
of the course reduction (`SATtoColor.EdgeRelation`):
* palette–palette (`t, t' < 3`);
* base–literal (`t = 0`, `3 ≤ t' < 3 + 2K`);
* positive literal `3 + 2v` – negative literal `3 + 2v + 1`;
* inside the gadget of a clause code `c` with `mem c`: index pairs `(0,1), (0,2), (1,2), (2,3),
  (3,4), (3,5), (4,5)`;
* literal `3 + ℓ` – gadget node `i` of clause `c` when `ℓ` is the clause's literal `0, 1, 2` and
  `i = 0, 1, 4` respectively;
* gadget node `5` – base and gadget node `5` – false node (`t' = 0, 2`). -/
def gadgetEdge (K : ℕ) (mem : ℕ → Bool) (t t' : ℕ) : Bool :=
  let L := 3 + 2 * K
  let N := gadgetN K
  (decide (t < 3) && decide (t' < 3)) ||
  (decide (t = 0) && decide (3 ≤ t') && decide (t' < L)) ||
  (decide (3 ≤ t) && decide (t < L) && decide ((t - 3) % 2 = 0) && decide (t' = t + 1)) ||
  (decide (L ≤ t) && decide (t < N) && decide (L ≤ t') && decide (t' < N) &&
    decide ((t - L) / 6 = (t' - L) / 6) && mem ((t - L) / 6) &&
    decide (((t - L) % 6, (t' - L) % 6) ∈
      [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5)])) ||
  (decide (3 ≤ t) && decide (t < L) && decide (L ≤ t') && decide (t' < N) &&
    ((decide (t - 3 = clauseLit K ((t' - L) / 6) 0) && decide ((t' - L) % 6 = 0)) ||
     (decide (t - 3 = clauseLit K ((t' - L) / 6) 1) && decide ((t' - L) % 6 = 1)) ||
     (decide (t - 3 = clauseLit K ((t' - L) / 6) 2) && decide ((t' - L) % 6 = 4)))) ||
  (decide (L ≤ t) && decide (t < N) && decide ((t - L) % 6 = 5) && decide (t' = 0 ∨ t' = 2))

/-- The defining equation of `gadgetEdge` (see its docstring for the cases).

**Proof sketch.** `rfl`: the right-hand side is the body of `gadgetEdge` with its two `let`s
inlined. -/
theorem gadgetEdge_eq (K : ℕ) (mem : ℕ → Bool) (t t' : ℕ) :
    gadgetEdge K mem t t' =
      ((decide (t < 3) && decide (t' < 3)) ||
      (decide (t = 0) && decide (3 ≤ t') && decide (t' < 3 + 2 * K)) ||
      (decide (3 ≤ t) && decide (t < 3 + 2 * K) && decide ((t - 3) % 2 = 0) &&
        decide (t' = t + 1)) ||
      (decide (3 + 2 * K ≤ t) && decide (t < gadgetN K) && decide (3 + 2 * K ≤ t') &&
        decide (t' < gadgetN K) &&
        decide ((t - (3 + 2 * K)) / 6 = (t' - (3 + 2 * K)) / 6) &&
        mem ((t - (3 + 2 * K)) / 6) &&
        decide (((t - (3 + 2 * K)) % 6, (t' - (3 + 2 * K)) % 6) ∈
          [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5)])) ||
      (decide (3 ≤ t) && decide (t < 3 + 2 * K) && decide (3 + 2 * K ≤ t') &&
        decide (t' < gadgetN K) &&
        ((decide (t - 3 = clauseLit K ((t' - (3 + 2 * K)) / 6) 0) &&
            decide ((t' - (3 + 2 * K)) % 6 = 0)) ||
         (decide (t - 3 = clauseLit K ((t' - (3 + 2 * K)) / 6) 1) &&
            decide ((t' - (3 + 2 * K)) % 6 = 1)) ||
         (decide (t - 3 = clauseLit K ((t' - (3 + 2 * K)) / 6) 2) &&
            decide ((t' - (3 + 2 * K)) % 6 = 4)))) ||
      (decide (3 + 2 * K ≤ t) && decide (t < gadgetN K) &&
        decide ((t - (3 + 2 * K)) % 6 = 5) && decide (t' = 0 ∨ t' = 2))) := rfl

/-- **The adjacency of the gadget graph**: `t` and `t'` are adjacent iff they are distinct and an
edge joins them in either orientation, `gadgetAdj K mem t t' = (t ≠ t') ∧ (gadgetEdge K mem t t' ∨
gadgetEdge K mem t' t)` (the symmetrization of `SATtoColor.ReductionGraph`). -/
def gadgetAdj (K : ℕ) (mem : ℕ → Bool) (t t' : ℕ) : Bool :=
  decide (t ≠ t') && (gadgetEdge K mem t t' || gadgetEdge K mem t' t)

/-- The defining equation of `gadgetAdj`. -/
theorem gadgetAdj_eq (K : ℕ) (mem : ℕ → Bool) (t t' : ℕ) :
    gadgetAdj K mem t t' =
      (decide (t ≠ t') && (gadgetEdge K mem t t' || gadgetEdge K mem t' t)) := rfl

/-- The gadget adjacency is symmetric: `gadgetAdj K mem t t' = gadgetAdj K mem t' t`. -/
theorem gadgetAdj_comm (K : ℕ) (mem : ℕ → Bool) (t t' : ℕ) :
    gadgetAdj K mem t t' = gadgetAdj K mem t' t := by
  unfold gadgetAdj
  rw [Bool.or_comm]
  by_cases h : t = t' <;> simp [h, eq_comm]

/-- The gadget adjacency is loopless: `gadgetAdj K mem t t = false`. -/
theorem gadgetAdj_self (K : ℕ) (mem : ℕ → Bool) (t : ℕ) : gadgetAdj K mem t t = false := by
  simp [gadgetAdj]

/-- **The gadget graph** on `Fin (gadgetN K)` for `K` variables and the clause-membership test
`mem`: `gadgetGraph K mem u v = gadgetAdj K mem u v`. -/
def gadgetGraph (K : ℕ) (mem : ℕ → Bool) : Graph (gadgetN K) :=
  fun u v => gadgetAdj K mem u v

/-- The entries of the gadget graph: `gadgetGraph K mem u v = gadgetAdj K mem u v`. -/
theorem gadgetGraph_apply (K : ℕ) (mem : ℕ → Bool) (u v : Fin (gadgetN K)) :
    gadgetGraph K mem u v = gadgetAdj K mem u v := rfl

end TCSlib.Cryptography.LevinHardness
