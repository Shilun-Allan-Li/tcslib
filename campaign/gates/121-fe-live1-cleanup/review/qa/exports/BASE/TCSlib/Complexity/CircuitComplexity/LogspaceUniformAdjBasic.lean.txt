/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.LogspaceUniform
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The adjacency representation of circuits

[AB09, p. 112] remarks that logspace-uniformity is robust: it is equivalent to the
computability in `O(log n)` space of the functions `SIZE(n)`, `TYPE(n, i)` and
`EDGE(n, i, j)` describing `Cₙ` by its adjacency matrix, "the first `n` vertices being the
inputs and the last the output". This file defines these functions, as languages on inputs
`⟨1ⁿ, bits i⟩` and `⟨1ⁿ, ⟨bits i, bits j⟩⟩`, and the canonical circuits for which the
representation determines the circuit.

## Main definitions

* `BoolCircuit.DAGCircuit.vtype`, `BoolCircuit.DAGCircuit.Edge` — the type of a vertex
  (`none` for an input) and the edge relation.
* `BoolCircuit.DAGCircuit.IsCanonical` — arguments listed in increasing order, output last.
* `BoolCircuit.DAGCircuitFamily.sizeLang`, `typeLang`, `edgeLang` — `SIZE`, `TYPE`, `EDGE`.
* `BoolCircuit.DAGCircuitFamily.HasLogspaceAdjacency` — polynomial size, and `SIZE`, `TYPE`,
  `EDGE` in `L`.

## Main results

* `BoolCircuit.DAGCircuit.encode_eq` — the shape of the description, for scanning it.

## Divergences from [AB09]

* **`SIZE` is a threshold language** `{⟨1ⁿ, bits i⟩ | i < |Cₙ|}` (the vertices), rather
  than the binary value of `|Cₙ|`; for polynomial-size families the two are inter-computable
  in logarithmic space (count up to the first non-vertex).
* **`TYPE` is one language per type** `t : Option GateKind` (`none` = input): the vertices of
  type `t`.
* **Canonical circuits.** The adjacency matrix forgets the order and repetitions of a gate's
  arguments, which `BoolCircuit.DAGCircuit.encode` records, and [AB09]'s "last vertex is the
  output" fixes the output. The equivalence is therefore stated for canonical circuits
  (strictly increasing arguments, output = last vertex), as [AB09]'s adjacency
  representation implicitly assumes. Without canonicity the literal equivalence fails. Fix
  an undecidable set `H ⊆ ℕ` and let `Cₙ` (for `n ≥ 2`) be the single gate `∧` on the
  inputs `0, 1`, listed as `(0, 1)` if `n ∈ H` and as `(1, 0)` otherwise, with the gate as
  output. Then `SIZE`, `TYPE`, `EDGE` do not depend on `H` and are in `L`. But
  `encode Cₙ` records the argument order, so any function mapping `1ⁿ` to it (computable,
  as implicitly logspace functions are) would decide `H`.
  The output condition is [AB09, Def 6.1]'s: a circuit is a DAG with a single sink, the
  output, which a topological numbering may place last. `BoolCircuit.DAGCircuit` allows
  any output vertex. The argument-order part is removed by
  `BoolCircuit.DAGCircuitFamily.HasLogspaceAdjacency.exists_canonical_isLogspaceUniform`:
  sorting and deduplicating the arguments changes neither the circuit's function nor its
  adjacency representation.
* **Polynomial size is part of `HasLogspaceAdjacency`.** [AB09, p. 112] speaks of `SIZE`
  being computable in `O(log n)` space, which presupposes that `|Cₙ|` has `O(log n)` bits,
  i.e. polynomial size (logspace-uniform families have it,
  `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPolySize`). Our threshold `SIZE`
  language alone does not bound `|Cₙ|`, so the bound is stated explicitly.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.2.1, p. 112.)
-/

namespace BoolCircuit

open Turing Complexity

namespace DAGCircuit

variable {n : ℕ} (C : DAGCircuit n)

/-- The type of vertex `i` [AB09, p. 112]: `none` for an input, the label of the gate
otherwise (`none` also beyond the circuit). -/
def vtype (i : ℕ) : Option GateKind :=
  if i < n then none else (C.gates[i - n]?).map (·.kind)

/-- The edge relation [AB09, p. 112]: vertex `i` is an argument of the gate at vertex `j`. -/
def Edge (i j : ℕ) : Prop :=
  n ≤ j ∧ ∃ g, C.gates[j - n]? = some g ∧ i ∈ g.args

/-- A circuit is *canonical* when every gate lists its arguments in strictly increasing order
and the output is the last vertex. -/
def IsCanonical : Prop :=
  (∀ g ∈ C.gates, g.args.Sorted (· < ·)) ∧ C.output + 1 = C.size

/-- The shape of the description of a circuit. -/
lemma encode_eq : C.encode = List.replicate n true ++ false ::
    (encodeList DAGGate.encode C.gates ++ (List.replicate C.output true ++ [false])) := by
  simp [encode, encodeNat]

end DAGCircuit

namespace DAGCircuitFamily

variable (C : DAGCircuitFamily)

/-- `SIZE` [AB09, p. 112], as the language of the vertices `⟨1ⁿ, bits i⟩`, `i < |Cₙ|`. -/
def sizeLang : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ i < (C.circuit n).size}

/-- `TYPE` [AB09, p. 112]: the vertices `⟨1ⁿ, bits i⟩` of `Cₙ` of type `t`. -/
def typeLang (t : Option GateKind) : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ i < (C.circuit n).size ∧
    (C.circuit n).vtype i = t}

/-- `EDGE` [AB09, p. 112]: the edges `⟨1ⁿ, ⟨bits i, bits j⟩⟩` of `Cₙ`. -/
def edgeLang : Language Bool :=
  {y | ∃ n i j, y = pairEncode (List.replicate n true) (pairEncode (Nat.bits i) (Nat.bits j)) ∧
    (C.circuit n).Edge i j}

/-- **The adjacency representation is logspace computable** [AB09, p. 112]: the family has
polynomial size and `SIZE`, `TYPE` and `EDGE` are in `L`. -/
def HasLogspaceAdjacency : Prop :=
  C.IsPolySize ∧ C.sizeLang ∈ LOGSPACE ∧ (∀ t, C.typeLang t ∈ LOGSPACE) ∧
    C.edgeLang ∈ LOGSPACE

/-- `⟨1ⁿ, bits i⟩` is in `SIZE` iff `i` is a vertex of `Cₙ`. -/
lemma mem_sizeLang {n i : ℕ} :
    pairEncode (List.replicate n true) (Nat.bits i) ∈ C.sizeLang ↔ i < (C.circuit n).size := by
  constructor
  · rintro ⟨n', i', h, hi⟩
    obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
    rwa [LogProg.bits_injective hb]
  · exact fun h => ⟨n, i, rfl, h⟩

/-- `⟨1ⁿ, bits i⟩` is in `TYPE t` iff `i` is a vertex of `Cₙ` of type `t`. -/
lemma mem_typeLang {t : Option GateKind} {n i : ℕ} :
    pairEncode (List.replicate n true) (Nat.bits i) ∈ C.typeLang t ↔
      i < (C.circuit n).size ∧ (C.circuit n).vtype i = t := by
  constructor
  · rintro ⟨n', i', h, hi⟩
    obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
    rwa [LogProg.bits_injective hb]
  · exact fun h => ⟨n, i, rfl, h⟩

/-- `⟨1ⁿ, ⟨bits i, bits j⟩⟩` is in `EDGE` iff `i → j` is an edge of `Cₙ`. -/
lemma mem_edgeLang {n i j : ℕ} :
    pairEncode (List.replicate n true) (pairEncode (Nat.bits i) (Nat.bits j)) ∈ C.edgeLang ↔
      (C.circuit n).Edge i j := by
  constructor
  · rintro ⟨n', i', j', h, hi⟩
    obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
    have := pairEncode_injective (a₁ := (Nat.bits i, Nat.bits j))
      (a₂ := (Nat.bits i', Nat.bits j')) hb
    simp only [Prod.mk.injEq] at this
    rwa [LogProg.bits_injective this.1, LogProg.bits_injective this.2]
  · exact fun h => ⟨n, i, j, rfl, h⟩

/-- Every circuit of the family is canonical. -/
def IsCanonical : Prop :=
  ∀ n, (C.circuit n).IsCanonical

end DAGCircuitFamily

end BoolCircuit
