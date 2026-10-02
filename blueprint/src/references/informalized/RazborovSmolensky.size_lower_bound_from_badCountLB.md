<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: size_lower_bound_from_badCountLB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# From a low-degree lower bound to an `AC⁰[p]` size lower bound

**Claim.** Let `p`, `q` be primes and `F : FeedForward (Fin 2) (Fin n) out` a circuit with
finite node types, `Unique out`, using only the gates `ACp_GateOps p` (`hUses`), and
computing `MOD q` exactly: `F.eval₁ x = (modGateOp q n).func x` for all Boolean `x`
(`hCompute`). If `LowDegreeBadCountLB (modQTarget) (circuitDegreeBound p ℓ F.depth) E`
holds — every polynomial of total degree `≤ circuitDegreeBound p ℓ F.depth` disagrees with
`MOD q` on at least `E` Boolean inputs — then `E * 2 ^ ℓ ≤ F.size * 2 ^ n`.

**Proof.** Three steps after `classical`.

1. `exists_single_poly_for_circuit_one_size` yields one polynomial `P` with
   `P.totalDegree ≤ circuitDegreeBound p ℓ F.depth` (`hdeg`) and
   `badInputCount (F.eval₁ ·) P * 2 ^ ℓ ≤ F.size * 2 ^ n` (`hbad`).
2. `hbad'`: `simpa [badInputCount, modQTarget, hCompute] using hbad` replaces the circuit's
   own output function by the `MOD q` target, legitimate because `hCompute` says they agree.
3. `hLB P hdeg` gives `E ≤ badInputCount (modQTarget) P`; `Nat.mul_le_mul_right (2 ^ ℓ)` and
   `le_trans` with `hbad'` close the goal.

**Remark.** This is the clean interface theorem: all circuit-side work is in
`exists_single_poly_for_circuit_one_size`, all algebra is in the hypothesis `hLB`.
