<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: exists_gate_poly_family -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every `AC⁰[p]` gate has an approximator family

**Claim.** For `n ℓ : ℕ`, a gate `op : GateOp (Fin 2)` and `hop : op ∈ ACp_GateOps p`,
there exists a `GatePolyFamily p n ℓ op`. It is stated as
`∃ _ : GatePolyFamily p n ℓ op, True`, i.e. bare nonemptiness; the witness packages
a nonempty finite seed type, a polynomial `poly polys s` per seed, the degree bound
`totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree`, and, on Boolean-valued
inputs, `(#bad seeds) * 2 ^ ℓ ≤ Fintype.card Seed`.

**Proof.** `classical`, then `by_cases hℓ : ℓ = 0`.

- **`ℓ = 0`** — `Seed := PUnit`, `poly := 0`. Degree by `simp`; the bad bound is
  vacuous (`2 ^ 0 = 1`), closed by `Finset.card_le_univ`. No accuracy is claimed
  at `ℓ = 0`.
- **`ℓ ≠ 0`** — record `hℓ1 : 1 ≤ ℓ` and `hmul : 1 ≤ (p - 1) * ℓ` (from
  `Fact.out : Nat.Prime p`, `omega`, `Nat.mul_pos`), then split with
  `ACp_GateOps_cases` into four gates:
  - **identity** — `poly polys _ := polys PUnit.unit`, seed `PUnit`. Degree: `⨆`
    over `PUnit` collapses (`simp`), then `Nat.mul_le_mul_right … hmul`. Bad set
    `∅` (`ext` + `Finset.mem_filter`), since `cast_bitify_eq` gives exact agreement.
  - **NOT** (`⟨Fin 1, fun x ↦ 1 - x 0⟩`) — `poly polys _ := 1 - polys 0`. Degree
    by `MvPolynomial.totalDegree_sub`, `le_ciSup` and `hmul` in a `calc`; bad set
    `∅` by `rcases` on the input bit and `simp [bitify]`.
  - **unbounded AND** (`⟨Fin width, fun x ↦ ∏ i, x i⟩`) — the only randomized
    case: `Seed := Fin ℓ → Finset (Fin width)`, `poly := approxAnd p`, degree from
    `approxAnd_totalDegree`. `exactAnd_on_bits` rewrites the intended output as
    `∏ i, (1 - (1 - eval y (polys i)) ^ (p - 1))`, matching the set bounded by
    `approxAnd_pointwise_bad_count`; that gives `… * 2 ^ ℓ ≤ 2 ^ (width * ℓ)`,
    which is `Fintype.card Seed` by `approxSeed_card`.
  - **`MOD p`** (`modGateOp p width`) — seed `PUnit`, `poly := exactMod p`.
    Degree from `exactMod_totalDegree` plus `(p - 1) * sup ≤ (p - 1) * (ℓ * sup)`
    via `hℓ1`; bad set `∅` by `exactMod_on_bits`.

**Remark.** Three of the four gate types are simulated *exactly* over `ZMod p`, so
only unbounded AND spends randomness; the uniform `2 ^ ℓ` accounting is what lets
the layer induction treat all gates alike.
