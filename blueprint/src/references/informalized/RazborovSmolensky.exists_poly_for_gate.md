<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: exists_poly_for_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every `AC⁰[p]` gate has a randomized low-degree approximator

**Claim.** Let `op ∈ ACp_GateOps p` and let `polys : op.ι → MvPolynomial (Fin n) (ZMod p)`
be polynomials already computed for its inputs. Then there is a finite type `Seed` (with
`Fintype`, `DecidableEq`, and `0 < Fintype.card Seed`) and a family
`P : Seed → MvPolynomial (Fin n) (ZMod p)` such that

- `(P s).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree` for every seed `s`, and
- for every Boolean `x : Fin n → Fin 2`, writing `y j = ((x j : ℕ) : ZMod p)` and
  `inputs i = (polys i).eval y`, if all `inputs i` lie in `{0, 1}` then
  `#{s | (P s).eval y ≠ (op.func (fun i ↦ bitify p (inputs i)) : ℕ)} * 2 ^ ℓ ≤ Fintype.card Seed`.

**Proof.** `classical`, then `by_cases hℓ : ℓ = 0`; otherwise `1 ≤ ℓ` and
`1 ≤ (p - 1) * ℓ` (`hmul`, from `1 < p`), and `ACp_GateOps_cases hop` splits into four
gate shapes.

- **`ℓ = 0`.** Take `Seed := PUnit` and `P := fun _ ↦ 0`. The bound is
  `card … * 1 ≤ 1`, immediate from `Finset.card_le_univ`.
- **Identity.** `Seed := PUnit`, `P := fun _ ↦ polys PUnit.unit`. Degree: the `⨆` over
  `PUnit` is that single degree, then `Nat.mul_le_mul_right` with `hmul`. Correctness:
  `cast_bitify_eq (hbits PUnit.unit)` shows the polynomial already agrees with the gate, so
  the bad filter is `∅` (proved by `ext` + `Finset.mem_filter`).
- **NOT.** `Seed := PUnit`, `P := fun _ ↦ 1 - polys 0`. Degree by
  `MvPolynomial.totalDegree_sub`, `le_ciSup`, and a `calc` inserting the factor
  `(p - 1) * ℓ ≥ 1`. Correctness by casing `inputs 0 ∈ {0, 1}` and `simp [bitify]`; again
  the bad filter is `∅`.
- **Unbounded AND of fan-in `width`.** `Seed := Fin ℓ → Finset (Fin width)`,
  `P := approxAnd p polys`. Degree is `approxAnd_totalDegree`. Correctness: `exactAnd_on_bits`
  rewrites the gate target into the Fermat product form, then
  `approxAnd_pointwise_bad_count` gives `… * 2 ^ ℓ ≤ 2 ^ (width * ℓ)` and
  `approxSeed_card` identifies that with `Fintype.card Seed`.
- **Unbounded `MOD p` of fan-in `width`.** `Seed := PUnit`, `P := fun _ ↦ exactMod p polys`.
  Degree by `exactMod_totalDegree` plus monotonicity in `ℓ` (`Nat.mul_le_mul_left`, using
  `1 ≤ ℓ`). Correctness by `exactMod_on_bits`, so the bad filter is `∅`.

**Remark.** Only the AND branch is genuinely randomized; identity, NOT, and `MOD p` are
computed *exactly*, so their seed type is a single point and the bad-seed set is literally
empty. The parameter `ℓ` is uniform across branches, which is why the deterministic
branches need `1 ≤ (p - 1) * ℓ` to absorb their degree bound into the common
`(p - 1) * ℓ * sup` shape.

**Status.** The `ℓ = 0` branch returns the zero polynomial, which approximates nothing —
admissible only because at `ℓ = 0` the conclusion degenerates to `card … ≤ 1`, so the
statement has no content there. No Lean consumers: `exists_gate_poly_family` in
`RazborovSmolensky/CircuitDegree.lean` re-derives the same four-way case analysis in the
record-based form actually used downstream.
