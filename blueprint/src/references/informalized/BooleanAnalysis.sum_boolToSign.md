<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: sum_boolToSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The two signs cancel

**Claim.** `∑ b : Bool, boolToSign b = 0`.

**Proof.** One line, `simp [boolToSign]`. The sum over the two-element type
`Bool` expands to `boolToSign false + boolToSign true = 1 + (-1) = 0`, using
the definition `boolToSign b = if b then -1 else 1`. ∎

**Remark.** This is the base case of Fourier cancellation: it is exactly why a
non-trivial Walsh character sums to zero over the cube. In `sum_chiS` the
`n`-fold product is factored coordinatewise into `∏ i, ∑ b, …` (via
`Fintype.prod_sum`), and any coordinate `i ∈ S` contributes this vanishing
factor, killing the whole product.

**Used in.** No textual call site, but the declaration carries `@[simp]`, so it
is consumed *implicitly*: in `sum_chiS` (same file) the closing `simp [hi]`
discharges `∑ b : Bool, (if i ∈ S then boolToSign b else 1) = 0` by rewriting
the `if` with `hi : i ∈ S` and then applying this lemma. It is also declared
`private`, so its simp-set membership reaches only `Basic.lean` — no downstream
file can use it, by design.
