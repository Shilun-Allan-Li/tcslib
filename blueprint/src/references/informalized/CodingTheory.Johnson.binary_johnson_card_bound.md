<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: binary_johnson_card_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Binary Johnson bound for a constant-weight code

**Claim.** Let `0 < n`, `1 ≤ d`, `2 * d ≤ n`, and let `C : Finset (BitVec n)`
satisfy `d ≤ hdist x y` for all distinct `x y ∈ C` and `wt x ≤ w` for all
`x ∈ C`. If `(w : ℝ) ≤ J2 n d`, where
`J2 n d = (n - Real.sqrt (n * (n - 2*d))) / 2`, then `C.card ≤ 2 * n`.

**Proof.** Instantiate the parametric theorem at `α := alpha n d`.

1. `0 ≤ α` by `alpha_nonneg`.
2. `α < 1` by `alpha_lt_one_of_hd1` (this is where `1 ≤ d` is used).
3. Every shifted codeword is nonzero: `shifted_ne_zero_of_alpha_lt_one` with
   steps 1–2 — with `0 ≤ α < 1` each coordinate of `pmOne x - α • ones` is
   `1 - α` or `-1 - α`, both nonzero.
4. The arithmetic inequality
   `(n - 2*d) + α^2*n + 2*α*(2*w - n) ≤ 0` is `johnson_arith` applied to
   `hn`, `hd` and `hwJ`.
5. `exact binary_johnson_card_bound_parametric hn C hpair hwt α …` with
   steps 1, 3, 4. ∎

**Used in.** `binary_johnson_card_bound_of_admissible`, and through it
`binary_johnson_bound_radius`. The choice `α = Real.sqrt ((n - 2*d)/n)` is
exactly the one making the Rankin inner-product bound vanish at the Johnson
radius `J2 n d`.
