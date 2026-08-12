<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: exists_nontrivial_qth_root_modqField -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `𝔽_{p^{q-1}}` contains a nontrivial `q`-th root of unity when `p ≠ q`

**Claim.** Let `p` and `q` be primes with `p ≠ q`, and let
`ModqField p q := GaloisField p (q - 1)`. Then there is an element
`ω : ModqField p q` with `ω ^ q = 1` and `ω ≠ 1`.

**Proof.** Three steps.

1. `exists_unit_of_order_q_modqField p q hpq` produces a unit `u` of the field
   with `orderOf u = q`.
2. Take `ω := (u : ModqField p q)`. Then `ω ^ q = 1`: apply the coercion
   `Units.val` to `pow_orderOf_eq_one u` via `congrArg` and rewrite the exponent
   with `hu` (`simpa [hu]`).
3. `ω ≠ 1`: if the coercion were `1` then `u = 1` by `Units.ext`, so
   `q = orderOf u = 1` by `hu` and `simp`, contradicting `Nat.Prime.ne_one`.

**Remark.** Since `q` is prime, an element of order exactly `q` is the same thing
as a nontrivial `q`-th root of unity, so this weaker-looking conclusion loses
nothing; the multiplicative-order work is done upstream in
`exists_unit_of_order_q_modqField` (which uses `q ∣ p ^ (q-1) - 1` from Fermat
and cyclicity of `Kˣ`).

**Used in.** The root-of-unity cube `rootCube` used by the Smolensky half of the
Razborov–Smolensky argument.
