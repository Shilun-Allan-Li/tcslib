<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: exists_unit_of_order_q_modqField -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A unit of order exactly `q` in `𝔽_(p^(q-1))`

**Claim.** For primes `p ≠ q`, the unit group of `K = ModqField p q = GaloisField p (q - 1)`
contains an element of order exactly `q`: `∃ u : Kˣ, orderOf u = q`.

**Proof.**

1. `Fintype.card K = p ^ (q - 1)` from `natCard_modqField` (transported by
   `Nat.card_eq_fintype_card`), hence `Fintype.card Kˣ = p ^ (q - 1) - 1` by
   `Fintype.card_units`.
2. `p` and `q` are coprime distinct primes, by `(Nat.coprime_primes hp hq).2 hpq`,
   so Fermat gives `p ^ (q - 1) ≡ 1 [MOD q]` via
   `Nat.ModEq.pow_card_sub_one_eq_one`.
3. Therefore `q ∣ p ^ (q - 1) - 1 = Fintype.card Kˣ`, using
   `Nat.modEq_iff_dvd'` with positivity of `p ^ (q - 1)` from `Nat.pow_pos`.
4. The unit group of a finite field is cyclic, so
   `IsCyclic.card_orderOf_eq_totient` applied to that divisibility counts the
   elements of order `q` exactly: `#{u : Kˣ | orderOf u = q} = q.totient`.
5. `Nat.totient_prime hq` rewrites this to `q - 1 > 0`, so the filtered finset is
   nonempty by `Finset.card_pos`; `Finset.mem_filter` extracts the order equation
   from any member.

**Remark.** Only `orderOf u = q` is produced here; the field-element version
(`ω ^ q = 1 ∧ ω ≠ 1`) is the separate `exists_nontrivial_qth_root_modqField`,
which coerces `u` down and uses primality of `q` to rule out `ω = 1`.
