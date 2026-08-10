<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: dim_map_r_E -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Rank-nullity for the restriction of `S` to a coordinate set

**Claim.** For `S ≤ V n p` and `E : Finset (Fin n)`,
`finrank (S.map (r_E E)) = finrank S - finrank (S ⊓ V_sub (E_c E))`, where
`r_E E : V n p →ₗ V_sub E` zeroes out all coordinates outside `E`. The image of
`S` under restriction loses exactly the dimensions of the part of `S` supported
off `E`.

**Proof.** Rank-nullity for `r_E E` restricted to `S`, then identification of the
kernel.

1. Generalise to an arbitrary `f : V n p →ₗ V_sub E` and an arbitrary submodule
   `U`, and apply `LinearMap.finrank_range_add_finrank_ker` to the composite
   `f ∘ₗ U.subtype`, giving
   `finrank (map f U) = finrank U - finrank (ker (f ∘ₗ U.subtype))`
   (`eq_tsub_of_add_eq`, after `range (f ∘ₗ U.subtype) = map f U`).
2. Identify `ker (f ∘ₗ U.subtype)` with `U ⊓ ker f`: `Submodule.finrank_map_subtype_eq`
   moves the finrank across the inclusion, and the membership `Iff` is routine
   (`simp_all [Submodule.mem_inf, LinearMap.mem_ker, …]`).
3. Instantiate at `f := r_E E`, `U := S`.
4. Finally `ker (r_E E) = V_sub (E_c E)` — this is `ker_r_E E`, stated there as
   `V_sub (Finset.univ \ E)` and matched up by `convert`.

**Remark.** ℕ subtraction is sound here because the kernel part sits inside `S`.

**Used in.** `g_expansion`, which is the dimension count driving
`cleaning_dimension_identity` and hence the Singleton bound.
