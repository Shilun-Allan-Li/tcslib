<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: ker_r_E -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The kernel of the restriction map is the subspace supported off E

**Claim.** For `E : Finset (Fin n)`, the kernel of the restriction map
`r_E E : V n p →ₗ[F p] V_sub E` is exactly `V_sub (Finset.univ \ E)`. Recall
`r_E E v` zeroes every coordinate outside `E`, and `V_sub C` is the subspace of
vectors vanishing outside `C`; so a vector dies under `r_E E` precisely when it
vanishes *on* `E`.

**Proof.** `ext x` and prove both inclusions.

- (⊆) From `hx : x ∈ ker (r_E E)` get `(r_E E) x = 0` (`LinearMap.mem_ker`),
  then `congrArg Subtype.val` pushes this to an equation in `V n p` and
  `congrArg Prod.fst` / `Prod.snd` to the two component functions:
  `(fun i => if i ∈ E then x.1 i else 0) = 0`, likewise for `x.2`. For
  `i ∉ Finset.univ \ E` we have `i ∈ E` (`Finset.mem_sdiff`), so evaluating the
  function equality at `i` via `congrArg (fun f => f i)` and simplifying the
  `if` with `hiE` gives `x.1 i = 0` and `x.2 i = 0`.
- (⊇) From `hx : x ∈ V_sub (univ \ E)`, show `(r_E E) x = 0` by `ext i` and
  `by_cases hi : i ∈ E`. When `i ∈ E`, `i ∉ univ \ E`, so `hx i hnot` supplies
  the vanishing of the coordinate; when `i ∉ E` the `if` branch is already `0`
  (`simp [r_E, hi]`). Conclude with `LinearMap.mem_ker`.

**Used in.** `dim_map_r_E`, where rank–nullity for `r_E E` is stated in terms of
`S ⊓ ker (r_E E)` and this lemma rewrites that intersection as
`S ⊓ V_sub (E_c E)` — the "cleaning" form used throughout the `g` computations.
