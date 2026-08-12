<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: majority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The majority function on an odd number of bits

**Definition.** For `k : ℕ`, `majority k : BooleanFunc (2 * k + 1)` is

```
majority k x = if (Finset.univ.filter (fun i => x i = false)).card > k then 1 else -1
```

i.e. `+1` when strictly more than `k` of the `2k + 1` coordinates are `false`,
and `-1` otherwise. Since the arity is odd there is never a tie, so the two
branches genuinely partition the cube. A plain `noncomputable def` with no
proof content.

**Remark.** The `false`-counting is not a slip: it matches the file's
`boolToSign` convention `false ↦ 1`, `true ↦ -1`, under which `false` is the
`+1` input. So `majority k` really is "the sign of the sum of the `±1`
coordinates", the standard `Maj_{2k+1}`.

**Used in.** Nothing — no other declaration in the repository references it.
It sits with `dictator` and `parity` as one of the canonical example functions,
but unlike those two it has no accompanying characterisation lemma
(`dictator_eq_chi`, `parity_eq_chi_univ`), so nothing downstream can yet say
anything about its Fourier expansion.
