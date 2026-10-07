<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: fiber_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Each encoder fiber has at most (4w)^d restrictions

**Claim.** Let `f : DNF n` have width at most `w`, let `d ≤ s`, assume each term of
`f` mentions each variable at most once (`hnd`), and fix a target restriction
`γ : Restriction n`. Then the set of `ρ` that are `s`-restrictions, are bad for
`f.eval` at depth `d`, and satisfy `(razborovEncode f w d ρ).1 = γ` has cardinality
at most `(4 * w) ^ d`.

**Proof.** Three steps: forget a hypothesis, injectivity, then count aux strings.

1. Set `S` to the stated filter and `T` to the same filter with `IsRestriction s ρ`
   dropped. Then `S ⊆ T` (`Finset.mem_filter`, keeping `hρ.2.1` and `hρ.2.2`), so
   `Finset.card_le_card hST` reduces the goal to bounding `T.card`.
2. `ρ ↦ (razborovEncode f w d ρ).2` is injective on `T` (`Set.InjOn`): two members
   of `T` share the same first component `γ` by `hγ₁`, `hγ₂`, so `Prod.ext` makes
   the full encodings equal, and `razborovEncode_injective` (using `hbad₁`,
   `hbad₂`, `hw`, `hnd`) forces `ρ₁ = ρ₂`.
3. `Finset.card_image_of_injOn hinj` rewrites `T.card` as the cardinality of the
   image of aux strings, which `aux_image_card_bound f w d hw γ` bounds by
   `(4 * w) ^ d`. ∎

The exponent counts the `d` path steps, each carrying a position in `Fin w`, a
direction, and an "is-last-free-literal" flag: `w · 2 · 2 = 4w` choices per step.
The hypothesis `_hd : d ≤ s` is stated but unused in this proof.

**Used in.** `bad_count_bound` (line 1639), which sums this fiber bound over the
possible `γ` to bound the total number of bad `s`-restrictions.
