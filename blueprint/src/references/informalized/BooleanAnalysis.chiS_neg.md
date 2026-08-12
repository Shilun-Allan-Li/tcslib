<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: chiS_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Characters under the antipodal map

**Claim.** Flipping every bit multiplies a Walsh character by the sign of its
degree: for `S : Finset (Fin n)` and `x : BoolCube n`,
`chiS S (fun i => !x i) = (-1 : ℝ) ^ S.card * chiS S x`.

**Proof.**

1. `simp only [chiS]` exposes both sides as products over `S`, and
   `simp_rw [boolToSign_not]` replaces each factor `boolToSign (!x i)` by
   `-boolToSign (x i)`. The goal becomes the purely algebraic
   `∏ i ∈ S, (-c i) = (-1) ^ |S| * ∏ i ∈ S, c i`.
2. `induction S using Finset.induction`:
   - **empty**: `simp` — both sides are `1`, since `(-1) ^ 0 = 1` and the empty
     product is `1`.
   - **insert `a` into `s`** (with `ha : a ∉ s`): `Finset.prod_insert ha` peels
     the new factor off both products, `Finset.card_insert_of_notMem ha` rewrites
     `|insert a s|` to `|s| + 1`, and `ih` handles the rest of the product.
     `ring` then closes the goal by matching one extra `-1` against the
     incremented exponent.

**Remark.** Only `|S|` mod 2 survives, so the character is even or odd as a
function on the hypercube according to the parity of its degree — the fact that
makes the antipodal involution a usable change of variables.

**Used in.** `fourierCoeff_odd_even`, its only consumer: combined with oddness of
`f` and evenness of `|S|`, it forces the Fourier sum to equal its own negation.
