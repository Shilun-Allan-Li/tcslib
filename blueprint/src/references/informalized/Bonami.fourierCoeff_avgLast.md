<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: fourierCoeff_avgLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fourier coefficients of the last-coordinate average

**Claim.** For `f : BooleanFunc (n+1)` and `S : Finset (Fin n)`,
`fourierCoeff (avgLast f) S = fourierCoeff f (S.image Fin.castSucc)`. So
averaging out the last variable simply reads off the Fourier coefficients of `f`
at frequencies that do not contain `Fin.last n`.

**Proof.**

1. Unfold `avgLast`, `fourierCoeff`, `innerProduct`, `expect`, `chiS`,
   `restrictLast`, normalising with `ring_nf` between steps.
2. `Finset.prod_image` (legitimate since `Fin.castSucc` is injective,
   `Fin.castSucc_inj`) shows `χ_{S.image castSucc} (Fin.snoc x b) = χ_S x`:
   the lifted set omits the last coordinate, so the character is blind to `b`.
3. `uniformWeight_succ` (after `add_comm 1 n`) replaces `uniformWeight (n+1)` by
   `uniformWeight n / 2`, and `sum_boolCube_succ` splits the sum over
   `BoolCube (n+1)` into the `snoc · false` and `snoc · true` halves.
4. The two halves are exactly the two summands of `avgLast`, so pulling the
   factor `1/2` inside (`← mul_add`, `Finset.mul_sum`) and finishing with
   `ring_nf` / `simp` gives the identity. ∎

**Used in.** `Hypercontractivity/Simple.lean` (rewritten right-to-left to express
a Fourier level of `f` through `avgLast f`). The companion statement for the
half-difference is `fourierCoeff_diffLast`; note `degree_avgLast` re-proves this
identity inline instead of calling this lemma.
