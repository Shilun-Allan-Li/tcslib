<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/FourthMoment.lean :: card_image_castSucc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Lifting a subset along castSucc preserves its size

**Claim.** For `S : Finset (Fin n)`, `(S.image Fin.castSucc).card = S.card` —
lifting a subset of `Fin n` into `Fin (n+1)` along `Fin.castSucc` does not change
its cardinality.

**Proof.** One line: `Finset.card_image_of_injective S (Fin.castSucc_injective n)`
— `Fin.castSucc` is injective, so the image has the same cardinality. ∎

**Used in.** `BooleanAnalysis.Hypercontractivity.noiseOp_snoc` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/FourthMoment.lean`.
