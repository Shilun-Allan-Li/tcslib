<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: card_image_castSucc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Lifting a subset along castSucc preserves its size

**Claim.** For `S : Finset (Fin n)`, `(S.image Fin.castSucc).card = S.card` —
lifting a subset of `Fin n` into `Fin (n+1)` along `Fin.castSucc` does not change
its cardinality.

**Proof.** One line: `Finset.card_image_of_injective S (Fin.castSucc_injective n)`
— `Fin.castSucc` is injective, so the image has the same cardinality. ∎

**Used in.** `noiseOp_snoc`, where a `Finset (Fin n)` is lifted into
`Finset (Fin (n+1))` and the noise weight `ρ ^ S.card` has to be recognized as
unchanged. Deliberately granular: it exists so that rewrite steps in the
noise-operator decomposition can name it directly, alongside its companion
`card_image_castSucc_union_last` for the branch that adjoins `Fin.last n`.
