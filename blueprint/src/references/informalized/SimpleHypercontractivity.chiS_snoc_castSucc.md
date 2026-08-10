<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: chiS_snoc_castSucc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A lifted character ignores the appended coordinate

**Claim.** For `S : Finset (Fin n)`, `x : BoolCube n` and `b : Bool`,
`chiS (S.image Fin.castSucc) (Fin.snoc x b) = chiS S x`. Since
`chiS S x = ∏ i ∈ S, boolToSign (x i)` and the lifted set `S.image castSucc`
never contains `Fin.last n`, the value of the appended bit `b` is irrelevant.

**Proof.** `unfold chiS` and then a single `simp_all only [...]` chaining:

1. `Fin.castSucc_inj` / `injOn_of_eq_iff_eq` supply the injectivity needed by
   `Finset.prod_image`, reindexing `∏ i ∈ S.image castSucc` as `∏ i ∈ S` over
   `castSucc i`.
2. `Fin.snoc_castSucc` evaluates each factor: `Fin.snoc x b (castSucc i) = x i`.

The resulting product is `∏ i ∈ S, boolToSign (x i) = chiS S x`. ∎

**Used in.** `noiseOp_snoc` (branch where the frequency set avoids the last
coordinate), and hence in the whole `(2,4)` / `(2,2k)` induction on `n`.
