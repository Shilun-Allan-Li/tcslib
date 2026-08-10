<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: chiS_snoc_with_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A lifted character including the last coordinate picks up a sign

**Claim.** For `S : Finset (Fin n)`, `x : BoolCube n` and `b : Bool`,
`chiS (S.image Fin.castSucc ∪ {Fin.last n}) (Fin.snoc x b) = boolToSign b * chiS S x`.
Companion to `chiS_snoc_castSucc`: here the frequency set does contain
`Fin.last n`, so the character factors as the appended bit's sign times the
character of `S` on `x`.

**Proof.** `unfold chiS`, then one `simp +decide only [...]` doing three things:

1. `Finset.union_singleton` presents the set as `insert (Fin.last n) (S.image castSucc)`,
   and `Finset.mem_image` together with `Fin.castSucc_ne_last` shows
   `Fin.last n ∉ S.image castSucc`, so `Finset.prod_insert` splits off that
   factor.
2. `Fin.snoc_last` evaluates the split-off factor to `boolToSign b`.
3. The remaining product is reindexed exactly as in `chiS_snoc_castSucc`
   (`Fin.castSucc_inj`, `injOn_of_eq_iff_eq`, `Finset.prod_image`,
   `Fin.snoc_castSucc`), giving `chiS S x`. ∎

**Used in.** `noiseOp_snoc`; the `boolToSign b` factor is precisely the sign that
makes the `diffLast` summand appear in the last-coordinate decomposition of `T_ρ`.
