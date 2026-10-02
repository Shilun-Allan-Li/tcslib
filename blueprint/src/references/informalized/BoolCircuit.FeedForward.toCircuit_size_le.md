<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: toCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Size of the tree-unrolled circuit

**Claim.** Let `F : FeedForward Bool (Fin n) out` with AND/OR labelling `isAnd` and
fan-in `Fintype` data `gfin`, and suppose every gate has fan-in at most `k`:
`hk : ∀ d v, Fintype.card (F.gates d v).op.ι ≤ k`. Then for every output name `o : out`,

`(F.toCircuit isAnd gfin o).size ≤ (k + 1) ^ F.depth`.

**Proof.** One term-mode line:
`nodeToCircuit_size_le F isAnd gfin hk F.depth _ _`, i.e. the layerwise bound
`(nodeToCircuit … m hm v).size ≤ (k + 1) ^ m` instantiated at `m := F.depth` with the
transported output node.

The layerwise lemma is proved by `induction' m with m ih`:
* base case — `unfold nodeToCircuit; simp +decide [Circuit.size]`: a layer-`0` node is a
  literal, of size `1 = (k + 1) ^ 0`;
* successor case — `h_node` rewrites the size of `.node` as
  `1 + (children's sizes).foldr (· + ·) 0` (`Nat.recAux`, `List.foldr_map`,
  `Circuit.size.eq_def`); `h_foldr`, an induction on the list, bounds a `foldr`-sum by
  `L.length * (k + 1) ^ m` when every entry is; combining these with `pow_succ'` and
  `nlinarith [hk _ v, pow_pos (Nat.succ_pos k) m]` gives
  `1 + k * (k + 1) ^ m ≤ (k + 1) ^ (m + 1)`.

**Remark.** The bound is exponential in the depth because tree-unrolling duplicates any
node whose value is read by more than one downstream gate.
