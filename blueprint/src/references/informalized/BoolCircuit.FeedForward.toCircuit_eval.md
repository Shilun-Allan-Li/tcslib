<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: toCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tree-unrolling preserves the computed function

**Claim.** Let `F : FeedForward Bool (Fin n) out` with AND/OR labelling `isAnd` and
fan-in `Fintype` data `gfin`, and assume `hcorrect : F.IsAndOrGate isAnd gfin` — i.e.
every gate's operation really is the AND (when `isAnd d v = true`) or OR (when `false`)
of its inputs, folded over `Finset.univ.val.toList`. Then for every output name
`o : out` and every input `x : Fin n → Bool`,

`(F.toCircuit isAnd gfin o).eval x = F.eval x o`.

**Proof.**
* `simp only [toCircuit, eval]` unfolds both sides to the corresponding statement about
  the last layer: `nodeToCircuit … F.depth …` on the left, `F.evalNode …` on the right,
  applied to the same transported output node.
* `exact nodeToCircuit_eval F isAnd gfin hcorrect _ _ _ x` closes it — the whole content
  is in that lemma, whose own proof is an induction on the layer index `m` using
  `Nat.recAux_zero` / `Nat.recAux_succ` to unfold `nodeToCircuit` and
  `FeedForward.evalNode`, then `cases isAnd _ v <;> simp [Circuit.eval, List.foldr_map, h_ih]`
  to match the AND/OR fold against `Circuit.eval`.

**Status.** No size hypothesis appears — correctness of the unrolling is independent of
the duplication blowup, accounted for separately by `toCircuit_size_le`. Neither
theorem currently has a consumer outside this file.
