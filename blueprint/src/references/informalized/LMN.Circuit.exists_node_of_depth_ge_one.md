<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: Circuit.exists_node_of_depth_ge_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A circuit of positive depth is a gate node

**Claim.** For `c : Circuit m` with `1 ≤ c.depth` there exist `isAnd : Bool` and
`cs : List (Circuit m)` with `c = Circuit.node isAnd cs`. No constraint is
placed on `cs` — in particular it may be empty.

**Proof.** Case split on the constructor of `c` (`cases c`).

1. `c = Circuit.lit l`: `Circuit.depth` unfolds to `0`, so the hypothesis reads
   `1 ≤ 0` and is discharged by `simp [Circuit.depth] at h`.
2. `c = Circuit.node isAnd cs`: the witnesses are the constructor's own
   arguments, `exact ⟨isAnd, cs, rfl⟩`.

**Remark.** This is the elimination form of "depth 0 iff literal": it converts a
numeric depth hypothesis into a structural pattern match, which is what the
depth-reduction proofs need since `Circuit` is a nested inductive and `cases`
on a bare depth inequality is not available.

**Used in.** `absorbOneLevel_depth1`, `child_depth_le1_has_signed_dnf`,
`exists_circuit_depth_reduction_depth2`, and `exists_circuit_depth_reduction`
(all in the same file) to expose the top gate of `c_top` before absorbing it.
