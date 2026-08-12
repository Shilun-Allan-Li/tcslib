<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Circuit.one_le_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every circuit has at least one node

**Claim.** For every `C : BoolCircuit.Circuit n`, `1 ≤ C.size`. Here `Circuit.size` counts
all nodes, being `1` on a literal leaf and `1 + Σ children sizes` on a gate.

**Proof.** By `cases C`, one `simp [Circuit.size]` per constructor:

* `lit l` — `size = 1`;
* `node isAnd cs` — `size = 1 + …`, so the bound holds regardless of the children.

Because both branches only need the leading `1`, no induction over the child list is
required.

**Remark.** Stated with `_root_.` so it lands in the `BoolCircuit` namespace even though it
is declared inside `ACP`; it exists purely to feed `Nat.le_mul_of_pos_left` in
`Circuit.toFeedForward_size_le`.
