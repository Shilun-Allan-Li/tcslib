<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.guideFill_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preserving the origin under filling

**Claim.** If a guide tape has the origin mark exactly at coordinate $0$, then filling any number of cells in either direction preserves the property that the origin mark occurs exactly at $0$.

**Proof.** Unfold the definition of the filled tape and its guide mark. On a newly filled coordinate, the assigned mark is the origin precisely when that coordinate is $0$. On coordinates not newly filled, the value comes from the original guide tape, where by hypothesis it is the origin precisely at $0$. Therefore the filled tape has the origin mark at $z$ exactly when $z=0$.
