<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.BPP_PTM_of_polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure of BPP Under Reductions

**Claim.** If $L'$ is polynomial-time many-one reducible to $L$ and $L$ belongs to BPP, then $L'$ belongs to BPP.

**Proof.** First convert the assumption that $L$ belongs to machine-defined BPP into the verifier-based condition (`inBPP_of_mem_BPP_PTM`). Closure of the verifier-based class under polynomial-time many-one reductions then transfers this condition from $L$ to $L'$ (`InBPP.of_polyTimeReducible`). Convert the resulting verifier-based membership back to machine-defined BPP (`mem_BPP_PTM_of_inBPP`).

**Key facts.** `Randomized.inBPP_of_mem_BPP_PTM`, `Randomized.InBPP.of_polyTimeReducible`, `Randomized.mem_BPP_PTM_of_inBPP`.
