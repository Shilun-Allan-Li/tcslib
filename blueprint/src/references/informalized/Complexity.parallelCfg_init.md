<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelCfg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Initial Configurations

**Claim.** Encoding the initial configuration of $P$ on the image under $e$ of a binary word $x$ gives the initial configuration of its transverse binary realization on $x$.

**Proof.** Both configurations begin in the same state, have their input heads at position $1$, and have empty output. The encoded input position is the original position, since applying $e$ to each list entry does not change the list length. At every encoded work-tape track and position, the original initial tape contains no symbol; its transverse code is therefore the same all-blank tape. The work-head positions also agree, as the encoded track indexed by a pair retains the position of its original tape. Hence all configuration fields match.
