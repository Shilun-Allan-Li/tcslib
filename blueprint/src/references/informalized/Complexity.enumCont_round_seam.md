<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_round_seam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Candidate Seam

**Claim.** The buffered composition started from the assembly configuration with phase $b$ and word $s$ on its work tape is the configuration in the corresponding first-phase state with $s$ represented on tape zero and all other tapes blank.

**Proof.** Again, equality of configurations follows by comparing their fields. Their states, input-head positions, and outputs agree directly. For the tape contents, split the work-tape indices into the assembly machine's block, the single buffer tape, and the verifier's block, as in the definition of the blocked tape layout. The first block has one tape, whose index is zero, and its contents represent $s$. The buffer and verifier blocks are blank: the initial assembly configuration has empty output, so its buffer tape is blank, and the verifier block is blank by construction. These are exactly the tape functions represented by the state word, which puts $s$ at index zero and the empty word elsewhere. The head positions also agree: the first tape's head is at zero, and the buffer and verifier heads are at zero.
