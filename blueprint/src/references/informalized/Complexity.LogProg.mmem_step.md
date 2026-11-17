<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.mmem_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Memory Correspondence

**Claim.** A memory instruction at state $l$ has a one-step transition that is mirrored by the compiled machine on the corresponding seam configuration, preserving the register values, answer, and output while updating the memory tape and head consistently.

**Proof.** Split on the memory instruction assigned at $l$; the hypothesis that it is a memory instruction leaves four cases. For a read, both systems leave memory and its head unchanged and move to the successor chosen by the bit under the head. For a set, both move to the given successor, set the current memory cell to true, and leave the head fixed. For a left or right move, both keep the tape unchanged, move the head by one cell in the indicated direction, and enter the given successor. In each case the compiled transition leaves the ordinary work tapes unchanged and emits no output. Thus the compiled action applied to the seam configuration is exactly the seam configuration formed from the program's successor state, updated memory, and updated head. Choosing those successor data gives both required equalities.
