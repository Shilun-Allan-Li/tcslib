<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satAppend_seek -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeking the First Blank

**Claim.** If $w=pr$, then from the seek state with the work head at $|p|$, the machine scans the remaining suffix and reaches the copy state with its head at $|w|$ after $|r|+1$ steps, keeping the input head and tape unchanged.

**Proof.** Induct on $r$. If $r$ is empty, $w=p$, so the head is already at the end of the work word. The seek transition reads blank, changes to the copy state, and leaves the work head at $|w|$; the one-step run follows from the run-length identities. If $r=b::r'$, the equality $w=pbr'$ shows that the work-tape cell at position $|p|$ contains $b$. The seek transition advances the work head by one and preserves the tape and input head, placing the head at the end of $pb$. Decompose the run into this first step and the remaining run (`runFrom_succ_eq_step`); the induction hypothesis applies to prefix $pb$ and suffix $r'$, since $w=(pb)r'$. The zero-step run identity supplies the base-case run calculation (`runFrom_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
