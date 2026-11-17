<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.inc_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment run on a binary counter

**Claim.** From the configuration with register $r$ holding the bits of $n$ at head position zero, the program reaches the configuration with the bits of $n+1$ at head position zero; every earlier configuration has state $c_C$ or $c_B$ and head position in the stated range.

**Proof.** Apply the carry-in run lemma (`incC_run`) to the word of $n$ with empty prefix. It yields a time $T_1$ and a head position $p$ at which the program is in state $c_B$ with the bits of $n+1$ on the tape, since incrementing the bit word represents adding one (`bits_succ`). The carry-in bound gives $p+1\le |\mathrm{bits}(n+1)|$, so the carry-phase lemma (`incB_run`) applies with countdown $(p+1)$ and ends at head position zero in state $\mathrm{next}$. Concatenate the two runs using the iteration addition law (`rrun_add`); this gives the required endpoint. For an earlier time, if it is before $T_1$, the carry-in lemma supplies a configuration in state $c_C$ and its head bound is below the final bit-word length. The length of the original bit word is no greater than the incremented word's length: under increment, the first zero changes to one without growth, or a string of ones propagates the carry and the word may grow by one. If the time is at or after $T_1$, the carry-phase lemma supplies state $c_B$ and its head bound. Thus every earlier configuration has one of the two asserted states and satisfies the common position bounds.

**Key facts.** `Complexity.LogProg.incC_run`, `Complexity.LogProg.bits_succ`, `Complexity.LogProg.incB_run`, `Complexity.LogProg.rrun_add`.
