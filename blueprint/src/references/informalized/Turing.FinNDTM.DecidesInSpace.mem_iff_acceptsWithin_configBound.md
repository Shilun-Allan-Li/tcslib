<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership at the Configuration Bound

**Claim.** For every input $x$, membership in $L$ is equivalent to acceptance within the stated configuration bound.

**Proof.** Fix $x$, and take the time $T$ and associated halting, space, and correctness properties supplied by the space-decision hypothesis. If $x\in L$, correctness at time $T$ gives acceptance within $T$. The space bound then yields acceptance within the configuration bound by \texttt{acceptsWithin_of_spaceUsedWith_le}. Conversely, acceptance within that bound implies $x\in L$ by the general acceptance-soundness result \texttt{DecidesInSpace.mem_of_acceptsWithin}. These two implications establish the equivalence.

**Key facts.** `Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le`, `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`.
