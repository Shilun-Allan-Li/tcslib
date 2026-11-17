<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.doubled_getElem? -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of a Duplicated Bit String

**Claim.** In the string obtained by replacing each bit of $x$ by two consecutive copies, the entries at indices $2p$ and $2p+1$ both equal the entry of $x$ at index $p$, with absent lookups preserved.

**Proof.** Induct on the list $x$, allowing the index $p$ to vary. For the empty list, all the lookups are absent. If $x$ begins with a bit $a$, then at $p=0$ the two entries in the duplicated list are precisely the two copies of $a$. For $p+1$, the two indices in the duplicated list lie in the duplicated tail: the first is $2p+2$, and the second is $2p+3$. Applying the induction hypothesis to the tail at $p$ gives the desired equalities, including the absent-lookup cases.
