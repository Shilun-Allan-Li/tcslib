<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.card_parityBlockAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Block Assignments

**Claim.** For every natural number $r$, the number of assignments of a sign in $\{-1,1\}$ to each of $r$ positions is $2^r$.

**Proof.** There are two signs available at each position, and assignments are functions from the $r$ positions to this two-element set. The number of such functions is the size of the codomain raised to the size of the domain, namely $2^r$.
