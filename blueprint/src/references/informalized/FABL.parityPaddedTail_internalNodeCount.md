<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityPaddedTail_internalNodeCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Internal Node Count of the Padded Tail

**Claim.** For natural numbers $n,r,q$, the internal node count of the padded parity tail is the sum of the parity layer sizes from level $0$ through level $q$, namely $\sum_{k=0}^{q} r^k2^r$.

**Proof.** The padded tail consists of a bottom layer with the same number of gates as the standard tail at level $q$, followed by that standard tail at level $q$. Its internal node count is therefore the size of the level-$q$ layer plus the standard tail's count. By the standard-tail counting identity (FABL.parityStandardTail_internalNodeCount), the latter is the sum over levels below $q$. Adding the level-$q$ term yields the sum over levels $0$ through $q$.

**Key facts.** `FABL.parityStandardTail_internalNodeCount`.
