<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.closestInProperty_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of the closest function

**Claim.** The function selected as closest to $f$ among those satisfying $P$ itself satisfies $P$.

**Proof.** The existence theorem supplies a function satisfying $P$ that minimizes the normalized Hamming distance to $f$ among all functions satisfying $P$ (\texttt{exists\_closestInProperty}). The selected function is defined to be the witness supplied by that theorem. Its witness property therefore gives $P$ immediately.

**Key facts.** `FABL.exists_closestInProperty`.
