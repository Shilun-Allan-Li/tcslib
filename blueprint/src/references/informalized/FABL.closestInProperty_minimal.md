<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.closestInProperty_minimal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimal distance among functions satisfying a property

**Claim.** For every function $g$ satisfying $P$, the selected closest function has normalized Hamming distance from $f$ at most that of $g$.

**Proof.** The existence theorem provides a function satisfying $P$ whose normalized Hamming distance from $f$ is no greater than that of any other function satisfying $P$ (\texttt{exists\_closestInProperty}). The selected function is the witness from that theorem. Applying its minimizing property to the given $g$ and its hypothesis $P(g)$ yields the claimed inequality.

**Key facts.** `FABL.exists_closestInProperty`.
