<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.composeThreeQueryProof_castAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Original Proof Coordinates

**Claim.** In the composed proof, each coordinate in the initial block of length $\ell$ agrees with the corresponding original proof coordinate.

**Proof.** The index obtained by casting $i$ into the larger coordinate range lies in the original-proof summand under the decomposition of the composed proof's indices. By the definition of the composed proof, that summand returns the original proof at the given coordinate, hence the value is $p(i)$.
