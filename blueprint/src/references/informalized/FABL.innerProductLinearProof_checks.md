<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductLinearProof_checks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Checks passed by the inner product proof

**Claim.** If the inner product of $w$ modulo two is $1$, the proof recording each coordinatewise product and each cumulative sum passes every seed check: it has initial cumulative sum $0$, final sum $1$, correct products, and the required recurrence between consecutive sums.

**Proof.** Separate the seed into endpoint checks and coordinate checks. At the initial endpoint, the proof's prefix sum over no coordinates is $0$, so the check passes. At the final endpoint, the full prefix sum equals the inner product (`innerProductPrefixBit_full`), which is $1$ by hypothesis; hence that check passes as well. For a product check at coordinate $i$, the recorded product is defined as the product of the two corresponding input bits, so the required Boolean equality holds. For a recurrence check, the prefix sum through coordinate $i$ is the preceding prefix sum plus that coordinate's product (`innerProductPrefixBit_succ`), exactly the equation being tested.

**Key facts.** `FABL.innerProductPrefixBit_full`, `FABL.innerProductPrefixBit_succ`.
