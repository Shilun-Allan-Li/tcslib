<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_lenLe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time length comparison on pairs

**Claim.** The function that outputs $1$ exactly when the second decoded component has length at most the first decoded component’s length is polynomial-time computable.

**Proof.** First form, in polynomial time, the encoded pair whose first component is the decoded first component and whose second component is the decoded second component with a leading $1$ added. A polynomial-time pair-length-checking machine accepts a decoded pair $(a,b)$ exactly when $|b|\le 1\cdot(|a|+1)^1$; by the machine’s guarantee, it rejects invalid pair encodings. The pair encoding theorem and polynomial-time closure under composition therefore give a polynomial-time test on the original input. The pair decoder recovers the two chosen components exactly. Since the second component has had one bit prefixed, its length is $|\pi_2(z)|+1$, while the bound is $|\pi_1(z)|+1$. Thus the check is equivalent to $|\pi_2(z)|\le|\pi_1(z)|$.

**Key facts.** `Turing.FinTM.computesFunInTime_pairLenCheck`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_prepend`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.comp`, `Turing.pairDecode_pairEncode`.
