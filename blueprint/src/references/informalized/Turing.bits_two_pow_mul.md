<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.bits_two_pow_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary digits of a shifted integer

**Claim.** For $m>0$, the binary digit list of $2^j m$ consists of $j$ false digits followed by the binary digit list of $m$.

**Proof.** We induct on $j$. When $j=0$, the claim reduces to the fact that an empty list of false digits contributes nothing. For the successor case, write $2^{j+1}m=2(2^jm)$. Since $m>0$, the product $2^jm$ is positive. The binary expansion rule for doubling a positive natural number therefore puts a false digit at the front of its binary digit list. Applying the induction hypothesis to the remaining digits gives one false digit followed by the $j$ false digits and then $m$'s binary digits, as required.
