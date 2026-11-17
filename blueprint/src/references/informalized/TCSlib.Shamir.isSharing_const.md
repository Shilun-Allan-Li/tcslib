<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.isSharing_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant sharing

**Claim.** For any $d$ and $c\in F$, the function assigning $c$ to every party shares $c$ with degree less than $d+1$.

**Proof.** Take the constant polynomial with value $c$. Its degree is at most zero, which is less than $d+1$. Its value at zero is $c$, and its value at every party's label is $c$, as required.
