<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.Data.check_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Check on an Encoded Pair

**Claim.** Checking the encoded pair of $x$ and $U$ is equivalent to the stated length bound on $t$ together with the core condition for $x,U,t,e$.

**Proof.** Expand the definition of the check. Its length bound uses the length of the first decoded component of the input, and its core condition uses both decoded components. For an input that is the encoding of $(x,U)$, decoding returns $x$ and $U$. Substituting these identities leaves exactly the stated length bound and the core condition.
