<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.narun_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation law for runs

**Claim.** Running the nondeterministic register machine on the concatenation of two choice strings is the same as first running on the first string and then on the second.

**Proof.** Induct on the first choice string, with the initial configuration arbitrary. If it is empty, concatenation leaves the second string unchanged, and the claimed identity is immediate. Otherwise write it as $b::\sigma$. Unfolding the run on this leading choice applies the one-step transition determined by $b$, followed by the run on $\sigma$. The induction hypothesis, applied to that resulting configuration, identifies the remaining run on $\sigma++\tau$ with first running on $\sigma$ and then on $\tau$. This is precisely the desired concatenation identity.
