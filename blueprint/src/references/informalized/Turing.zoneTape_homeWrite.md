<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneTape_homeWrite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape values away from home cells

**Claim.** Changing the home value of zone contents leaves the tape value unchanged at every integer position other than $0$ and $1$.

**Proof.** By definition, the tape value first handles positions $0$ and $1$ using the home value. The hypotheses exclude both positions, so these two cases are bypassed. In every remaining case the tape value is determined by the left or right zone contents, which the home update leaves unchanged. Thus the two tape values agree.
