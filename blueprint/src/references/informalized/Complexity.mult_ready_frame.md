<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_ready_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication frame preservation

**Claim.** If two register assignments agree at every register other than register 0, and the first assignment satisfies the multiplication-ready conditions, then the second does too.

**Proof.** The multiplication-ready conditions specify values only for registers 1, 2, 3, 4, 5, 6, 7, 11, and 12. Each is distinct from register 0, so the frame hypothesis says the second assignment agrees with the first at every register used by those conditions. Transferring each specified equality across that agreement establishes all the required conditions.
