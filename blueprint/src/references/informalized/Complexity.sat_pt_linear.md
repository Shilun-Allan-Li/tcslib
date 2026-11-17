<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Time Implies Polynomial Time

**Claim.** If a finite Turing machine computes $f$ on every input of length $n$ within $C(n+1)$ steps, then $f$ is polynomial-time computable.

**Proof.** The assumed linear-time machine and coefficient satisfy the hypothesis of the general result that every linear-time computable function is polynomial-time computable (`Complexity.polyTimeComputable_of_linear`). Applying that result gives the claim.

**Key facts.** `Complexity.polyTimeComputable_of_linear`.
