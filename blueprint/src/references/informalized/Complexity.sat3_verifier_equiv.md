<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat3_verifier_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# 3SAT Verifier Certificates

**Claim.** A decoded formula has width at most three and is satisfiable exactly when there is a Boolean word of length $|x|+1$ whose concatenation with $x$ is accepted by the verifier in 3SAT mode.

**Proof.** First, satisfiability of the decoded formula is equivalent to the existence of a Boolean word $u$ of length $|x|+1$ whose associated assignment satisfies the formula (`Complexity.sat_certificate`). The verifier's behavior on a concatenation $x++u$ of this prescribed length is characterized by `Complexity.satVerdict_append`: it accepts precisely when the width check passes and the decoded formula evaluates to true under the assignment from $u$. The Boolean width check is true exactly for formulas of width at most three (`Complexity.satWidth_spec`). Hence, if the formula has width at most three and is satisfiable, a certificate supplied by the satisfiability characterization makes the verifier accept. Conversely, acceptance forces both the width check and the evaluation to be true, yielding width at most three and a satisfying certificate, so the formula is satisfiable.

**Key facts.** `Complexity.sat_certificate`, `Complexity.satVerdict_append`, `Complexity.satWidth_spec`.
