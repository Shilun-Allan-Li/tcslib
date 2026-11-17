<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.mem_SigmaP_two_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-level existential characterization

**Claim.** A language belongs to the second existential level exactly when there are polynomial witness bounds and a coNP language such that membership is equivalent to the existence of a witness of the specified length whose encoded pair with the input belongs to that coNP language.

**Proof.** Write $2=1+1$ and apply the successor-level characterization (mem_SigmaP_succ_iff) at level $1$. It states that membership in the second existential level is equivalent to the asserted encoded-witness condition with a language in $\text{PiP}(1)$. The identity $\text{PiP}(1)=\text{coNP}$ (PiP_one) replaces that class by coNP, giving exactly the claimed characterization.

**Key facts.** `Complexity.mem_SigmaP_succ_iff`, `Complexity.PiP_one`.
