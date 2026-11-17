<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_numVars_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable Count of a Cons Formula

**Claim.** For a clause $C$ and a CNF formula $\varphi$, the variable count of $C::\varphi$ is the maximum of the variable maximum of $C$ and the variable count of $\varphi$.

**Proof.** The list of literals obtained by flattening $C::\varphi$ is the concatenation of the literals from $C$ and those from $\varphi$. Applying the defining fold that takes the maximum, its value on this concatenation is the maximum of its values on the two parts. These two values are precisely the clause variable maximum of $C$ and the variable count of $\varphi$.

**Key facts.** `Complexity.sat_foldMax_append`.
