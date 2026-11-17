<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satReduction_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the SAT Reduction

**Claim.** For every Boolean word $x$, including words that do not encode a well-formed formula, $x$ belongs to $\mathrm{SAT}$ if and only if its image under the string-level reduction belongs to $\mathrm{SAT3}$.

**Proof.** Decode $x$ to a CNF formula $\varphi$. By the serialization round-trip theorem (`Std.Sat.CNF.decode_serialize`), decoding the reduction output recovers exactly the transformed formula $\mathrm{satTransform}(\varphi)$. The transformation preserves satisfiability (`Complexity.satTransform_equisat`) and produces a formula whose clauses all have width at most $3$ (`Complexity.satTransformFrom_width`, applied at the initial variable bound). Thus the output satisfies both defining conditions of $\mathrm{SAT3}$ exactly when $\varphi$ is satisfiable, which is the condition that $x$ belongs to $\mathrm{SAT}$.

**Key facts.** `Std.Sat.CNF.decode_serialize`, `Complexity.satTransform_equisat`, `Complexity.satTransformFrom_width`.
