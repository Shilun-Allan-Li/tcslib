<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean :: Complexity.NSPACE_compl_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure of NSPACE Under Complement

**Claim.** For every space-constructible function $S$, the class of languages whose complements belong to $\mathrm{NSPACE}(S)$ is exactly $\mathrm{NSPACE}(S)$.

**Proof.** For any language $L$, if $L\in\mathrm{NSPACE}(S)$, closure under complement (`compl_mem_NSPACE`) gives $L^c\in\mathrm{NSPACE}(S)$. Conversely, if $L^c\in\mathrm{NSPACE}(S)$, apply the same closure result to $L^c$ to obtain $(L^c)^c\in\mathrm{NSPACE}(S)$. Since complementing twice returns $L$, this proves the reverse implication and hence equality of the two classes.

**Key facts.** `Complexity.compl_mem_NSPACE`.
