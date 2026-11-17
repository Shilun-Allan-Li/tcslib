<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean :: Complexity.NL_eq_coNL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure of Logarithmic Space Under Complement

**Claim.** The class of languages decidable in nondeterministic logarithmic space is equal to the class of languages whose complements belong to that class.

**Proof.** To prove equality, take an arbitrary language $L$ and compare membership in the two classes. If $L\in\mathrm{NL}$, the complement-closure theorem for nondeterministic logarithmic space gives $L^c\in\mathrm{NL}$, so $L\in\mathrm{coNL}$. Conversely, if $L\in\mathrm{coNL}$, then $L^c\in\mathrm{NL}$. Applying the same complement-closure theorem gives $(L^c)^c\in\mathrm{NL}$; since $(L^c)^c=L$, this says $L\in\mathrm{NL}$. Thus the classes have the same members.

**Key facts.** `Complexity.compl_mem_NL`.
