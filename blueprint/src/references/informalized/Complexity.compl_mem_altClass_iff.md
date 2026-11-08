<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.compl_mem_altClass_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Duality for Alternating Classes

**Claim.** For every Boolean quantifier type $b$, every $i\in\mathbb N$, and every binary language $L$, $L^c\in\mathrm{AltClass}(b,i)$ if and only if $L\in\mathrm{AltClass}(\neg b,i)$.

**Proof.** Suppose first that $L^c$ is in $\mathrm{AltClass}(b,i)$, witnessed by bounds $C,c$ and a verifier language $V\in P$. Complement closure of polynomial time (`Complexity.compl_mem_P`) gives $V^c\in P$. The witness equivalence for $L^c$ says that $x\in L$ exactly when the alternating condition for $V$ fails. The negation law for alternating quantifiers (`Complexity.not_altQuant`) identifies this failure with the alternating condition using verifier $V^c$ and the opposite quantifier type $\neg b$. Thus the same bounds, with verifier $V^c$, witness $L\in\mathrm{AltClass}(\neg b,i)$. Conversely, take witnesses $C,c,V$ for $L\in\mathrm{AltClass}(\neg b,i)$. Again $V^c\in P$. Applying the negation law to the alternating condition for $V$ converts it to the condition for $V^c$ with type $b$. The witness equivalence for $L$ then says exactly that $x\in L^c$ holds when this latter condition holds, giving $L^c\in\mathrm{AltClass}(b,i)$.

**Key facts.** `Complexity.compl_mem_P`, `Complexity.not_altQuant`.
