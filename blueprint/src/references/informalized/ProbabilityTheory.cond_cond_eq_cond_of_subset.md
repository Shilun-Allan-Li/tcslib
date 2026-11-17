<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.cond_cond_eq_cond_of_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated conditioning on a subset

**Claim.** For a finite measure and measurable sets $F\subseteq A$, conditioning first on $A$ and then on $F$ gives the same measure as conditioning directly on $F$.

**Proof.** The iterated-conditioning identity states that conditioning first on $A$ and then on a measurable set $F$ agrees with conditioning directly on $A\cap F$ (\texttt{cond\_cond\_eq\_cond\_inter}). Since $F\subseteq A$, we have $A\cap F=F$. Substitution gives $(\mu[\cdot\mid A])[\cdot\mid F]=\mu[\cdot\mid F]$.

**Caveat.** The proof relies on the intersection form of the iterated-conditioning identity, which is not included in the supplied upstream entries.
