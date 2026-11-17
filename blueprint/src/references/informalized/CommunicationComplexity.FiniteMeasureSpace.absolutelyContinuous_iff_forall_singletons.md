<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Continuity on a Finite Space

**Claim.** On a finite measurable space, $\mu\ll\nu$ if and only if every singleton of $\nu$-measure zero also has zero $\mu$-measure.

**Proof.** If $\mu\ll\nu$, then every set of $\nu$-measure zero has zero $\mu$-measure, so the condition follows by taking singleton sets. Conversely, assume every $\nu$-null singleton is $\mu$-null. Let $S$ be any measurable set with $\nu(S)=0$, and let $T$ be the finite set of points of $S$. The space is discrete, so $T=S$. Decompose $\mu(T)$ as the finite sum of the measures of its singletons (\texttt{MeasureTheory.sum\_measure\_singleton}). For each $\omega\in T$, monotonicity of measure shows $\nu(\{\omega\})\le\nu(S)=0$, hence that singleton is $\nu$-null and therefore also $\mu$-null by assumption. Every summand is zero, so $\mu(S)=0$. This is precisely $\mu\ll\nu$.
