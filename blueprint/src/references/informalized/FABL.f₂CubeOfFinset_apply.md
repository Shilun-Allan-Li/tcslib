<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.f₂CubeOfFinset_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinates of a Set Indicator

**Claim.** For every finite set $S\subseteq\mathrm{Fin}(n)$ and every $i\in\mathrm{Fin}(n)$, the $i$th coordinate of its binary indicator vector is $1$ when $i\in S$ and $0$ otherwise.

**Proof.** By definition, the indicator vector assigns to each coordinate $i$ the value $1$ if $i$ belongs to $S$, and $0$ otherwise. The claimed equality is therefore the defining coordinate formula.
