<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_uniformProd_snd_uniformDisjointCoordinateVector_cond_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional independence of the coordinate vector

**Claim.** Conditioning the product of the uniform special-coordinate law and the uniform disjoint-coordinate-vector law on the first coordinate being $i$ leaves the second coordinate uniformly distributed.

**Proof.** Fix a vector $c$. Under the product law, the conditioning event that the first coordinate equals $i$ has mass $1/n$: it is the rectangle consisting of the singleton $\{i\}$ and the whole vector space, whose factor masses are $1/n$ and $1$ (`uniformFin_singleton`, `uniformDisjointCoordinateVector_univ`). The joint event that the first coordinate equals $i$ and the second equals $c$ is the rectangle $\{i\}\times\{c\}$, with mass $(1/n)(1/3^n)$ by the singleton formulas (`uniformFin_singleton`, `uniformDisjointCoordinateVector_singleton`). Dividing the joint mass by the conditioning-event mass gives $1/3^n$, which is precisely the mass of $c$ under the uniform vector law (`uniformDisjointCoordinateVector_singleton`). Thus every singleton has the same conditional mass as under that law, proving equality of distributions.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_univ`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_singleton`.
