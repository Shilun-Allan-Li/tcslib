<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.card_submodule_eq_two_pow_finrank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of a binary subspace

**Claim.** A linear subspace $A$ of the $n$-dimensional vector space over the field with two elements has $2^{\dim A}$ elements.

**Proof.** The subspace $A$ is itself a finite-dimensional vector space over the field with two elements. A finite-dimensional vector space of dimension $d$ over a field with two elements has exactly $2^d$ elements: choosing a basis identifies each vector uniquely with a $d$-tuple of field elements, and each of the $d$ coordinates has two choices. Taking $d=\dim A$ gives the claimed cardinality.
