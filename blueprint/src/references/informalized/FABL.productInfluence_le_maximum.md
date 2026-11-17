<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productInfluence_le_maximum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bounded by the Maximum

**Claim.** For a finite state space with a probability distribution and a real-valued function on its product space, the influence at any coordinate is at most the maximum coordinate influence.

**Proof.** The set of coordinates is nonempty because it contains the specified coordinate $i$. The maximum influence is therefore the supremum of the coordinate influences over this finite set. Each member of a set is at most its supremum, so the influence at $i$ is at most the maximum.
