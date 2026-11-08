<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.decisionTreeProcessPMF_map_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input marginal of the tree process

**Claim.** When a process sample is formed by drawing an input from the product distribution and recording the tree's query trace, its input marginal is the product distribution.

**Proof.** The process distribution is the image of the product input distribution under the map sending an input $x$ to its process sample, whose input component is $x$. Mapping this distribution onward by the input projection is therefore the same as mapping by the composite of these two functions. That composite is the identity on inputs, since the input component of the sample constructed from $x$ is exactly $x$. The image of the product distribution under the identity is the product distribution itself.
