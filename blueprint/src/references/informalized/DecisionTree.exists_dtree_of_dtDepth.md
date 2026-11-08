<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: DecisionTree.exists_dtree_of_dtDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Tree Attaining Least Depth

**Claim.** For every Boolean function on $n$ coordinates, there is a decision tree computing it whose depth is at most the least depth of any decision tree computing it.

**Proof.** The least depth is defined as the least natural number $d$ for which there exists a decision tree of depth at most $d$ computing the given function. The full tree construction establishes that such a $d$ exists. The defining property of the least such number supplies a tree of depth at most that number, together with equality of its evaluation and the function at every assignment.
