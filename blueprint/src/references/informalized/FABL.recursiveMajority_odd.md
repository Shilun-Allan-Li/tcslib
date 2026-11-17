<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.recursiveMajority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oddness of Recursive Majority

**Claim.** If $n$ is odd, then recursive majority of arity $n$ is an odd Boolean function at every depth.

**Proof.** Use induction on the depth. At depth zero, recursive majority is the identity on the sole coordinate, so negating the input negates the output. At depth $d+1$, the successor equation expresses the output as ordinary majority of the depth-$d$ outputs on the input blocks (`recursiveMajority_succ`). Negating the full input negates each block coordinatewise. By the induction hypothesis, each block's recursive-majority output is therefore negated, so the vector of branch outputs for the negated input is the pointwise negative of the original branch-output vector. Since $n$ is odd, ordinary $n$-input majority is odd (`majority_odd`); applying this fact gives the negative of the original output, as required.

**Key facts.** `FABL.recursiveMajority_succ`, `FABL.majority_odd`.
