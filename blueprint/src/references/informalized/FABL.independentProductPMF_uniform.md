<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.independentProductPMF_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independent product of uniform distributions

**Claim.** For a finite nonempty set $D$, the independent product of uniform distributions on $D$ is uniform on the set of functions from $V$ to $D$.

**Proof.** Compare point probabilities at an assignment $a:V\to D$. Each coordinate uniform distribution assigns probability $1/|D|$ to its chosen value, so the independent product assigns $a$ probability $(1/|D|)^{|V|}$. The set of assignments has cardinality $|D|^{|V|}$, by the finite product cardinality formula. Thus the uniform distribution on assignments assigns probability $1/|D|^{|V|}$ to $a$ as well. The point probabilities agree for every assignment, proving equality of the distributions.
