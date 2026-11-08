<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productProbabilityPMF_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity of an independent product

**Claim.** The independent product of uniform distributions on a finite nonempty set $D$, indexed by a finite set $V$, is uniform on the function space $V\to D$.

**Proof.** Compare the two probability mass functions at an arbitrary assignment $a:V\to D$. Each coordinate contributes mass $1/|D|$, so the independent-product mass is $(1/|D|)^{|V|}$. The function space has $|D|^{|V|}$ elements, and its uniform distribution assigns mass $1/|D|^{|V|}$ to each assignment. These masses agree, hence the probability mass functions are equal.
