<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.partitionFunction_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Signed Variable Identification

**Claim.** If a class of Boolean functions is closed under independently negating input coordinates and under identifying input coordinates, then it is closed under the combined operation $w\mapsto f((z_iw_{\pi(i)})_{i=1}^n)$.

**Proof.** First negate the inputs of $f$ coordinatewise by $z$. The assumed negation closure puts the resulting function in $B_n$. Then identify its coordinates according to $\pi$; identification closure puts this function in $B_m$. Evaluating the two operations in succession gives exactly $w\mapsto f((z_iw_{\pi(i)})_{i=1}^n)$, so this partition function belongs to $B_m$.
