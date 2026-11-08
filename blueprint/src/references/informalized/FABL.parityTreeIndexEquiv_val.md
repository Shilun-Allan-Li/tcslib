<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityTreeIndexEquiv_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity tree index formula

**Claim.** Under the canonical bijection between pairs $(j,k)$ with $j<r$ and $k<r^t$ and indices below $r^{t+1}$, the image index is $jr^t+k$.

**Proof.** The canonical product-of-finite-intervals bijection lists the second coordinate within each successive block of length $r^t$: the pair $(j,k)$ is sent to the index obtained by taking $j$ full blocks and then offset $k$. Thus its value is $j r^t+k$. The identification of the target size with $r^{t+1}$ uses the power identity $r^{t+1}=r\,r^t$; commutativity of natural-number multiplication puts the resulting index in the stated order.
