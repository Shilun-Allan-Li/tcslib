<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.bentkusWhitening_norm_sq_eq_inv_quadraticForm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Whitened Norm and Inverse Quadratic Form

**Claim.** For a positive definite real matrix $S$ and vector $z$, the squared norm of the image of $z$ under the inverse square root of $S$ equals the quadratic form $z^{\mathsf T}S^{-1}z$.

**Proof.** Let $R=S^{1/2}$ and $T=R^{-1}$. The square-root identity gives $R^2=S$, and the whitening identity gives $TR=I$. Consequently, $(T^2)S=T(TR)R=I$, so $T^2=S^{-1}$. Let $L$ be the linear map represented by $T$. The squared-norm identity for an adjoint expresses $\|Lz\|^2$ as the inner product of $z$ with $L^*Lz$. The whitening map is self-adjoint, so $L^*=L$ and $L^*L=L^2$. Composition of the maps represented by matrices corresponds to matrix multiplication; since $T^2=S^{-1}$, this composition is the map represented by $S^{-1}$. Finally, the Euclidean inner product with that image is the matrix quadratic form $z\mathbin{\cdot_v}(S^{-1}z)$, as required.
