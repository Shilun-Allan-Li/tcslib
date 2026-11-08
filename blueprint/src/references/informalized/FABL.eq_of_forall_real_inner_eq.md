<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/VectorValuedFourier.lean :: FABL.eq_of_forall_real_inner_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality from inner products

**Claim.** In a real inner product space, if u and v have equal inner products with every vector w, then u=v.

**Proof.** Take the difference u−v. By bilinearity in the second argument and the assumed equality for every w, its inner product with any w is zero; in particular, choosing w=u−v gives ⟨u−v,u−v⟩=0. Positive definiteness of the inner product implies u−v=0, hence u=v.
