<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.localReconstruct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Locality of Shamir Reconstruction

**Claim.** Reconstruction from a finite set $A$ of parties depends only on the shares held by parties in $A$: if two share functions agree at every party in $A$, their reconstructions from $A$ are equal.

**Proof.** By definition, reconstruction from $A$ evaluates at zero the polynomial interpolating the values of the share function on the labels of parties in $A$. Since the two share functions agree at every party in $A$, their prescribed values at all interpolation nodes agree. The interpolation uniqueness principle says that interpolating data that agree on the chosen nodes gives the same polynomial (`Lagrange.interpolate_eq_of_values_eq_on`). Thus the interpolating polynomials, and hence their evaluations at zero, are equal.
