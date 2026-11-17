<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.recombine_eq_reconstruct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recombination equals reconstruction

**Claim.** For every finite set of parties and every assignment of shares, recombination equals reconstruction by the specified scheme.

**Proof.** By the recombination formula for interpolation, recombining the shares equals the interpolating polynomial's value at zero. The scheme reconstructs precisely by taking that same interpolation polynomial's value at zero. Thus the two quantities agree.

**Key facts.** `TCSlib.Shamir.recombine_eq_eval_interpolate`.
