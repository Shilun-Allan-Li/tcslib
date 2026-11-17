<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Defs.lean :: TCSlib.SecretSharing.Scheme.PerfectPrivacy.card_view_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal View Counts under Perfect Privacy

**Claim.** If the scheme has perfect privacy for the access structure, then for every unauthorized set $B$, any two secrets, and any assignment $w$, the numbers of random choices yielding view $w$ on $B$ under those secrets are equal.

**Proof.** Perfect privacy supplies a bijection $e$ on the randomness space such that, for every random choice $r$ and every party $i\in B$, the share under the second secret at $e(r)$ equals the share under the first secret at $r$. Consequently, if $r$ produces view $w$ under the first secret, then $e(r)$ produces view $w$ under the second, so this bijection restricts to a map between the two sets of random choices counted in the claim. Its inverse is induced by $e^{-1}$. The privacy equality applied to $e^{-1}(r)$, together with $e(e^{-1}(r))=r$, shows that the inverse map also preserves the required view condition. These restricted maps are inverse bijections, and bijective finite-type cardinality is invariant under equivalence; hence the two cardinalities agree.
