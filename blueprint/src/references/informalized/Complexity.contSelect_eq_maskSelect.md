<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.contSelect_eq_maskSelect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Masked Selections

**Claim.** For any finite Boolean words $m$ and $w$, the two specified procedures for selecting the bits of $w$ indicated by true entries of $m$, stopping when either word ends, produce the same list.

**Proof.** Induct on the mask $m$, generalizing over $w$. If the mask is empty, both procedures return the empty list, regardless of $w$. If the mask begins with a bit $e$ and the other word is empty, both again return the empty list. When both are nonempty, write them as $e::m'$ and $b::w'$. Each procedure emits $[b]$ when $e$ is true and emits nothing when $e$ is false, then applies itself to $m'$ and $w'$. The induction hypothesis identifies those recursive tails, so the full outputs agree.
