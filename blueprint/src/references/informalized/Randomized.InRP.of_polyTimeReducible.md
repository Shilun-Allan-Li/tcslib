<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.InRP.of_polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# RP closure under polynomial-time reductions

**Claim.** If $L'$ is polynomial-time many-one reducible to $L$ and $L$ is in RP for the polynomial-time verifier model, then $L'$ is also in RP for that model.

**Proof.** Let $f$ be a polynomial-time reduction from $L'$ to $L$, and let $M$ be the RP verifier for $L$. The reduction theorem for efficient verifiers supplies a polynomial random-bit bound large enough to run $M$ on $f(x)$, while the new verifier feeds $M$ the initial segment of its random string having the length required for $f(x)$ (Randomized.exists_eff_reducedVerifier). For a member $x$ of $L'$, the reduction property puts $f(x)$ in $L$. The random-bit truncation fact identifies the new verifier's acceptance probability with that of $M$ on $f(x)$ (Randomized.randProb_take), so it is at least $2/3$. For a nonmember $x$, the reduction property puts $f(x)$ outside $L$. Any random string used by the new verifier has an initial segment of the required length; that segment can be represented as a random assignment (Randomized.exists_ofFn_eq). The RP soundness condition for $M$ then says it rejects on this segment. Thus the new verifier rejects for every random string, establishing the RP conditions.

**Key facts.** `Randomized.exists_eff_reducedVerifier`, `Randomized.randProb_take`, `Randomized.exists_ofFn_eq`.
