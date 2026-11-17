<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.isSharing_degreeReduce -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharing After Degree Reduction

**Claim.** If $u$ is a sharing of $z$ of degree at most $2d$ and $|A|\ge 2d+1$, then degree reduction produces a degree-$d$ sharing of $z$.

**Proof.** For each party $i$ in $A$, the resharer supplies a degree-$d$ sharing of the value $u(i)$. Multiplying that sharing by the coefficient used for recombination preserves degree $d$ and shares the correspondingly scaled value (`IsSharing.smul`). Summing these sharings over $A$ again gives a degree-$d$ sharing, now of the coefficient-weighted sum of the values held by the parties (`IsSharing.sum`). Since $u$ is a degree-at-most-$2d$ sharing and $|A|\ge 2d+1$, the reconstruction property says this weighted sum is $z$ (`IsSharing.recombine_eq`). Substituting that secret into the summed sharing identifies its partywise values with the degree-reduction output, proving the claim.

**Key facts.** `TCSlib.Shamir.IsSharing.smul`, `TCSlib.Shamir.IsSharing.sum`, `TCSlib.Shamir.IsSharing.recombine_eq`.
