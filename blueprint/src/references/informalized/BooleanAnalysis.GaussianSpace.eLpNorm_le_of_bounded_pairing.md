<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Duality.lean :: BooleanAnalysis.GaussianSpace.eLpNorm_le_of_bounded_pairing -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An $L^q$ Bound from Bounded Pairings

**Claim.** Under the stated bounded-pairing hypothesis, the nonnegative bounded function $v$, dominated almost everywhere by $|u|$, has $L^q(\mu)$ norm at most $C$.

**Proof.** Let $r=q/(q-1)$, so $1/r+1/q=1$. Choose a signed test function $g$ whose magnitude is $v^{q-1}$ and whose sign agrees with $u$: it equals $v^{q-1}$ where $u\ge0$ and $-v^{q-1}$ where $u<0$. The measurability assumptions on $u$ and $v$ make this test measurable, and the bounds $0\le v\le B$ show it is essentially bounded, so it is allowed in the pairing hypothesis. Almost everywhere, $|g|=v^{q-1}$ and $ug=|u|v^{q-1}$. Consequently, the integral of $v^q$ is at most the integral of $ug$, which is at most its absolute value and hence at most $C\|g\|_{L^r}$. The choice of exponent gives $|g|^r=v^q$, so writing $A=\int v^q\,d\mu$, this inequality becomes $A\le C A^{1/r}$. If $A=0$, the desired norm bound follows immediately; if $A>0$, divide by $A^{1/r}$ to obtain $A^{1/q}\le C$. Since $v$ is nonnegative and essentially bounded on a probability space, its $L^q$ norm is precisely $A^{1/q}$, proving the claim.
