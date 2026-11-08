<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseDuality.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.signed_power_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed-power duality identities

**Claim.** For $q>2$, if $g=z|z|^{q-2}$, then $zg=|z|^q$ and $|g|^{q/(q-1)}=|z|^q$.

**Proof.** If $z=0$, both identities follow from the zero-power conventions, since the exponents $q$ and $q/(q-1)$ are positive. Otherwise $|z|>0$. For the first identity, use $z^2=|z|^2$ to write $zg=|z|^2|z|^{q-2}=|z|^q$, combining powers with positive base. For the second, taking absolute values gives $|g|=|z|^{q-1}$, again by combining powers of $|z|$. Raising to $q/(q-1)$ gives $|g|^{q/(q-1)}=|z|^q$.
