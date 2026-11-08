<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.signed_power_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed power dual identities

**Claim.** For $q>1$ and $z\in\mathbb R$, set $g=z|z|^{q-2}$. Then $zg=|z|^q$ and $|g|^{q/(q-1)}=|z|^q$.

**Proof.** Since $q>1$, both $q$ and $q-1$ are nonzero. If $z=0$, both identities follow from the zero-exponent-power convention for positive exponents. Otherwise $|z|>0$, so real powers of $|z|$ combine by adding their exponents. For the first identity, $z^2=|z|^2$, hence $zg=|z|^2|z|^{q-2}=|z|^q$. For the second, taking absolute values gives $|g|=|z|^{q-1}$; raising this to $q/(q-1)$ yields $|g|^{q/(q-1)}=|z|^q$.
