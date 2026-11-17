<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.IsSharing.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Sharing Degree Bound

**Claim.** If $d\leq e$ and $f$ shares $x$ using a polynomial of degree at most $d$, then $f$ also shares $x$ using a polynomial of degree at most $e$.

**Proof.** Take a polynomial $p$ witnessing that $f$ shares $x$ with degree bound $d$. Since $d\leq e$, we have $d+1\leq e+1$, so the degree bound $\degree(p)<d+1$ implies $\degree(p)<e+1$. The same polynomial still evaluates to $x$ at zero and agrees with $f$ at every party label. Hence it witnesses the sharing condition with bound $e$.
