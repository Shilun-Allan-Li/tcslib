<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Interpolation.lean :: TCSlib.Interpolation.exists_unique_degreeLT_eval_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unique Polynomial Interpolation

**Claim.** Given a field $F$, a finite set $s\subseteq\iota$, an evaluation map $v$ injective on $s$, and prescribed values $w$, there is a unique polynomial of degree less than $|s|$ that takes the value $w(i)$ at each point $v(i)$ for $i\in s$.

**Proof.** Take the Lagrange interpolation polynomial associated to $s$, the nodes $v(i)$, and the prescribed values $w(i)$. The degree bound for Lagrange interpolation gives degree less than $|s|$, and the interpolation property gives the required value at every node indexed by $s$. For uniqueness, any polynomial of degree less than $|s|$ with those same values equals the Lagrange interpolation polynomial, by the uniqueness theorem for interpolation at distinct nodes. The injectivity of $v$ on $s$ ensures those nodes are distinct.
