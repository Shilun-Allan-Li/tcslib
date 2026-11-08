<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.IsSharing.add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition of Polynomial Sharings

**Claim.** If $f$ shares $x$ and $g$ shares $y$ using polynomials of degree at most $d$, then their pointwise sum $f+g$ shares $x+y$ using a polynomial of degree at most $d$.

**Proof.** Choose polynomials $p$ and $r$ witnessing the sharing conditions for $f$ and $g$, respectively. The polynomial $p+r$ has degree at most the maximum of the degrees of $p$ and $r$, so its degree is still less than $d+1$. Evaluation at zero respects addition, giving $(p+r)(0)=x+y$. At each party label, evaluation also respects addition: $(f+g)(i)=f(i)+g(i)=p(\mathrm{label}(i))+r(\mathrm{label}(i))=(p+r)(\mathrm{label}(i))$. Thus $p+r$ witnesses that $f+g$ shares $x+y$ with the required degree bound.
