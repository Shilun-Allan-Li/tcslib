<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.IsSharing.mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication of polynomial sharings

**Claim.** If $f$ shares $x$ with degree bound $d$ and $g$ shares $y$ with degree bound $e$, then their pointwise product shares $xy$ with degree bound $d+e$.

**Proof.** Choose witnessing polynomials $p$ and $r$ for the two sharings. Use their product $pr$ to witness the product sharing. The degree of a product is at most the sum of the degrees, and the strict bounds on the degrees of $p$ and $r$ imply that this sum is less than $d+e+1$. At zero, $(pr)(0)=p(0)r(0)=xy$. At each party's label, $(pr)$ evaluates to the product of the two evaluations, which are exactly that party's shares in $f$ and $g$.
