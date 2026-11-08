<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.IsSharing.smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar multiplication of polynomial sharings

**Claim.** If $f$ shares $x$ with degree bound $d$, then multiplying every share by $c$ gives a sharing of $cx$ with the same degree bound.

**Proof.** Choose a witnessing polynomial $p$ for $f$ and use $c p$ as the witness for the scaled shares. The degree of a product is at most the sum of the degrees, and the constant polynomial with value $c$ has degree at most zero, so $cp$ still has degree less than $d+1$. Its value at zero is $c p(0)=cx$, and at each party's label its value is $c$ times the original share.
