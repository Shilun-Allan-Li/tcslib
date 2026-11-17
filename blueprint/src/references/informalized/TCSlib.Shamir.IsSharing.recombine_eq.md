<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.IsSharing.recombine_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from enough shares

**Claim.** If $f$ shares $x$ with degree bound $d$, then for every finite set $A$ of parties with $d+1\le |A|$, its reconstruction sum equals $x$.

**Proof.** Choose a witnessing polynomial $p$ for the sharing. The party-label map is injective on $A$ (`TCSlib.Shamir.label_injective`), and the size hypothesis gives $\deg p<|A|$. The uniqueness theorem for interpolation says that a polynomial of degree less than the number of interpolation points is determined by its values there. Since $p$ evaluates at each party's label to that party's share, it equals the polynomial interpolating the shares on $A$. The reconstruction sum is the value at zero of that interpolating polynomial (`TCSlib.Shamir.recombine_eq_eval_interpolate`); substituting $p$ and using $p(0)=x$ proves the result.

**Key facts.** `TCSlib.Shamir.label_injective`, `TCSlib.Shamir.recombine_eq_eval_interpolate`.
