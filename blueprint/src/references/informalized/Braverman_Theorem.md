<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: Braverman_Theorem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Braverman fooling bound

**Claim.** If the Braverman property holds, then there is a positive constant $c$ such that for each allowed $n,d,m,\varepsilon$ one can choose a natural number $k\le (\log(m/\varepsilon)+2)^{cd}$ for which every $k$-wise independent distribution fools all circuits of depth at most $d$ and size at most $m$ to error $\varepsilon$.

**Proof.** Take a witness $c_B>0$ to the Braverman property and set the final exponent constant to $c_B+1$. For given parameters, put $B=\log(m/\varepsilon)+2$, $E=c_Bd$, and $k=\lceil B^E\rceil$. The ceiling bound for the Braverman parameter gives $k\le B^{(c_B+1)d}$. Now fix a $k$-wise independent distribution $\mu$ and a circuit $C$ with the required depth and size bounds. The Braverman property supplies degree-$k$ lower and upper sandwiching polynomials for the Boolean function computed by $C$, with uniform average gap at most $\varepsilon$. The circuit's probability under any distribution is its expectation of this Boolean function: the identity expressing that probability as a weighted sum is `Circuit.prob_eq_sum`. Applying the fact that such sandwiching polynomials imply fooling (`Sandwiching_Implies_Fooling`) shows that the difference between the expectation under $\mu$ and the uniform expectation is at most $\varepsilon$. This holds for every such circuit and distribution, proving the claim.

**Key facts.** `Braverman_Bound_Helper`, `Circuit.prob_eq_sum`, `Sandwiching_Implies_Fooling`.
