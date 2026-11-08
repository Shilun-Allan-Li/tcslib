<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/LeftoverHash.lean :: TCSlib.InformationTheory.hashPair_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hashed Pair Probability

**Claim.** For each seed $s\in S$ and output $y\in\beta$, the hashed pair distribution assigns $(s,y)$ probability $|S|^{-1}\sum_{x:f(s,x)=y}X(x)$.

**Proof.** Expanding the mapped product distribution gives a sum over pairs $(a,x)$ whose image $(a,f(a,x))$ equals $(s,y)$. The product outcome has probability $|S|^{-1}X(x)$, so the sum is over those pairs with $a=s$ and $f(s,x)=y$. Summing first over the seed coordinate leaves only $a=s$; the remaining sum is $|S|^{-1}$ times the sum of $X(x)$ over inputs satisfying $f(s,x)=y$.

**Key facts.** `TCSlib.InformationTheory.FinDist.map_apply`, `TCSlib.InformationTheory.FinDist.prod_apply`.
