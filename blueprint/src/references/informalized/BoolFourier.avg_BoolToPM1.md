<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.avg_BoolToPM1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the sign embedding

**Claim.** The average of the two values of the Bool-to-$\pm1$ embedding is zero: $(\mathrm{BoolToPM1}(\mathtt{false})+\mathrm{BoolToPM1}(\mathtt{true}))/2=0$.

**Proof.** By definition, the embedding sends false to $1$ and true to $-1$. Their sum is $1+(-1)=0$, so dividing by $2$ still gives zero.
