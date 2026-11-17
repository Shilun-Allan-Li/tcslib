<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of Multilinear Random Evaluation

**Claim.** For a positive integer $p$, independent random variables each in $L^p$ have the property that every multilinear polynomial in them, with real coefficients, belongs to $L^p$.

**Proof.** For each subset $S$ of the coordinate indices, first show that the product of the variables indexed by $S$ belongs to $L^p$. Induct on the finite set $S$. The empty product is the constant $1$, which is integrable on a probability space. For the induction step, write the product as $X_i$ times the product over the remaining indices. The latter product is measurable and in $L^p$ by induction. Independence of the variables implies independence of $X_i$ and that product; applying the measurable map $x\mapsto |x|^p$ preserves independence. Thus the expectation of the product of their $p$th absolute powers factors, and is finite because each factor has finite $p$th moment. This proves the product is in $L^p$.

The multilinear evaluation is a finite sum, over all subsets $S$, of these products multiplied by the corresponding real coefficient. Multiplication by a constant preserves $L^p$, and finite sums of $L^p$ functions remain in $L^p$. Hence the entire evaluation belongs to $L^p$.
