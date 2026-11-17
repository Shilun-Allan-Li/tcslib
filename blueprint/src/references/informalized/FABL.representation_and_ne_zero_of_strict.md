<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/IntegralThresholdRepresentations.lean :: FABL.representation_and_ne_zero_of_strict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict sign representation

**Claim.** If $f(x)p(x)>0$ for every $x$, where $f$ takes values in $\{-1,1\}$, then $f(x)$ is the threshold sign of $p(x)$ and $p(x)$ is nonzero at every $x$.

**Proof.** Fix $x$. If $f(x)=1$, strict positivity of $f(x)p(x)$ implies $p(x)>0$, so the threshold sign is $1$ (`thresholdSign_of_nonneg`). If $f(x)=-1$, then the product is $-p(x)>0$, hence $p(x)<0$, and the threshold sign is $-1$ (`signValue_neg_one`, `thresholdSign_of_neg`). These two possible values of $f(x)$ establish the representation. Finally, if $p(x)=0$, then $f(x)p(x)=0$, contradicting the assumed strict positivity; thus $p(x)\ne0$.

**Key facts.** `FABL.signValue_neg_one`, `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
