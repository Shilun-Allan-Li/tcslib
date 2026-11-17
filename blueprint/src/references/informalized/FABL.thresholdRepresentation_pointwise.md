<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ChowTheorem.lean :: FABL.thresholdRepresentation_pointwise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise comparison with a threshold representation

**Claim.** If $f$ is represented by the threshold sign of a polynomial $p$ and $p$ never vanishes, then at every input $x$, $g(x)p(x)\le f(x)p(x)$; the inequality is strict whenever $g(x)\ne f(x)$.

**Proof.** Fix $x$. Since Boolean values are $\pm1$, first consider $f(x)=1$. The representation forces $p(x)\ge0$, and nonvanishing strengthens this to $p(x)>0$. If $g(x)=1$, the two products agree; if $g(x)=-1$, then $g(x)p(x)=-p(x)<p(x)=f(x)p(x)$. Now consider $f(x)=-1$. The representation forces $p(x)<0$. If $g(x)=-1$, the products agree; if $g(x)=1$, then $g(x)p(x)=p(x)<-p(x)=f(x)p(x)$. These cases establish both the weak comparison and strictness when the Boolean values differ. The threshold representation's sign implications are `thresholdSign_of_neg` and `thresholdSign_of_nonneg`.

**Key facts.** `FABL.thresholdSign_of_neg`, `FABL.thresholdSign_of_nonneg`.
