<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_iterate_exists_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value Attained by Repeated Averaging

**Claim.** For every natural number $m$ and real $x$, the $m$-fold interval average of a continuous function equals its value at some point in $[x,x+m\eta]$.

**Proof.** Induct on $m$, allowing the starting point $x$ to vary. When $m=0$, choose the point $x$ itself. For the successor, the next interval average of the $m$-fold average is an average of the continuous function $s\mapsto S_\eta^m\psi(x+s)$ over $[0,\eta]$. The mean-value property for continuous functions on an interval supplies some $t\in[0,\eta]$ at which this function equals its average. Apply the induction hypothesis to the $m$-fold average starting at $x+t$. It supplies $y\in[x+t,x+t+m\eta]$ with that value equal to $\psi(y)$. Since $0\le t\le\eta$, this interval lies inside $[x,x+(m+1)\eta]$. The average therefore equals $\psi(y)$, completing the induction.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.continuous_intervalSmooth_iterate`.
