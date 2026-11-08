<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalLogLimits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical logarithmic limits

**Claim.** The logarithm of the critical dimension, divided by $w\log 2$, tends to $1$, and the critical width error tends to $0$.

**Proof.** 1. Write $D_w$ for the critical dimension and $M_w=(\log 2)w2^w$. Since $\log 2>0$, the natural numbers tend to infinity, and $2^w\to\infty$, their product $M_w$ tends to infinity. The dimension asymptotic equivalence (`tribesCriticalDimension_isEquivalent_main`) says $D_w\sim M_w$; consequently $D_w\to\infty$ as well and $D_w/M_w\to1$. Taking logarithms gives $\log(D_w/M_w)\to0$.

2. The normalized logarithm of $M_w$ tends to $1$. Indeed, for positive $w$, expanding the logarithm of $M_w=(\log 2)w2^w$ yields
\[
\frac{\log M_w}{w\log 2}=1+\frac{\log w}{w\log 2}+\frac{\log(\log 2)}{w\log 2}.
\]
The last two terms tend to zero: $\log w=o(w)$ and the denominator grows linearly. Combining this with $\log D_w=\log M_w+\log(D_w/M_w)$ and dividing by $w\log 2$ proves the first limit.

3. For the width error, the definitions of logarithm base $2$ and $M_w$ give, for all sufficiently large $w$,
\[
E_w=-\frac{\log(D_w/M_w)-\log\!\left(\frac{\log D_w}{w\log 2}\right)}{\log 2}.
\]
The first logarithm in the numerator tends to zero by the asymptotic equivalence. By the first limit, the ratio inside the second logarithm tends to $1$, so that logarithm also tends to zero. Since $\log 2\ne0$, the displayed expression tends to zero, proving the second limit.

**Key facts.** `FABL.tribesCriticalDimension_isEquivalent_main`.
