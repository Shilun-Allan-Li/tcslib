<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tendsto_two_pow_mul_log_tribesCriticalDimension_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Logarithmic Dimension Limit

**Claim.** The quantity $2^w\log(D_w)/D_w$, where $D_w$ is the tribes critical dimension, tends to $1$ as $w\to\infty$.

**Proof.** Write $D_w$ for the critical dimension and $M_w=(\log 2)w2^w$. First, $D_w\to\infty$, so $D_w$ is eventually nonzero (\texttt{tendsto\_tribesCriticalDimension\_atTop}). Since $D_w$ is asymptotically equivalent to $M_w$, the ratio $M_w/D_w$ tends to $1$ (\texttt{tribesCriticalDimension\_isEquivalent\_main}). Also, $\log(D_w)/(w\log 2)$ tends to $1$ (\texttt{tendsto\_log\_tribesCriticalDimension\_div\_width}). The product of these two ratios therefore tends to $1$. For all sufficiently large $w$, elementary cancellation, using $w>0$, $D_w>0$, and $\log 2>0$, identifies that product with $2^w\log(D_w)/D_w$. Thus the claimed limit follows.

**Key facts.** `FABL.tendsto_tribesCriticalDimension_atTop`, `FABL.tribesCriticalDimension_isEquivalent_main`, `FABL.tendsto_log_tribesCriticalDimension_div_width`.

**Caveat.** The supplied informal statement describes a broader proposition about tribes asymptotics and bias, but the formal declaration and proof establish only the displayed normalized logarithmic dimension limit.
