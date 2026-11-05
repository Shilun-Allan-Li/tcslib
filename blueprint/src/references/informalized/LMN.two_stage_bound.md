<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: LMN.two_stage_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# A two-stage bound for random restrictions

**Claim.** Fix parameters $p_1, p_2 \in (0,1]$, a constant $\beta \ge 0$, and two events $E$ and $A$ on restrictions of $n$ variables. Write $\Pr_p[\,\cdot\,]$ for probability under a Bernoulli($p$) random restriction, and $\rho_1 \circ \rho_2$ for the composition that uses the values fixed by $\rho_1$ and fills in $\rho_2$ on the coordinates $\rho_1$ leaves free. If every restriction $\rho_1$ on which $A$ fails satisfies $\Pr_{p_2}[E(\rho_1 \circ \rho_2)] \le \beta$, then $\Pr_{p_1 p_2}[E] \le \Pr_{p_1}[A] + \beta$.

**Proof.** Throughout, write $w_p(\rho) = p^{\,|\mathrm{free}(\rho)|}\bigl((1-p)/2\bigr)^{\,n-|\mathrm{free}(\rho)|}$ for the weight the Bernoulli($p$) law assigns to a restriction $\rho$, so that $\Pr_p[F] = \sum_{\rho} w_p(\rho)\,[F(\rho)]$ for any event $F$, the sum ranging over all restrictions of the $n$ variables.

1. **Factor the $(p_1 p_2)$-restriction into two stages.** The engine of the proof is the composition law for Bernoulli restrictions (`restriction_compose_eq`): drawing a single restriction at parameter $p_1 p_2$ is the same as drawing $\rho_1$ at parameter $p_1$, then drawing $\rho_2$ at parameter $p_2$ on the coordinates $\rho_1$ left free, and composing. At the level of probabilities this reads
\[
\Pr_{p_1 p_2}[E] \;=\; \sum_{\rho_1} w_{p_1}(\rho_1)\,\Pr_{p_2}\bigl[E(\rho_1 \circ \rho_2)\bigr].
\]
(The hypotheses $0 < p_i \le 1$ are exactly what this law requires.) This is the one structural step; the rest is estimation of the resulting sum.

2. **Bound each inner probability.** Fix $\rho_1$, and set $c(\rho_1) = 1$ if $A(\rho_1)$ holds and $c(\rho_1) = \beta$ otherwise. We claim $\Pr_{p_2}[E(\rho_1 \circ \rho_2)] \le c(\rho_1)$. When $A(\rho_1)$ holds this is the trivial bound that a probability never exceeds $1$ (`bernoulliRestrProb_le_one'`); when $A(\rho_1)$ fails it is precisely the standing hypothesis. Because every weight $w_{p_1}(\rho_1)$ is nonnegative (`bernoulliRestrWeight_nonneg'`), we may multiply each term through by its weight and sum, preserving the inequality:
\[
\sum_{\rho_1} w_{p_1}(\rho_1)\,\Pr_{p_2}\bigl[E(\rho_1 \circ \rho_2)\bigr]
\;\le\;
\sum_{\rho_1} w_{p_1}(\rho_1)\,c(\rho_1).
\]

3. **Split the weighted sum along $A$.** Separating the right-hand sum according to whether $A(\rho_1)$ holds,
\[
\sum_{\rho_1} w_{p_1}(\rho_1)\,c(\rho_1)
\;=\;
\sum_{\rho_1 :\, A(\rho_1)} w_{p_1}(\rho_1)
\;+\;
\beta \sum_{\rho_1 :\, \neg A(\rho_1)} w_{p_1}(\rho_1).
\]
The first term is, by the very definition of the restriction probability as the total weight of the favourable restrictions, equal to $\Pr_{p_1}[A]$.

4. **Bound the residual by $\beta$.** It remains to control the second term. The restrictions on which $A$ fails form a subset of all restrictions, and every weight is nonnegative, so
\[
\sum_{\rho_1 :\, \neg A(\rho_1)} w_{p_1}(\rho_1)
\;\le\;
\sum_{\rho_1} w_{p_1}(\rho_1)
\;=\; 1,
\]
the last equality being that the Bernoulli($p_1$) weights form a probability distribution and so sum to one (`bernoulliRestrWeight_sum_one`). Since $\beta \ge 0$, multiplying through gives $\beta \sum_{\neg A} w_{p_1} \le \beta$. Chaining the estimates of steps 1–4 yields
\[
\Pr_{p_1 p_2}[E] \;\le\; \Pr_{p_1}[A] + \beta,
\]
as claimed. $\blacksquare$

**Key facts.** `LMN.restriction_compose_eq`, `SwitchingLemma.bernoulliRestrProb_le_one'`, `SwitchingLemma.bernoulliRestrWeight_nonneg'`, `SwitchingLemma.bernoulliRestrWeight_sum_one`.
