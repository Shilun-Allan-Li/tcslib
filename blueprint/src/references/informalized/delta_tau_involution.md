<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: delta_tau_involution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# An involution of the interval $[0,\tfrac12]$

**Claim.** Fix a real number $\delta$ with $0 \le \delta \le \tfrac12$ and set $\tau = \tfrac12 - \sqrt{\delta(1-\delta)}$. Then $\tau$ again lies in $[0,\tfrac12]$ and the rule recovers $\delta$ when applied to $\tau$: one has $\tfrac12 - \sqrt{\tau(1-\tau)} = \delta$. Consequently the map $x \mapsto \tfrac12 - \sqrt{x(1-x)}$ is an involution of $[0,\tfrac12]$.

**Proof.** Write $s = \sqrt{\delta(1-\delta)}$, so that $\tau = \tfrac12 - s$. The whole argument turns on a single algebraic identity, after which the result falls out by taking a square root of a perfect square. The Lean proof follows exactly this route: it first clears the inner square root by squaring, then rearranges the goal into the form "$\sqrt{\cdot} = \text{something}$" and discharges it by the characterisation of the square root as the inverse of squaring on the nonnegatives.

1. **The product $\tau(1-\tau)$ is a perfect square.** Since $\tau = \tfrac12 - s$, we have $1-\tau = \tfrac12 + s$, and therefore
\[
\tau(1-\tau) = \left(\tfrac12 - s\right)\left(\tfrac12 + s\right) = \tfrac14 - s^{2}.
\]
This is pure ring algebra — expanding the product into a difference of squares — and is the content of the initial normalisation step.

2. **Eliminate the inner root.** By construction $s = \sqrt{\delta(1-\delta)}$, and $\delta(1-\delta) \ge 0$: the factor $\delta$ is nonnegative by hypothesis, and $1-\delta \ge 0$ because $\delta \le \tfrac12 \le 1$. Hence squaring undoes the square root (`Real.sq_sqrt`, which gives $\sqrt{a}^{2}=a$ whenever $a \ge 0$), so $s^{2} = \delta(1-\delta)$. The nonnegativity side-condition is the one fed to the lemma, and it is a routine linear-arithmetic check from $0 \le \delta \le \tfrac12$. Substituting,
\[
\tau(1-\tau) = \tfrac14 - \delta(1-\delta) = \tfrac14 - \delta + \delta^{2} = \left(\delta - \tfrac12\right)^{2} = \left(\tfrac12 - \delta\right)^{2}.
\]

3. **Rearrange the goal.** The claim $\delta = \tfrac12 - \sqrt{\tau(1-\tau)}$ is transposed into the equivalent form
\[
\sqrt{\tau(1-\tau)} = \tfrac12 - \delta,
\]
simply by moving the terms across the equality (this is the bookkeeping done by the `eq_sub_iff_add_eq` rewrites).

4. **Take the square root of the square.** It remains to verify $\sqrt{\tau(1-\tau)} = \tfrac12 - \delta$. Using the characterisation of the square root as the inverse of squaring on the nonnegatives (`Real.sqrt_eq_iff_mul_self_eq`): to prove $\sqrt{a} = b$ it suffices that $b \ge 0$ and $b \cdot b = a$. Here $b = \tfrac12 - \delta \ge 0$, again because $\delta \le \tfrac12$, and by Step 2 we have $b^{2} = \left(\tfrac12 - \delta\right)^{2} = \tau(1-\tau) = a$. Both the sign condition and the squared-equality identity are elementary consequences of $0 \le \delta \le \tfrac12$ (closed by `nlinarith`). This is precisely the step where $\delta \le \tfrac12$ is essential: $\sqrt{(\tfrac12-\delta)^{2}} = \lvert \tfrac12 - \delta\rvert$, and the hypothesis is what lets us drop the absolute value as $\tfrac12 - \delta$ rather than $\delta - \tfrac12$.

Putting the pieces together, $\tfrac12 - \sqrt{\tau(1-\tau)} = \tfrac12 - (\tfrac12 - \delta) = \delta$, which is the asserted identity. Since both $\delta$ and $\tau = \tfrac12 - s$ lie in $[0,\tfrac12]$ — note $0 \le s = \sqrt{\delta(1-\delta)} \le \tfrac12$, the upper bound because $\delta(1-\delta) \le \tfrac14$ — the rule is a genuine self-map of $[0,\tfrac12]$, and the identity just proved shows it is its own inverse, i.e. an involution.
