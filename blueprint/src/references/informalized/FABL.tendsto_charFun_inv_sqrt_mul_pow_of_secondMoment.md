<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.tendsto_charFun_inv_sqrt_mul_pow_of_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characteristic function limit from the second moment

**Claim.** Under the stated measurability, finite second moment, zero mean, and second-moment hypotheses, $\varphi(1/\sqrt n)^n$ tends to $\exp(-q/2)$.

**Proof.** The second-order characteristic-function expansion says that $\varphi(t)-(1-qt^2/2)=o(t^2)$ as $t\to0$ (`taylor_charFun_two_of_secondMoment`). Since $n^{-1/2}\to0$, composing this expansion with $t=n^{-1/2}$ shows that $\varphi(n^{-1/2})$ differs from $1-q/(2n)$ by a term that is $o(1/n)$; here $(n^{-1/2})^2=1/n$. The standard exponential limit for powers of a sequence of the form $1+z/n+o(1/n)$, with $z=-q/2$, now yields the limit $\exp(-q/2)$.

**Key facts.** `FABL.taylor_charFun_two_of_secondMoment`.
