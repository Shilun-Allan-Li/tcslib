<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Replacement.lean :: BooleanAnalysis.GaussianSpace.independent_affine_replacement_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-order affine replacement bound

**Claim.** Under the stated moment, independence, smoothness, and integrability hypotheses, replacing $U$ by $V$ in the affine input changes the expectation of $\psi$ by at most $(3C/4)\mathbb E[D^4]$.

**Proof.** First, $D\in L^4$ implies that $D^4$ is integrable (`integrable_mul_pow_of_memLp`). Fix real numbers $a,d$. The fourth-order affine replacement estimate for independent inputs with matching first three moments and the prescribed fourth-moment bounds gives a difference of conditional expectations at most $(3C/4)d^4$ (`affine_replacement_bound`). Apply the independent affine comparison bound with $B(a,d)=(3C/4)d^4$: the independence assumptions allow the scalar estimate to be integrated over the law of $(A,D)$, while the given integrability hypotheses apply to the two composed functions (`independent_affine_comparison_bound`). The bound becomes the integral of $(3C/4)D^4$, which is $(3C/4)\int D^4\,d\mu$ by taking the constant factor outside the integral. This is the claimed estimate.

**Key facts.** `BooleanAnalysis.Hypercontractivity.integrable_mul_pow_of_memLp`, `BooleanAnalysis.GaussianSpace.affine_replacement_bound`, `BooleanAnalysis.GaussianSpace.independent_affine_comparison_bound`.
