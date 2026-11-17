<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.pmfExpectation_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation and Scalar Division

**Claim.** For a real-valued function $f$ on a finite probability space and any real scalar $c$, the expectation of $x\mapsto f(x)/c$ is the expectation of $f$ divided by $c$.

**Proof.** Write the expectation as the finite sum $\sum_x (p(x))_{\mathbb R} f(x)$. Dividing each summand by $c$ is the same as dividing the whole finite sum by $c$, by distributivity of scalar division over finite sums. Term by term, $ (p(x))_{\mathbb R}(f(x)/c)=((p(x))_{\mathbb R}f(x))/c$, so the claimed identity follows. This algebraic identity also holds when $c=0$ under the usual totalized real division.
