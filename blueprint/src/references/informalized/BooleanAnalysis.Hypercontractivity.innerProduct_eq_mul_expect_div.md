<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Holder.lean :: BooleanAnalysis.Hypercontractivity.innerProduct_eq_mul_expect_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rescaling the Inner Product

**Claim.** For nonzero real scalars $A,B$, the inner product of $u$ and $v$ equals $AB$ times the expectation of the product of their respective rescalings by $A$ and $B$.

**Proof.** At each cube point, nonvanishing of $A$ and $B$ gives $u(x)v(x)=AB\,(u(x)/A)(v(x)/B)$. Substitute this pointwise identity into the finite uniform-measure sum defining the inner product. Pulling the constant factor $AB$ outside the sum yields the stated rescaling formula.
