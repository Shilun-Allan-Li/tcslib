<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.zkDot_add_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right-additivity of the dot product

**Claim.** For vectors $s,x,y\in(\mathbb{Z}/k\mathbb{Z})^n$, the dot product satisfies $s\cdot(x+y)=s\cdot x+s\cdot y$.

**Proof.** At each coordinate $i$, distributivity gives $s_i(x_i+y_i)=s_ix_i+s_iy_i$. Summing these equalities over all coordinates and distributing the finite sum over addition gives $\sum_i s_i(x_i+y_i)=\sum_i s_ix_i+\sum_i s_iy_i$, which is the claimed identity.
