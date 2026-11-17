<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.geom_sum_toOmega -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Geometric Sum of Root Powers

**Claim.** For any residue $j$, the sum of $\mathrm{toOmega}(ja)$ over all residues $a$ equals $k$ if $j=0$ and equals zero otherwise.

**Proof.** Split into the cases $j=0$ and $j\ne0$. If $j=0$, every summand is $1$, giving $k$. If $j\ne0$, put $r=\omega_k^{j.val}$. Rewriting each summand using `toOmega_mul` identifies the sum with the geometric sum $\sum_{a=0}^{k-1}r^a$. The geometric-sum formula makes this zero: the numerator vanishes because $r^k=1$, using `rootOfUnity_pow_k`; the denominator is nonzero because $j.val$ is not divisible by $k$. Primitivity of $\omega_k$ (`isPrimitiveRoot_rootOfUnity`) implies that $r=1$ would force $k$ to divide $j.val$, contradicting $0<j.val<k$. Finally, the residue classes correspond bijectively to the integers from $0$ through $k-1$, so this geometric sum is the original sum.

**Key facts.** `ZkFourier.toOmega_mul`, `ZkFourier.rootOfUnity_pow_k`, `ZkFourier.isPrimitiveRoot_rootOfUnity`.
