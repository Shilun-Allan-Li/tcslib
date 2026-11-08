<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.normalize_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalization at the Origin

**Claim.** For any function $f : (\mathbb{Z}/k\mathbb{Z})^n \to \mathbb{Z}/k\mathbb{Z}$, its normalization satisfies $(\mathrm{normalize}\,f)(0)=0$.

**Proof.** By definition, $(\mathrm{normalize}\,f)(0)=f(0)-f(0)$. An element subtracted from itself is zero, so $(\mathrm{normalize}\,f)(0)=0$.
