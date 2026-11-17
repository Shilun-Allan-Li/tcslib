<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.lg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm setup reaches its initialized state

**Claim.** If the input-length register contains $k$, all registers are bounded by $B$, and $S.Lg+hv(k)\le B$, then the setup loop reaches the state with input-length register zero and logarithm counter $S.Lg+hv(k)$, with the memory unchanged and the guard maintained.

**Proof.** Use strong induction on $k$. When $k=0$, the test at the logarithm-setup label takes the zero branch directly to the width computation. The logarithm quantity $hv(0)$ is zero, so the reached state is exactly the required one. When $k>0$, the test takes the nonzero branch, the machine halves the input-length counter to $k/2$, and increments the logarithm counter by one. These steps preserve the register bound: the counter only decreases, and the increment is allowed by $S.Lg+hv(k)\le B$. The identity $hv(k)=hv(k/2)+1$ for positive $k$ converts the remaining bound into $S.Lg+1+hv(k/2)\le B$. Since $k/2<k$, the induction hypothesis applies to the updated state and finishes the setup. Reachability is then re-expressed at the specified endpoint state; memory and head position remain unchanged throughout.

**Key facts.** `Complexity.LogProg.ExpBFS.hv_div`, `Complexity.LogProg.ExpBFS.step_of`, `Complexity.LogProg.MReach.refl`, `Complexity.LogProg.ExpBFS.reach_cf`.
