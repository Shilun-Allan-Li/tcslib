<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.index_fragment_safe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safety After a Register Update

**Claim.** After replacing the extra tape and its head position and setting the encoded state to $\ell$, the resulting configuration satisfies safety for input length $|v|$ and parameter $S$.

**Proof.** For each original tape, the register update leaves its contents and head position unchanged, so its head bounds follow from the assumed bounds on $c$. For the extra tape, the new head position is $p$, which lies between $-1$ and $|\operatorname{bits}(|v|+1)|$ by hypothesis. These are exactly the required head bounds. Finally, the safety condition about call states is vacuous: the updated state is $\ell$, and the program has no call at $\ell$, so it cannot satisfy the premise that this state has an associated call specification.
