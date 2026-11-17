<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.UTab.psnS_toBitSrc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Previous-Snapshot Source Translation

**Claim.** When register $LB$ equals $t$ times the configuration stride, translating the snapshot-source list with the flag indicating $t=0$ gives the source list for the preceding snapshot.

**Proof.** Compare the two lists entry by entry; both have the snapshot width as their length. If $t=0$, the flag is true, so each source is a false constant, exactly as in the definition of the previous-snapshot sources at time zero. If $t\ne0$, the flag is false, and each translated source is a block source whose instruction index is $\rho(LB)-1$. Write $t=t'+1$. Using $\rho(LB)=t\,\mathrm{cfgStride}$, this index simplifies to $t'\,\mathrm{cfgStride}$. Since $t-1=t'$, this is the preceding snapshot's index; the hypothesis that $|\ell|=N$ makes the stride and snapshot-index expressions agree. The bit position is unchanged, so the entries coincide.
