<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.imageCfg_safe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safety of an Encoded Configuration

**Claim.** The encoded configuration obtained from $c$ with index $i$ and phase $\mathrm{ph}$ satisfies the work-head bounds and call-state conditions defining safety at input length $|v|$ and parameter $S$.

**Proof.** Check the head bounds separately for the extra tape and for each original tape. For the extra tape, its head is at zero, which lies between the prescribed lower bound $-1$ and upper bound $|\operatorname{bits}(|v|+1)|$. For each original tape, the encoded head is exactly the corresponding head of $c$, so its bounds follow from the hypothesis that those heads lie in $[-S,S]$. For the call-state condition, whenever the encoded state is a call state, its input head is at position $1$, its extra-tape head is at $0$, and that tape still stores $\operatorname{bits}(i)$. The assumption $i\le |v|$ supplies the required index bound.
