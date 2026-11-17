<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.goR_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward cleanup run

**Claim.** Under the stated marking, position, and bound hypotheses, the cleanup machine's rightward walk keeps all work-head positions within the bound through time $n+1$ and then enters the erasing phase with both heads at tape $i$ positioned at $b$.

**Proof.** Proceed by induction on $n$, keeping the other head positions arbitrary subject to the bound. When $n=0$, the equation $b+1-D_p(i)=0$ gives $D_p(i)=b+1$. The marking function has no symbol at that position, so the rightward-walk transition reverses direction and enters the erasing phase, moving both heads to $b$. The initial positions satisfy the bound, and the updated position $b$ does too because $0\le b$ and $b+1\le B$; thus both the initial and one-step configurations obey the bound.

For the successor case, the hypotheses give $a\le D_p(i)\le b$. The marking function therefore has a symbol at the scanned position, so the machine continues right, moving both heads at index $i$ from $D_p(i)$ to $D_p(i)+1$. This updated position remains in $[-B,B]$: the lower bound follows from $a\le D_p(i)$ and the upper bound follows from $b+1\le B$. All other positions are unchanged, so the updated configuration meets the induction hypotheses with the remaining distance reduced by one. Apply the induction hypothesis to this configuration. Every positive time in the original run is one step followed by a time in that shorter run, so its bound follows from the induction result; time zero follows directly from the original bound. The induction's endpoint puts both heads at $b$ in the erasing phase, as required.

**Key facts.** `Complexity.LogProg.PB_ccfg`, `Complexity.LogProg.abs_update_le`, `Complexity.LogProg.apply_clAct`, `Complexity.LogProg.ccfg_mark`, `Complexity.LogProg.ccfg_state`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
