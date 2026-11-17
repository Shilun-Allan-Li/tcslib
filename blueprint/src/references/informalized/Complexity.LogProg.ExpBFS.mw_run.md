<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.mw_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Register Addition Run

**Claim.** Starting at the multiplication-loop stage indexed by $i$, the machine reaches the width-clear instruction with $w=K_0X$, all other registers unchanged, and memory and head position preserved; the register and head guards hold throughout.

**Proof.** Use induction on $j=K_0-i$. In the zero case, the assumptions $i<K_0$ and $K_0-i=0$ are incompatible, so the case is impossible. In the successor case, first run the copy loop at index $i$. The inequality $(i+1)X\le K_0X\le B$, together with $w=iX$, gives $w+X\le B$. The copy-loop result therefore adds $X$ to $w$, leaving the other registers unchanged and preserving the guard. If $i+1<K_0$, the next loop index is $i+1$ and the remaining distance is $j$; apply the induction hypothesis and concatenate the runs using `MReach.trans`. If instead $i+1\not<K_0$, then $i+1=K_0$, so this final copy loop exits directly at the width-clear instruction. Its updated width is $iX+X=K_0X$, as required. In both cases `reach_cf` identifies the endpoint with the stated register record and keeps memory and the head at their initial values.

**Key facts.** `Complexity.LogProg.ExpBFS.cp_run`, `Complexity.LogProg.MReach.trans`, `Complexity.LogProg.ExpBFS.reach_cf`.
