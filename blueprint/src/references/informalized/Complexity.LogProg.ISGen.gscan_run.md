<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean :: Complexity.LogProg.ISGen.gscan_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-length scan initialization

**Claim.** If the type-$0$ oracle answers the encoded query for $k$ by whether $k<|x|$, and the registers are bounded with $\sigma.n\le |x|\le B$, then the scan state with registers $\sigma$ has the same termination, register-bound, and acceptance property as the state at $lg0$ with its input-length register set to $|x|$.

**Proof.** Induct on the difference $d=|x|-\sigma.n$, keeping the register bound and $\sigma.n\le |x|$. When $d=0$, the input-length register already equals $|x|$. The scan query asks whether $\sigma.n<|x|$, so the oracle answers false; the machine proceeds to $lg0$, and the resulting register state is the assumed one. The negative-query semantic principle gives the conclusion (`NSem.call_neg`), with equality of states transferring the hypothesis (`IG.of_eq`). When $d>0$, the query is true, so the machine increments $n$ and returns to scan (`NSem.call_pos`, followed by `NSem.inc`). The new difference is smaller by one, and the bounds remain valid; apply the induction hypothesis to the incremented state. This proves the desired property for the original scan state.

**Key facts.** `Complexity.LogProg.ISGen.IG.of_eq`, `Complexity.LogProg.NSem.call_neg`, `Complexity.LogProg.NSem.call_pos`, `Complexity.LogProg.NSem.inc`.
