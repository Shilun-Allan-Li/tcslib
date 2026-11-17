<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.inputLength_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input length counting loop

**Claim.** Under the stated oracle condition, starting at `scan` with all registers bounded by $B$ and $r\le |x|$, the program reaches `done` with $r=|x|$. Every earlier configuration satisfies $\mathrm{PreS}$ and keeps all registers at most $B$.

**Proof.** Use strong induction on the remaining distance $N=|x|-v(r)$, generalizing over the register assignment. At `scan`, the call is on the whole input paired with the binary word for the current value of $r$. The virtual-word identity for a whole-input call with one register ($\texttt{Complexity.LogProg.vword\_whole₁}$), together with the oracle hypothesis, shows that the call answers positively exactly when $v(r)<|x|$.

If $v(r)<|x|$, the program goes to `inc`, increments $r$, and returns to `scan`. The updated register remains at most $B$, because its new value is at most $|x|\le B$; all other registers retain their bounds. The remaining distance strictly decreases, so the induction hypothesis applies at the new scan configuration. The reachability composition lemma ($\texttt{AReach.step}$) adds the scan and increment steps to that inductive run, with the precondition and register bound checked at each configuration.

If the scan test is negative, the assumption $v(r)\le |x|$ forces $v(r)=|x|$. The call therefore goes to `done` without changing registers. The endpoint update to $r$ by $|x|$ leaves the assignment unchanged, and the single-step reachability fact ($\texttt{AReach.single}$) supplies the claimed reach.

**Key facts.** `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.single`.
