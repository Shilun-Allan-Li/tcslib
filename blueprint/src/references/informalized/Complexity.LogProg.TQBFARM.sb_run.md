<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.sb_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Subtraction Run

**Claim.** From label $\mathrm{sb}(b,0)$ with register state $st$, the program reaches the test label $\mathrm{jzC}(b)$ with $V$ set to zero and $C$ replaced by the truncated difference $st.C-st.V$, while all configurations before the endpoint satisfy the precondition and register bound.

**Proof.** The subtraction-loop result (\texttt{Complexity.LogProg.sub_run}) applies to two distinct registers when the loop tests one register for zero, decrements it, and then decrements the other before returning to the test. Here the tested register is $V$ and the other is $C$; these registers are distinct. Starting with $V=st.V$, the loop clears $V$ and performs exactly $st.V$ decrements of $C$, with truncated subtraction if $C$ runs out first. Thus the endpoint has $V=0$ and $C=st.C-st.V$, and the control label is $\mathrm{jzC}(b)$. The bound on every register from $st.Bd\,B$ supplies the boundedness hypothesis of the loop result; translating its register-function endpoint back to the seven-field state gives the claimed run.

**Key facts.** `Complexity.LogProg.TQBFARM.St.Bd.toV`, `Complexity.LogProg.sub_run`.
