<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.certVerdict_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Step Certificate Verdict

**Claim.** Starting in state $0$ with the capacity tape holding $w$ from cell $0$ and its head at $|w|$, the verdict machine halts in three steps and appends to the original output the bit indicating whether $w=[\mathrm{true}]$.

**Proof.** The first transition, from state $0$, moves the capacity-tape head one cell left and enters state $1$. The next transition tests the symbol now under that head. If it is true, the machine moves left again and enters state $2$; otherwise it halts and appends false. In state $2$, it halts on the third transition, appending the bit that records whether the scanned cell is blank. The tail-test lemma (\texttt{Turing.cert\_tail\_test}) states that the two readings used in these tests—true at the last cell and blank at the preceding cell—hold together exactly when $w=[\mathrm{true}]$. Thus the two halting branches append precisely the desired indicator. The run-after-one-step identity (\texttt{Turing.MultiTapeTM.runFrom\_succ\_eq\_step}), applied to unfold the three transitions, gives both the final halted state and the output claimed.

**Key facts.** `Turing.cert_tail_test`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
