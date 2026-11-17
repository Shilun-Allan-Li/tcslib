<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.redirectTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Redirected computation halts on the final bit

**Claim.** If a machine computes $w$ from $x$ in exactly $t$ steps and the final bit of $w$ is $b$, redirecting the machine to halt on $b$ computes empty output from $x$ in exactly $t$ steps.

**Proof.** Translate the computation hypothesis into its two endpoint properties: at time $t$ the original machine is halted and its output is $w$ (`computesInTime_iff`). The redirected-run identity (`redirect_run`) says that the redirected configuration at time $t$ is obtained by applying the redirection to this original endpoint. Because the original machine has halted, the redirect's recorded last bit is the last bit of $w$, namely $b$. The hypothesis that this bit equals the designated halting bit therefore selects the halting branch of the redirection. By construction the redirected machine emits no output, so its endpoint is halted with empty output. Translating these two endpoint properties back through `computesInTime_iff` proves the claim.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.redirect_run`.
