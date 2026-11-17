<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.stepRel_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of a Single Nondeterministic Step

**Claim.** Under the stated space bound, the encoded configuration reached using choice string $v$ has a step within the space window $s$ to the encoding reached using $v$ followed by $b$ exactly when the proposed code $c'$ is that latter configuration's encoding.

**Proof.** First, appending the bit $b$ to the choice string means taking one step with choice $b$ from the configuration reached after $v$; this follows from the run-on-appended-strings law and the empty-run identity (\texttt{runWith\_append}, \texttt{runWith\_cons}, and \texttt{runWith\_nil}).

For the forward implication, unpack membership in the step language (\texttt{mem\_stepLang}) to obtain configurations $C,C'$ in the space window, with $C$'s code equal to the code after running $v$, a nondeterministic step from $C$ to $C'$, and $C'$'s code equal to $c'$. Both $C$ and the actual configuration after $v$ lie in the window, by the assumed space bound (\texttt{inWin\_run}). Equal codes for configurations in the window imply equal core summaries (\texttt{coreSum\_eq\_of\_code\_eq}). A core summary determines the core summary after taking the same chosen step (\texttt{coreSum\_stepWith}); moreover, fixing the machine's choice to $b$ makes every nominal choice select that same step (\texttt{stepWith\_fixCoin}). Therefore $C'$ and the actual next configuration have equal core summaries, hence equal configuration encodings by \texttt{cfgWord\_congr}; applying the binary-value encoding gives the desired equality of codes.

Conversely, suppose $c'$ is the code of the configuration after $v$ followed by $b$. Use the actual configurations before and after that step as the witnesses in the step-language characterization. The first is in the window by \texttt{inWin\_run}; the second is also in the window by the same bound applied to the extended choice string. The appended bit supplies the required nondeterministic transition, with the fixed-choice identity confirming it is precisely the $b$-step. Their codes are the given code and $c'$, so the encoded pair belongs to the step language.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`, `Complexity.Codec.mem_stepLang`, `Randomized.BPLInP.inWin_run`, `Randomized.BPLInP.coreSum_eq_of_code_eq`, `Turing.NDTM.coreSum_stepWith`, `Randomized.BPLInP.stepWith_fixCoin`, `Complexity.Codec.cfgWord_congr`.
