<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.acceptLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Language Characterization

**Claim.** Under the space-bound hypotheses, the encoded input, run configuration code, and space bound belong to the acceptance language exactly when the run using choice string $v$ halts and outputs exactly $[\mathrm{true}]$.

**Proof.** Unpack membership in the acceptance language (`Complexity.Codec.mem_acceptLang`). For the forward implication, this gives a configuration $C$ in the space window whose code is the code of the run, and which is halting with output $[\mathrm{true}]$. The run itself is in the same space window by the space-use bound (`Randomized.BPLInP.inWin_run`). Thus the equal codes determine equal cores and output summaries (`Randomized.BPLInP.coreSum_eq_of_code_eq`). Projecting this equality onto the machine-state component transfers the halting condition from $C$ to the run. Projecting onto the output-summary component, and using that the summary is accepting exactly for output $[\mathrm{true}]$ (`Turing.outSummary_eq_accept_iff`), gives the required output condition. Conversely, if the run halts and has output $[\mathrm{true}]$, choose that run itself as the witness configuration. It lies in the space window, and its code is the specified code by reflexivity, so it witnesses language membership.

**Key facts.** `Complexity.Codec.mem_acceptLang`, `Randomized.BPLInP.inWin_run`, `Randomized.BPLInP.coreSum_eq_of_code_eq`, `Turing.outSummary_eq_accept_iff`.
