<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.FinTM.exists_certificateShell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Polynomial-Length Certificate Decider

**Claim.** If the machine $P$ correctly halts with output $\mathrm{out}(x,u)$ within the specified time on every certificate $u$ of the prescribed polynomial length, then a finite Boolean machine decides whether an input $y$ has a decomposition $y=xu$ with that certificate length and output $[\mathrm{true}]$, within a bound of the stated form.

**Proof.** The construction assembles machines for splitting a candidate input, preparing work tapes, running the verifier, and checking the resulting Boolean output; the proof then establishes the behavior and time bound of the assembled machine.

1. First choose a machine that solves the length-constrained split problem, with a polynomial time bound, using the split-solver existence theorem (`Turing.FinTM.computesFunInTime_splitSolve`). Convert this into a machine that calls the solver and reaches a designated exit state, with a time bound recorded by `Turing.FinTM.exists_inputCallTM`. A cut-and-compose construction gives a version of this call that can be embedded in a larger machine while preserving the relevant interval before its exit (`Turing.cert_call_cut`).

2. Choose a preparation machine that places the encoded candidate pair on suitable work tapes and establishes the layout needed by the verifier (`Turing.cert_prepare_exists`). Embed the split-solver call into its designated tapes, leaving the remaining tapes blank; the embedding lemma supplies the resulting run and its cut property (`Turing.cert_embed_call`). The split-word length estimate (`Turing.certSplitWord_length`) will later bound this preparation cost in terms of $|y|$.

3. For each input $y$, the split solver either reports no valid split or returns a candidate index $i$. In the first case, the split-language characterization shows $y$ is not in the target language (`Turing.certSplit_language`). The guard machine sees an empty certificate slot and halts with output false (`Turing.certGuard_run`), with the needed first-entry cut supplied by `Turing.certGuard_cut`.

4. In the second case, the split-validity result says the suffix has exactly the required certificate length (`Turing.certSplit_valid`). The verifier hypothesis therefore applies to the prefix and suffix. The preparation output encodes this pair; the encoding-length identity confirms that this encoding is nonempty (`Turing.length_pairEncode`). The guard consequently permits the verifier phase. The certificate-core run theorem simulates the verifier, producing a halt and the prescribed output within the verifier's deadline plus its fixed overhead (`Turing.certCore_run`). The split-language characterization identifies whether that output is true with membership of $y$ in the target language. Composing the guard and verifier phases using the cut-aware composition theorem yields the checked machine's correct halting state and indicator output (`Turing.seamCompTM_run_ofCfg`).

5. Compose the embedded preparation phase with the checked phase, and apply the computation characterization to identify the constructed machine's halt and output with deciding the language (`Turing.FinTM.computesInTime_iff`). The phase-composition result justifies the composed run and its timing (`Turing.seamCompTM_run_ofCfg`). Finally, the split-word length bound, the polynomial lower bound on $(|y|+1)^{c+2}$, and elementary arithmetic bound the preparation, checking, and verifier costs by the claimed expression. Extend the obtained computation to the full time bound using monotonicity of computation in time (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_splitSolve`, `Turing.FinTM.exists_inputCallTM`, `Turing.cert_call_cut`, `Turing.cert_prepare_exists`, `Turing.cert_embed_call`, `Turing.certSplitWord_length`, `Turing.certSplit_language`, `Turing.certGuard_run`, `Turing.certGuard_cut`, `Turing.certSplit_valid`, `Turing.length_pairEncode`, `Turing.certCore_run`, `Turing.seamCompTM_run_ofCfg`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.

**Caveat.** The supplied statement of `certCore_run` is truncated, so its exact output specification cannot be fully checked from the payload; the proof uses it to simulate the verifier and obtain the output needed for the membership test.
