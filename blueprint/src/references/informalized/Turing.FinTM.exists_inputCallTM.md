<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: Turing.FinTM.exists_inputCallTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Call Machine

**Claim.** A finite Boolean machine with at least one work tape can, from a clean seam with blank work tapes, reach a clean exit seam holding $f(x)$ on its first work tape and blank tapes elsewhere, in positive time bounded linearly by $T(|x|)+|x|+|f(x)|+1$, with no earlier positive-time visit to the exit.

**Proof.** Start with the install-call machine for $M$: it receives its argument on a work tape and reaches a clean exit with $f(x)$ installed, within the stated call bound. There are two cases. If its entry and exit states coincide, modify the machine using the seam-release construction, which separates the initial seam state from its returned exit state while preserving the run and its clean endpoint. If they differ, the install-call machine’s guarantee excludes the exit at every earlier positive time; the only additional time to check is zero, where the distinctness of entry and exit excludes it. Thus in either case there is a call machine whose exit is avoided at all times before its positive completion time. Now prepend an input-copy phase that copies the native input $x$ onto the first work tape. The copier reaches its done seam after $2|x|+2$ steps and does not visit that seam state earlier. The seam-composition run lemma joins this copier to the call machine, and its first-return lemma ensures the combined machine does not reach the final exit prematurely. The combined time is $2|x|+3+t$, where $t$ is the call duration, and the bound follows by absorbing the copy time into the coefficient $b+3$.

**Key facts.** `Turing.FinTM.exists_installCallTM`, `Turing.seamReleaseTM_firstReturn`, `Turing.inputCopyTM_run_ofCfg`, `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`.
