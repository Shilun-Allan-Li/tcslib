<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRunTM_silent_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Silent simulation and acceptance specification

**Claim.** Under the stated tape embedding, verifier-run, and timing hypotheses, the combined machine halts on every choice word of the specified exact length. For every larger length $B$, some length-$B$ choice word makes it halt with output $[\mathrm{true}]$ exactly when some length-$m$ word makes $R$ reach acceptance without an earlier accepting or rejecting visit.

**Proof.** The assumed profile is nonblank exactly on the cells from $0$ through $m-1$. Thus the configuration $c_P$ has a nonblank block of length $m$ on tape $\iota(j_R)$, with blanks immediately before and after it. These facts establish the block, right-end, and left-end conditions required by the handoff and acceptance results.

For any length-$m$ word $s$, the clean-configuration identity `guessRunCfg_clean` says that the handoff configuration, after the block is replaced by $s$, is precisely the silent embedding of the verifier's initial configuration on tape $j_R$. The simulation theorem `embedSilentTM_runFrom` then identifies every subsequent run of the embedded verifier with the corresponding run of $R$. In particular, the verifier's bounded first verdict for each $s$ transfers to the embedded machine. This supplies the hypotheses for `guessRunTM_haltsWithin`, which gives halting for every choice word of the specified exact length.

For the acceptance equivalence at each $B$ above that bound, apply `guessRunTM_accepts_iff` to the same configuration and transferred verifier runs. Its two directions identify a guessed length-$m$ word and a first verdict of the verifier with the combined machine's halting, true-output outcome. The run-by-run identity from silent simulation transfers both the accepting state and the absence of earlier accepting or rejecting states between $R$ and its embedding. Hence the combined machine has such a word exactly when $R$ has a length-$m$ choice leading to a first acceptance.

**Key facts.** `Turing.guessRunCfg_clean`, `Turing.embedSilentTM_runFrom`, `Turing.guessRunTM_haltsWithin`, `Turing.guessRunTM_accepts_iff`.
