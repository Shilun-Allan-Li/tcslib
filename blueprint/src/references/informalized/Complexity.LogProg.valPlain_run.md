<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.valPlain_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Plain-input validation run

**Claim.** Under the specified transitions and no-call conditions, the machine accepts the run precisely when the input is a valid plain encoding: valid inputs reach the next state at position $1$, while invalid inputs halt with a rejecting output, preserving the indicated register-head positions and avoiding call states before the endpoint.

**Proof.** Let $t$ be the length of the initial run of ones. The bound $t\le |x|$ (`tRun_le`) allows the machine to scan these bits. Alternate the states $vU0,vU1$ according to the parity of the number of bits read. Each scanned bit is $1$ (`getElem?_lt_tRun`), so the prescribed transitions advance the input head without changing the register-head positions. The scan lemma (`scanR`) gives the resulting run and its intermediate-state invariant; its final state is determined by the parity of $t$.

Use the characterization of valid plain words (`validPlain_iff`) to check the remaining format. If the input ends at $t$, has a noninitial bit equal to $1$ there, or $t$ is odd, the characterization rules out validity and the indicated transition rejects. If the prefix has even length and the bit at $t$ is false, the machine enters the separator-check state. It rejects if the next bit is absent or false. If that bit is true, it enters the word-scanning state at position $3+t$.

Write $w=x.drop(t+2)$. The drop-length relation and the symbol-alignment calculation identify the input symbols encountered by the scan with the bits of $w`. The state after each scanned bit records its value; applying `scanR` again shows that the machine reaches the appropriate final scanning state while traversing $w$. At the right boundary, the state machine rejects exactly when the last bit of $w$ is false. By `canon_iff`, that is precisely when $w$ is not canonical. Thus this branch rejects exactly for invalid encodings; otherwise it enters the rewind states. The rewind lemma (`rewind_x`) shows that these states return the input head to position $1$ and reach `next`. Throughout, `rrun_add` joins the scan and continuation runs, and the intermediate-state witnesses from the scan and rewind establish the no-call and register-position requirements. The input-boundary step and position changes follow from `inSym_succ`, `rrun_one_x`, `apply_xAct`, and `moveInputPos_pos_val`; rejecting terminal steps are justified by `rrun_one_rej`.

**Key facts.** `Complexity.LogProg.tRun_le`, `Complexity.LogProg.scanR`, `Complexity.LogProg.getElem?_lt_tRun`, `Complexity.LogProg.validPlain_iff`, `Complexity.LogProg.inSym_succ`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.moveInputPos_pos_val`, `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.rrun_one_rej`, `Complexity.LogProg.rewind_x`, `Complexity.LogProg.rrun_add`, `Complexity.LogProg.getElem?_tRun`, `Complexity.LogProg.canon_iff`.
