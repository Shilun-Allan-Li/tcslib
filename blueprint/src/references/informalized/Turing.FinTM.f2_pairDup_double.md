<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_pairDup_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Duplication Run Invariant

**Claim.** For every $j\le |x|$, after $2j$ steps the machine is in its scanning state at input-head position $j+1$, and its output consists of the first $j$ bits of $x$, each doubled.

**Proof.** Proceed by induction on $j$. At $j=0$, the initial configuration has scanning state $0$, head position $1$, and empty output, which is precisely the asserted configuration. For the successor step, apply the induction hypothesis at $j$. The scan configuration reads the $j$th input bit (`Turing.FinTM.f2_scanCfg_read`). The machine first advances to its intermediate state and emits that bit, then advances again and emits the same bit while returning to the scanning state. The head moves right on both steps; the right-move formula applies because the head is not at the right boundary (`Turing.moveInputPos_pos_of_ne_right`). The output is therefore the previous doubled prefix followed by two copies of the next bit, which is the doubled prefix of length $j+1$. Since the machine has zero work tapes, state, head position, and output determine the configuration (`Turing.Cfg.ext_zero_tapes`). The two successor-run identities express these transitions as the claimed run of $2(j+1)$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step'`).

**Key facts.** `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.f2_scanCfg_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_pos_of_ne_right`.
