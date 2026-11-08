<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_banks_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential Bank Cleanup

**Claim.** For every $j\le k$, the clean-call machine can clear the first $j$ banks and reach the cleaner-entry state for bank $j$ in at most $j(6T+8)$ steps.

**Proof.** Induct on $j$, retaining the bound for the accumulated run. When $j=0$, take zero steps: the initial frame is already the required frame, and the time bound is zero. For the successor case, write the induction hypothesis as a run of length $a$ that clears the first $j$ banks. The one-bank step lemma `emCall_bank_step`, applied to bank $j$, gives a run of length $b\le 6T+8$ from that frame to the frame with the first $j+1$ banks cleared. Concatenating the two runs yields a run of length $a+b$ (`MultiTapeTM.runFrom_add`). Since $a\le j(6T+8)$ and $b\le 6T+8$, this total is at most $(j+1)(6T+8)$, as required.

**Key facts.** `Turing.FinTM.emCall_bank_step`, `Turing.MultiTapeTM.runFrom_add`.
