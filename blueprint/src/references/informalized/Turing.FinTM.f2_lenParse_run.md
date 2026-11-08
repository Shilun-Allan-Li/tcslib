<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_lenParse_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Pair Parsing and Length Check

**Claim.** Starting in the pair-reading state at the beginning of a suffix, the augmented machine halts within the stated bound and outputs the bit indicating whether pair decoding succeeds with second component of length at most $r$.

**Proof.** Proceed by induction on the suffix, splitting it into blocks of two symbols when possible. For the empty suffix, one transition observes the end of input, emits false, and halts; the input-symbol calculation identifies the end marker correctly (`f2_lenCfg_read`). For a singleton suffix, the first-bit step records its bit, and the next step sees the end marker and halts with false; this agrees with pair decoding on a one-symbol word (`f2_lenParse_first`, `f2_lenCfg_read`). For a suffix beginning with $b,d$, use the two-step block analysis (`f2_lenParse_block`). If $b=d$, the machine returns to the pair-reading state after the pair, and the induction hypothesis applies to the remaining suffix. If $(b,d)=(0,1)$, it enters state $3$ after the pair, and the suffix-length check supplies halting and the correct Boolean output (`f2_lenSuffix_run`). If $(b,d)=(1,0)$, it halts immediately with false, exactly as the decoder's failure case prescribes. The equal-bit case's output agrees with recursively decoding the remaining suffix, since equal bits prepend the same bit to the first decoded component and leave the second component unchanged. The run-length bounds add the two steps for a pair to the bound for the remaining suffix; the immediate-halting cases satisfy the bound directly. Runs split into an initial segment and a continuation by the iteration law (`runFrom_add`), and zero- and one-step runs are identified with the starting configuration and one transition (`runFrom_zero`, `runFrom_succ_eq_step`).

**Key facts.** `Turing.FinTM.f2_lenCfg_read`, `Turing.FinTM.f2_lenParse_block`, `Turing.FinTM.f2_lenParse_first`, `Turing.FinTM.f2_lenSuffix_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
