<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_fuel_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Tape Setup

**Claim.** Starting in phase $0$ with an empty counter tape, payload $w$, counter head at zero, and payload head at $|w|$, the host reaches phase $4$ after $3|w|+4$ steps, with $w$ on the counter tape, the payload blank, and both heads at zero.

**Proof.** First, the phase-$0$ transition moves the counter head left and enters phase $1$, placing it at $-1$. Split the remaining time into three blocks of $|w|+1$ steps. In the first block, the rewind lemma moves the payload head from $|w|$ to zero, entering phase $2$. The copy lemma then processes the payload in the second block: it transfers each symbol to the counter tape, leaving the payload blank and both heads at the right end, and enters phase $3$. The return lemma uses the third block to move the two heads back to zero and enters phase $4$. The run-addition law composes these successive runs, and arithmetic gives $1+3(|w|+1)=3|w|+4$. The initial copy-tape identity says that copying from an empty prefix starts with exactly the buffer tape for $w$ (`f2_loopCopy_initial`).

**Key facts.** `Turing.FinTM.f2_loopControl_apply`, `Turing.FinTM.f2_loopHost_fuel_rewind`, `Turing.FinTM.f2_loopHost_fuel_copy`, `Turing.FinTM.f2_loopCopy_initial`, `Turing.FinTM.f2_loopHost_fuel_return`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_add`.
