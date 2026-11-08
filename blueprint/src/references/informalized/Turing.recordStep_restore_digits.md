<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_restore_digits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorded Digit Restoration

**Claim.** The complementing phase restores the width-$W$ binary representation of $p$ in the auxiliary tape within $4W+6$ steps, without reaching either verdict state and while keeping every work head within distance $W+1$ of its initial position.

**Proof.** Put $e(b)=\mathrm{digit}(b)$, let $F$ be the width-$W$ all-ones word, and let $R$ be the counter word obtained by decrementing $F$ exactly $q+1$ times. Its length is $W$ (`counterWord_length`). Since the value of $F$ is $2^W-1$, the complement of $R$ has binary value $q+1$ (`recordStep_complement_value`, `recordStep_saved_digits`); thus complementing the auxiliary word produces the width-$W$ representation of $q+1$. The scan that complements tape 3 takes $2W+2$ steps, reaches its done phase without reaching a verdict, and moves heads by at most $W+1$ (`recordStep_map_snapshot`). The phase-transition analysis then sends a right native move directly to restoration, while a non-right move first decrements the complemented digits. In the latter case, the fixed-width decrement changes the representation of $q+1$ to that of $q$ (`recordStep_digits_succ`), takes at most $2W+2$ further steps, and preserves the head bound (`recordStep_arithmetic_transport`). In either branch the controller enters restoration with the required digits; adding the phase-transition steps gives the claimed time bound. The phase-run results ensure neither verdict is reached early, and their head bounds give the stated bound throughout.

**Key facts.** `Turing.counterWord_length`, `Turing.recordStep_complement_value`, `Turing.recordStep_saved_digits`, `Turing.recordStep_map_snapshot`, `Turing.recordStep_digits_succ`, `Turing.recordStep_arithmetic_transport`, `Turing.recordStep_phase_run`.
