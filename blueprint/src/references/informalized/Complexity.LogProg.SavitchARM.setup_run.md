<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup.lean :: Complexity.LogProg.SavitchARM.setup_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Savitch Procedure Setup Run

**Claim.** Under the correct input-length oracle hypothesis, $1\le E$, and the stated bound on $B$, the procedure has a guarded finite run from its zeroed scan state to the outer-search state with radius $(|x|+2)^E$, width $(|x|+2)^{2E}$, and code bound $2^{(|x|+2)^{2E}}$.

**Proof.** Write $a=|x|+2$, $s=a^E$, and $w=a^{2E}$. First, $a\le s$ because $E\ge1$, and hence $s\le w$. Also $s^2=w$. The elementary estimate $w<2^w$ and the assumed $2^w\le B$ provide the bounds needed for the setup computations.

1. The input-length counting loop, using the oracle hypothesis at each queried counter, increments the length register to $|x|$. A register move transfers that value to the base register, after which two increments make it $a=|x|+2$.
2. The loading loop sets the exponent counter to $E$ and the power accumulator to one. The power loop then computes $a^E=s$. Copying this value to the radius register and squaring it produces $s^2=w$; moving the result into the width register gives the required width. The multiplication, copy, and move routines ensure the scratch registers are returned to the values needed by the next stage, while the bounds above keep the registers within $B$.
3. Finally, copying the width to the shift counter and shifting the initially unit code-bound register computes $K=2^w$. The shift routine clears its counter on exit. The resulting state is exactly the specified outer-search state, and concatenating these guarded runs yields the claimed reachability.

**Key facts.** `Complexity.LogProg.inputLength_loop`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.SavitchARM.ld_run`, `Complexity.LogProg.SavitchARM.pw_run`, `Complexity.LogProg.SavitchARM.cp_run`, `Complexity.LogProg.SavitchARM.mul_run`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.SavitchARM.cp_run`, `Complexity.LogProg.SavitchARM.sh_run`.
