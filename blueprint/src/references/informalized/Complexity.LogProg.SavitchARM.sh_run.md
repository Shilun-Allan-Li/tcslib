<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.sh_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift-loop Reachability

**Claim.** If the registers are bounded by $B$, the scratch register is zero, and the acted-on register times $2^C$ is at most $B$, then the phase-zero shift routine reaches its exit with the acted-on register multiplied by $2^C$ and the counter cleared, maintaining the guard before the final configuration.

**Proof.** For the selected shift site, the loop first counts the counter $C$ down to zero. At each iteration it tests the site register: if positive, it decrements that register and increments the scratch register twice; these paired operations preserve the quantity represented by the site register together with the accumulated doubled count. Once the site register reaches zero, the routine transfers the accumulated value back by incrementing the site register and decrementing the scratch register until the scratch register is zero. This implements multiplication of the original site value by $2^C$. The assumed product bound ensures the increasing register never exceeds $B$, and the other registers remain bounded; the general shift-loop theorem supplies the guarded finite run. The required register distinctions for applying that theorem follow from the three shift-site cases.

**Key facts.** `Complexity.LogProg.SavitchARM.sh_ne`, `Complexity.LogProg.SavitchARM.St.Bd.toV`, `Complexity.LogProg.shl_run`.
