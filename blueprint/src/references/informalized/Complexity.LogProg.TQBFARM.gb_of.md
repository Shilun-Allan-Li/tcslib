<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.gb_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bounds Imply the Configuration Guard

**Claim.** If all seven registers of a state are at most $B$, then for any input and instruction label the configuration with those register values and no answer satisfies the machine’s preconditions and register bound.

**Proof.** The guard has two parts. The precondition part holds for every configuration of this machine, by the unconditional precondition lemma (\texttt{preS_A}). For the register-bound part, the state’s coordinatewise bounds transfer to its register vector (\texttt{St.Bd.toV}). Together these establish the guard.

**Key facts.** `Complexity.LogProg.TQBFARM.preS_A`, `Complexity.LogProg.TQBFARM.St.Bd.toV`.
