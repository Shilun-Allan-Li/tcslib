<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.flipOutput_outputWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output under Flipped Transitions

**Claim.** On input $x$ under choices $w$, the output of the machine obtained by flipping $N$'s output is the word obtained by negating each bit of $N$'s output.

**Proof.** The flipped machine's initial configuration is the output-flipped version of the original initial configuration (`Turing.NDTM.flipOutput_initCfg`). The run correspondence (`Turing.NDTM.flipOutput_runWith`) says that after the same choices $w$, its configuration is the output-flipped version of the original final configuration. By definition, flipping a configuration applies Boolean negation pointwise to its output word. Reading the output component therefore gives the stated equality.

**Key facts.** `Turing.NDTM.flipOutput_initCfg`, `Turing.NDTM.flipOutput_runWith`.
