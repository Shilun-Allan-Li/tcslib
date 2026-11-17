<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPoly_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setup Rewind

**Claim.** Starting in setup state with every work head at $j-1$ and empty output, after $j+1$ steps the machine reaches the outermost loop state with every head at zero and output still empty.

**Proof.** Induct on $j$. At zero, every head is at $-1$, so the setup transition sees a blank on the first work tape, moves all heads right, and enters the outermost loop state; this puts every head at zero. For the successor step, every head is at position $j$, where a unary mark is present because $j<q$. The setup transition moves all heads left and remains in setup, producing the configuration with heads at $j-1$. Apply the induction hypothesis to the remaining steps. The transitions neither write nor emit output, so the output stays empty. Run decomposition separates the first transition from the remaining run (`runFrom_succ_eq_step`, `runFrom_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
