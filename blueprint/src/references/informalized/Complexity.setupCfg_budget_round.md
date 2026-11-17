<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_budget_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Budget Round

**Claim.** A budget-start configuration completes one round in $2|w|+(a+1)+4$ steps, appending $a+1$ unary markers and performing the borrow pass, with the phase determined by whether the pass ends with a carry.

**Proof.** Split the prescribed duration into the initial rewind, the marker-appending scan, and the borrow scan with its final transition. `setupCfg_budget_start` accounts for the first $|w|+2$ steps, returning the budget head to cell $1$ in append phase. `setupCfg_append` then accounts for $a+2$ steps: it appends $a+1$ unary markers and reaches borrow phase with the unary head advanced by that amount. `setupCfg_borrow` processes the $|w|$ bits, implementing the borrow pass and restoring the budget head to its starting position; the tape length is preserved by `budgetBorrow_length`. One further step is described by `setupCfg_borrow_end`: it enters unary-start if a carry remains and budget-start otherwise. The run composition law `runFrom_add` combines these successive runs, and the stated total follows by adding their lengths.

**Key facts.** `Complexity.setupCfg_budget_start`, `Complexity.setupCfg_append`, `Complexity.setupCfg_borrow`, `Complexity.budgetBorrow_length`, `Complexity.setupCfg_borrow_end`, `Turing.MultiTapeTM.runFrom_add`.
