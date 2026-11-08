<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.obliviousSchedule_borrow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the borrow pass

**Claim.** Starting in borrow phase with carry $c$ and a word $bs$ of budget bits immediately to the right of the head, the machine processes those bits in $|bs|$ steps, updates the carry according to `budgetBorrow`, moves the head to the right end of the word, and leaves the rewritten bits in reverse order to the left, while preserving the other configuration data and tapes.

**Proof.** The transition lemma `obliviousSchedule_borrow` identifies each step on a tagged budget bit with a single-lane action: it writes the updated bit, moves right, and updates the carry. The general lane-run lemma (`lane_run`) iterates exactly such transitions across a finite list. Applied to the budget bits, it gives the final carry and rewritten list as computed by the fold of the per-bit update. The fold identity `budgetFold` identifies that result with `budgetBorrow`. The lane-run description also gives the head displacement by the word length, places the reversed rewritten bits to the left of the new head, preserves the right-hand list, and retains the original base configuration on all other components. This yields the asserted run equation.

**Key facts.** `Complexity.lane_run`, `Complexity.obliviousSchedule_borrow`, `Complexity.budgetFold`.
