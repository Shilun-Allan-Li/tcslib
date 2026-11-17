<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCopy_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing the Separator

**Claim.** Running the copier for two steps from state $0$, with the source head at $|w|$ and record $r$, reaches state $3$ with the input-head position unchanged, source head at $|w|-1$ (with truncated subtraction), source word $w$, and record $r$ followed by $0,1$.

**Proof.** First, the source tape is blank at cell $|w|$, since that cell lies just beyond the finite word $w$. Thus the copier’s transition from state $0$ takes its blank-cell branch. The one-step writing rule (`clCopy_write`) says this branch writes $0$ to the record, moves the source head one cell left, leaves the source word unchanged, and enters state $2$. Applying the same rule from state $2$, now with the source head at $|w|-1$, writes $1$ to the record, moves the source head by zero, and enters state $3$. The two successor-step identities and the zero-step identity for a run (`runFrom_succ_eq_step'`, `runFrom_zero`) identify these two transitions with the two steps of the run. The record concatenations combine to $r ++ [0,1]$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.clCopy_write`.
