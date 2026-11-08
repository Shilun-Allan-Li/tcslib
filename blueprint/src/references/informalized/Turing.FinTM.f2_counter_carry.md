<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_carry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Carry Run

**Claim.** For input $x$, input-head position $p$, Boolean list $b$, and prefix $u$, starting the counter machine in state $1$ with head position $|u|$, tape for $u$ followed by $b$, and empty output, after $c(b)+1$ steps it is in state $2$, with input-head position $p$, work-head position $|u|+c(b)-1$, tape for $u$ followed by the increment of $b$, and empty output; here $c(b)$ is the number of leading true entries of $b$.

**Proof.** Induct on $b$. If $b$ is empty, one application of the transition rule ends the carry phase and writes a true bit, exactly the increment of the empty list; the head moves left once and the machine enters state $2$. If the first bit is false, the transition rule likewise ends the carry phase immediately, writes true at that position, and moves the head left. This is the incremented list, and the carry count is zero. If the first bit is true, one step changes it to false, keeps the machine in state $1$, and moves the head right. Apply the induction hypothesis to the tail with the prefix extended by this false bit. That run consumes the tail's carry count plus one steps; together with the initial step this is the required total, and the resulting tape is the increment of the original list. The head displacement is the initial move right followed by the induction displacement, giving $|u|+c(b)-1$.

**Key facts.** `Turing.FinTM.f2_counter_carry_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
