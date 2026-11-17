<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitRestore_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Cleanup Run

**Claim.** The cleanup machine started in its scan configuration at count $0$ reaches the specified configuration in state $(4,\mathrm{false})$ by some time $t\le 2|s|+|w|+5$.

**Proof.** First, the updated word has length at least $|s|$: the cleanup step either appends one symbol or leaves $s$ unchanged. The machine scans for $|s|$ steps to reach count $|s|$ (`splitRestore_scan`); one further transition enters state $(1,\mathrm{false})$, updates the first tape to the desired word, and leaves the input head at the scan position with the work heads at displacement $|s|-1$ (`splitRestore_append`). The rewind result (`splitRestore_rewind`) then takes $|s|+1$ steps to reach state $(2,\mathrm{false})$ with the same tape contents and all work heads at zero. From there, the machine moves left into state $(3,\mathrm{false})$ and scans left until it reaches the input boundary, then moves right into state $(4,\mathrm{false})$; the bounded return-time result `catalogRewind` guarantees this segment takes $r\le \mathrm{pos}+2$ steps, where $\mathrm{pos}$ is the current input-head position. Here that position is at most $|w|+1$ (`splitPos`), so $r\le |w|+3$. Concatenating these run segments gives a total time $(|s|+1)+(|s|+1)+r\le 2|s|+|w|+5$. At the end the input head is at position $1$ and all work heads are at zero; the tapes and output match the specified word configuration by extensional equality of configurations.

**Key facts.** `Turing.FinTM.catalogRewind`, `Turing.FinTM.splitRestore_append`, `Turing.FinTM.splitRestore_scan`, `Turing.FinTM.splitRestore_rewind`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`.
