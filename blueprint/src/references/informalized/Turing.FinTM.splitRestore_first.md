<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitRestore_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Entry into the Return State

**Claim.** There is a positive time no greater than $2|s|+|w|+5$ when the cleanup machine first reaches state $(4,\mathrm{false})$, in the specified configuration containing the updated first work tape, blank remaining work tapes, and empty output.

**Proof.** The complete-run result `splitRestore_run` supplies a time $T\le 2|s|+|w|+5$ at which the machine reaches the stated configuration. In any configuration with state $(4,\mathrm{false})$, the transition is a stationary control action: it leaves the input head fixed, does not alter work tapes or work-head positions, emits no output, and keeps the same state. Thus the configuration remains fixed after reaching it. The first-entry principle for a state with this fixed-point property (`catalogFirstEntry`) therefore gives a time $t\le T$ at which the machine reaches that destination and has not had state $(4,\mathrm{false})$ at any earlier time. It remains to show $t>0$. If $t=0$, the first-entry configuration equals the initial scan configuration, so their states would agree; the scan starts in a state whose first coordinate is $0$, whereas the destination has first coordinate $4$. This is impossible. Hence $0<t\le T$, giving the claimed bound and first-entry property.

**Key facts.** `Turing.FinTM.splitRestore_run`, `Turing.FinTM.catalogFirstEntry`.
