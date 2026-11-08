<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean :: Complexity.LogProg.runFrom_count_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Count Bound

**Claim.** Under the stated transition, halting, and head-position bounds, the configuration at the displayed configuration-count time equals the configuration at time $T$.

**Proof.** Let $T_0$ be the first time at which the run is halted. Then $T_0\le T$, the machine is not halted at any earlier time, and once halted its configuration remains fixed. We bound the number of possible codes for configurations at times before $T_0$, and show that distinct such times must have distinct codes.

For the last tape, the transition restriction and the lemma on its run (`last_tape_run`) show that each cell is either blank or contains $1$, and that a cell containing $1$ stays that way. Any nonblank cell must have been visited by the tape head (`mem_visited_of_ne_none`); therefore the assumed head bounds imply that all nonblank cells lie in the bounded ranges $[-B,B]$ on the first $K$ tapes and $[-P,P]$ on the last tape.

At each time, record the state, input-head position, the contents of the first $K$ tapes in their bounded windows, and the bounded position codes of all work-tape heads. For the last tape, record the set of positions in $[-P,P]$ containing $1$, represented by its cardinality. The first $K$ tape contents and their head positions are determined by these records: positions outside the bounded windows are blank, and the head-position codes determine the actual head positions (`posCode_injOn`). For the last tape, monotonicity of the set of positions containing $1$ makes the sets at two ordered times nested. If their cardinalities agree, the sets agree; cells outside the bounded range are blank. Since every cell is blank or contains $1$, the entire last-tape contents then agree. Thus equality of codes at two times implies equality of the machine cores.

But two different times strictly before $T_0$ cannot have the same core: the configuration-count injectivity result (`core_injOn`) rules this out for a run whose first halted time is $T_0$. Hence the code is injective on the times before $T_0$. Counting its possible values gives the displayed bound: there are $|S|+1$ choices for the state including the halted state, $|x|+2$ input-head positions, $3^{K(2B+1)}$ choices for the first-tape contents, $(2B+1)^K$ choices for their head positions, and $(2P+1)(2P+2)$ choices for the last-tape head code and the recorded cardinality. Therefore $T_0$ is at most the stated product.

The displayed time is consequently at least $T_0$. Both that run and the run at time $T$ agree with the configuration at $T_0$, because a halted configuration remains unchanged. The run-composition law (`runFrom_add`) expresses each later run as a continuation from time $T_0$, and the halting invariance lemma (`runFrom_of_halt`) makes each continuation constant. This proves the claimed equality.

**Key facts.** `Complexity.LogProg.last_tape_run`, `Turing.MultiTapeTM.mem_visited_of_ne_none`, `Turing.MultiTapeTM.ConfigCount.posCode_injOn`, `Turing.MultiTapeTM.ConfigCount.core_injOn`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
