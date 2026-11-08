<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.oblAction_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Budget Tape Action

**Claim.** The specified schedule action equals the action that performs the same write-and-move instruction on the designated budget tape, leaving the other tapes unchanged and entering state $q$.

**Proof.** Both actions have stationary input head, no output, and successor state $q$, so it suffices to compare their work-tape instructions at each index. The index type is the sum of the original $k$ tape indices and the three administrative indices. For an original tape index, the schedule action assigns no write and no movement. This index cannot equal the designated budget tape, which lies among the three administrative tapes, so the lane action also leaves it unchanged. For an administrative index $j$, if $j=0$, it is precisely the budget tape: both actions assign the write instruction $b$ and movement $d$. If $j\ne0$, it is one of the other two administrative tapes. It cannot coincide with the budget index, so both actions assign no write and no movement there. Thus the actions agree on every tape and in all other components, hence are equal.
