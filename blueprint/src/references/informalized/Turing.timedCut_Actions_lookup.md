<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_Actions_lookup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action Lookup by Read Offset

**Claim.** For a machine in code normal form, the nine transition actions listed for a state have length nine, and the entry indexed by the ordered pair of reads is the transition action for those reads.

**Proof.** The action list is formed by taking the three possible input reads in order and, for each, listing the three possible work-tape reads in order. Thus it has $3\cdot 3=9$ entries. The index is three times the index of the input read plus the index of the work-tape read, which is precisely the position of that pair in this nested listing. Checking the three possibilities for each read—blank, $0$, and $1$—shows that the selected entry is the transition action for that pair.
