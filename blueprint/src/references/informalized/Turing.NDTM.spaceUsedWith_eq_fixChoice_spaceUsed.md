<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean :: Turing.NDTM.spaceUsedWith_eq_fixChoice_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Under a Fixed Choice

**Claim.** Under the stated transition-agreement hypothesis along the fixed-choice run, the space used by the run under the finite choice word equals the space used during the corresponding number of steps of the machine with that choice fixed.

**Proof.** Fix a work tape and a prefix length $j$ between $0$ and $|w|$. The hypothesis says that, at every earlier time $j'<|w|$, the two transitions agree whenever the fixed-choice run is in a state. The run comparison theorem (`runWith_eq_fixChoice_runFrom`) therefore identifies the configuration reached under the first $j$ choices of $w$ with the configuration reached after $j$ steps of the machine whose choice is fixed to $b$. The hypothesis applies to the word $w.take\ j$, since each of its prefix times is less than $|w|$. In particular, the two configurations have the same work-tape head position at time $j$. This holds for every $j\le |w|$, so the sets of positions visited on the chosen tape—the images of these prefix times—are equal. Their cardinalities are equal as well. Summing over all work tapes gives the claimed equality of total space usage.

**Key facts.** `Turing.NDTM.runWith_eq_fixChoice_runFrom`.
