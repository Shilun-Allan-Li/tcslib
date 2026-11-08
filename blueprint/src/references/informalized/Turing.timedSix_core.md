<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedSix_core -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Core Lanes of the Six-Lane Assembly

**Claim.** For a type $A$, a function $a$ assigning values in $A$ to the four core indices, and $b,c\in A$, the six-lane assembly evaluated at the six-lane index corresponding to any core index $i$ equals $a(i)$.

**Proof.** There are four possible core indices. For each, its embedding into the six lanes by appending two unused indices selects, respectively, one of the first four branches in the definition of the assembly. That branch returns the value of $a$ at the original index, so the claimed equality holds in every case.
