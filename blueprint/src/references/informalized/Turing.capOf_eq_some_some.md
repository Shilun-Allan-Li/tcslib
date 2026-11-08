<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.capOf_eq_some_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Characterization of the Cap

**Claim.** The cap of a Boolean word is the nested optional value containing a Boolean exactly when the word is the singleton consisting of that Boolean.

**Proof.** Split the word into the cases of length zero, one, or at least two. The empty word has empty cap, and a word of length at least two has the cap marker for that case; neither is a nested optional containing a Boolean. For a singleton word $[a]$, the cap is precisely the nested optional containing $a$, so it equals the nested optional containing $v$ exactly when $a=v$, which is equivalent to the word being $[v]$.
