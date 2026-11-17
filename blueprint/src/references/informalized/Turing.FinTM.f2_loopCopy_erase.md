<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopCopy_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Copied Tape Symbol

**Claim.** Erasing cell $|p|$ from $T(p,b::r)$ gives exactly $T(p++[b],r)$.

**Proof.** Compare the two tapes at an arbitrary cell $z$. If $z=|p|$, the update sets that cell to blank. The right-hand tape is also blank there, because its prefix has length $|p|+1$. Otherwise the update leaves the left-hand tape unchanged. Since appending the singleton $[b]$ increases the prefix length by one, the conditions that $z$ lies before the old prefix and before the new prefix are equivalent for all such $z$. Beyond those prefixes, both definitions read from the same word: associativity gives $p++(b::r)=(p++[b])++r$. Hence the tapes agree at every cell.
