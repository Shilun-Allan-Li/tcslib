<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_wordPatch_twice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated equal-length word patches

**Claim.** Patching a tape with $u$ and then with an equal-length word $v$ at the same base position yields exactly the tape obtained by patching the original tape with $v$ once.

**Proof.** Compare the two patched tapes at an arbitrary position $q$. The interval overwritten by the second patch is the same as the interval overwritten by the first, because the words have equal length. Inside that interval, the second patch supplies the buffer-tape content of $v$ in either expression. Outside it, the second patch leaves the tape unchanged, while the first patch also leaves the original content at $q$ unchanged. Thus the two tapes agree at every position.
