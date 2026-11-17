<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_wordPatch_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A word patch preserves an agreeing tape

**Claim.** If a tape already agrees with a word $u$ at every offset from $-1$ through $|u|$, patching that tape with $u$ at the same base position leaves the entire tape unchanged.

**Proof.** Compare the patched tape with the original at an arbitrary position $q$. If $q$ lies in the interval overwritten by the patch, put $p=q-c_p$. The interval bounds imply $-1\le p\le |u|$, so the agreement hypothesis identifies the original tape content at $q=c_p+p$ with the buffer-tape content of $u$ at $p$. This is exactly what the patch writes. If $q$ lies outside the interval, the patch definition leaves its content unchanged. Hence the two tape functions agree everywhere.
