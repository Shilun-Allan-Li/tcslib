<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_patch_twice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idempotence of Counter Patching

**Claim.** Patching a tape with $u$ and then with an equal-length word $v$ at the same position gives the same tape as patching directly with $v$.

**Proof.** Compare the resulting tapes at an arbitrary position. The two patch intervals coincide because $u$ and $v$ have equal lengths. Inside that interval, both constructions return the buffered value from $v$; outside it, the second patch leaves the first patched tape unchanged, which is the original tape there. Hence the tapes agree everywhere.
