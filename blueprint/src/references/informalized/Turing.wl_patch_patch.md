<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wl_patch_patch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idempotence of an Equal-Length Tape Patch

**Claim.** If two joined field words have equal length, patching a configuration with the first fields and state, then with the second fields and state, gives the same configuration as applying only the second patch to the original configuration.

**Proof.** Compare the configuration components. The second patch sets the state to $q'$ and leaves the input-head position, work-head positions, and output unchanged, so these agree with a single patch by the second fields. For the work tapes, compare each tape and integer position. The second patch overwrites tape zero on the interval from its original head position up to, but excluding, that position plus the joined-word length of the second fields. By the equal-length hypothesis this interval is exactly the interval overwritten by the first patch. Thus, wherever the second patch writes, its value is determined solely by the second fields and agrees with the single-patch construction; outside that interval, the second patch retains the underlying tape value, and the first patch has made no change there either. Hence every component agrees.
