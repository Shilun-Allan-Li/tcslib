**Not yet clear to merge: #251.**

Gate 129 first return HOLD at `2e2f415c9bbf654cd8a68bb02aa62ea291d91116` (0 blockers, 3 majors, 2 minors,
8 notes). The first repaired candidate was pushed at `31aecdf5e5d6a7d9fe0adf06406a7f37d3e62e88`; the
full opacity check found two further mechanical initialization reads in the
incrementer. Final scope checks and a fresh merged-tree replay from the adopted
#252 snapshot are required before the Codex follow-up can be dispatched.
