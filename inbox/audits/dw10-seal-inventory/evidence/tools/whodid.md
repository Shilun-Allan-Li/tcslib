- **Lead (Claude, cloud):** everything at this checkpoint: preflight, toolchain, cache, bootstrap and tree map, the collectors and
  owner check, the item location, the scan, the seal generation, the seal runs (one process, then the parallel pool of four
  workers after the user's override), the controls, the reader index, the reconciliation and this report.
- **Sub-agents:** none has run yet. Lean is no longer the bottleneck since the parallelism ruling, so sub-agents are planned only
  for the classification review of the open items (A: SecureComputation, ZeroKnowledge; B: Encryption, Authentication, Games,
  Hashing, Randomness, Implications, Pseudorandom), analysis-only, with their logs under `evidence/subagents/<name>/`.
