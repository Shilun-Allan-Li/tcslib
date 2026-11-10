# PRF-based private-key encryption relocation

Seyoon merged #272 at `84bddbcaa87454bcc832c912791380e183613661`. Its Lean and checker inputs match the verified
PRG encryption head `73d000bfa590f98169f22a1e3bf64b88ebe64d5c`.

[PR #273](https://github.com/Shilun-Allan-Li/tcslib/pull/273) at `7e508a4501cfe078a48d84b444abc50443a08443` moves the scheme, correctness and fixed-vector
security proofs, and existence results to `Encryption.PrivateKey.FromPRF`.
`Hybrid` owns the finite six-hybrid bound, `HybridLemmas` owns the collision
and coin-relabelling estimates, and `ReductionMachine` owns the next-query
machine, its string encoding and run agreement. Both legacy
`Asymptotic.MultiMessage*` imports re-export their prior interfaces. The
private-key and pseudorandomness maps point to the new owners.

The sampler equation `prfEncReal_apply` and oracle evaluation equation
`eval_multiMsgAdv` let the asymptotic proofs read the hybrid through the new
boundary. The first two local compile attempts exposed imports that the old
PRF facade supplied indirectly. The final modules import the probability
lemmas and Boolean-ring instance from their providers.

- All 13 affected modules pass, including the root and campaign Checks.
  The replay verifies 1,094 retained local objects and 3,810 external objects.
- The census matches all 157 relocated declaration types, definition values
  and axiom sets, with seven private kernel name changes. The only proof
  reference changes are in the two proofs using the published equations.
  The generated `prfAdv.congr_simp` matches its prior type and dependencies.
  Both compatibility imports and the standalone probes pass.
- The two baseline and four new whole-file seals pass. The fixed-length
  wrapper passes the focused seal on both revisions with the same 47
  definitions and matchers. The controls block direct sampler reduction and
  accept both equations. The explicit and generated scans report zero
  foreign reads in the edited owners.
- Source lint and the diff check pass. The sampler equation clears one
  reader warning and 21 reader warnings carry forward. The five existing
  direct-import flags in the pseudorandomness map refer to modules reachable
  through `Pseudorandom.Functions` on both revisions.

The cleanup ledger was checked against the relocated definition providers.
[Ledger comparison](READS.json)

`private-key-from-prf-checks.zip` has SHA-256 `6b6187e3f836fd33315292c0394fb34069627f486e1fceb8f0114d82d5a0e64a`.
[Verification hashes](VERIFICATION.json)

Seyoon merged #273 at `36f5adb8f92d7496c9c3455ce1815f390fa13d47`. The Lean sources and checker inputs match the verified head.
