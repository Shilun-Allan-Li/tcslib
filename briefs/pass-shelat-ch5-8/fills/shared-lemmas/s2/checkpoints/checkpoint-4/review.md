# Internal source review of S2 checkpoint 4

Pinned exchange payload: `9b27244a5f583cde43040bfe6560cab7faf14436`.
Report SHA-256: `0674a5fd2e91a47fe0feabeb77ea9af5ef537da989315df37d509a3278470893`.
Two internal read-only reviewers: `/root/gate06_api_review` (H15 route/adapters) and
`/root/s2_workflow_review` (freeze/payload). Source-only review, 2026-11-07 PST.

## Checkpoint verdict

**0 blockers, 0 majors, 3 distinct minors.** This is not final acceptance, a native replay,
a seal pass, or external gate closure. The worker explicitly leaves milestone 5 pending.

1. **CP4-m1 — DiscreteLog sketch width.** Payload `DiscreteLog.lean:678` says the last
   `|t|` bits of the normalized word. It should say the last `|p|` bits. The implementation
   at lines 698–703 drops `|t|` leading bits from the zero-prefix/tail concatenation and
   correctly retains width `|p|`. Repair the prose only.
2. **CP4-m2 — stale H15 status.** Payload `Concrete.lean:85` still describes H15 as
   statement-only/an open fill. Refresh the module status to match the proof and keep final
   acceptance/landing status distinct from proof completion in the worker tree.
3. **CP4-m3 — abbreviated identity hashes.** Expand REPORT identity hashes from the worker's
   `git rev-parse`, including source checkpoint and exchange identities. Source identities
   obtained from patch headers alone are data, not independently verified local commit IDs.

## Independently checked source facts

- The three patches apply in memory to the five exact ancestor blobs at
  `31348fcf7dee32f84db1fc8f929d80653137995e` and reproduce all five submitted sources byte-for-byte.
  Their changed paths are exactly the owned files.
- No public addition/removal, header/hypothesis/visibility change, or public definition-body
  change was found. Exactly the six authorized public declaration docstrings are refreshed.
- All 64 copied private loop declarations disappear: DiscreteLog 15, ElGamal 15, RSA 18,
  Rabin 16. No retired loop names remain. There are 23 added private declarations, including
  Concrete's 15 implementation/leaf declarations.
- Owned admission tokens change 1 to 0; no new admit/axiom/sorryAx shortcut was found. The
  supplied 1,280 axiom records are standard-only; this is worker evidence, not an independent
  Lean axiom walk by either reviewer.
- H15 instances the existing repetition host with R=var and orbit bound 2n+4. The counter
  gates acceptance, preserving T=0, zero widths, B=0, k>B/overlap and truncated coins; `take`
  gives the unconditional tail-length bound. No strengthened public premise was found.
- Rabin's private overlong-fallback behavior change and strengthened private adapter premises
  are disclosed and within the brief's adapter allowance. Actual callers supply fallback
  lengths at most 3, bounded by max n 3; no public premise changes. RSA retains remainder
  normalization and fallback 1 % N.
- Source review found no concrete new foreign-definition read. It does not certify implicit
  read freedom; the final elaborated-term seals and both controls are still required.

Sizes reported/independently counted in the submitted sources: Concrete 935, DiscreteLog 1194,
ElGamal 2134, RSA 2412, Rabin 3553 lines. The brief's owned-file size exception remains in force.
Required checkpoint categories are present (REPORT, patches, all five sources, evidence).
Final Checks verification, ancestor axiom comparison, full headers, seals/controls and final
lints remain worker milestone 5, followed by maintainer final review and a user-merged PR.

**Not yet clear to merge — checkpoint only; three minor corrections and final evidence remain.**
