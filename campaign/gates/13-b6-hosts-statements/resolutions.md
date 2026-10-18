# B6 hosts statement gate: resolutions

**Gate:** `audits/b6-hosts-statements-pack.md`; bundle `audits/b6-hosts-statements-bundle.md`, SHA-256
`692e5822fa6b66693710c4226c1071f0c1bde3b97d6df3bfbf13cddf0b9e641e`, 70 sections.
**Findings:** `audits/b6-hosts-statements-findings.md`, verbatim.
**Verdict: PASS, CLOSED in round 1 (2026-10-14): 0 blockers, 0 majors, 5 minors.** The ten admitted
contracts are attainable as stated; the strengthened `space_universal`, the homes, the two moves
to `WindowClock`, and `exists_codeTM`'s derivation are approved. No minor is waived; the Lean
fixes travel with the landing PR.

| # | Finding (short) | Resolution |
|---|---|---|
| 1 | "Proof of Theorem 4.8" is too specific an attribution | **At landing:** cite [AB09, Theorem 4.8] with Exercise 4.1 and, where relevant, Claim 4.4, and call the detailed construction the repository's refinement; keep Exercise 4.1, p. 93 for `space_universal`. |
| 2 | `exists_rulerHostTM`'s prose promises an injection; the contract gives a map | **At landing:** "state map" in the prose. Injectivity, if a consumer needs it, is a separate gated addition. |
| 3 | `exists_windowLoopTM`'s sketch assumes positive first-exit times the record rows do not export | **At landing:** the sketch derives positivity for the halted-state test or inserts one stationary anchor step per round, absorbed into `C`; no statement changes. |
| 4 | `freeze.py` prints `RESULT: PASS` despite a public removal | Recorded: the landing freeze uses the maintainer's `declfreeze.py`, whose public-removed list is checked by hand; the evidence script is not an acceptance gate. A future gate script fails on unauthorized removals. |
| 5 | `WindowClock` and `SelfUniversal` omit `## Main definitions` | **At landing:** add the heading ("none: the module uses existing definitions"). |

**Rulings recorded:** the step clock keeps `+2` (no weakening to `+3`); the runner stays
clock-agnostic (Route A if the shared clock is filled first, else Route B); `∃` statements now,
`U₀` by `Classical.choose`; `Contract` adapters after MIG-0b; the ruler call rows stay gated with
the host; no time clause on `U₀`; no intermediate input-head envelope for B6 (P6).
