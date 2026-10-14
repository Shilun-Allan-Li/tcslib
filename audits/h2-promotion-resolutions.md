# H2-S statement gate: resolutions (round 1 → round 2)

**Gate:** `audits/h2-promotion-pack.md`; round-1 bundle `audits/h2-promotion-bundle.md`, SHA-256
`3b9b166e4b282a7c84026a92472dd7b868f6c19323390ae4aac1bcbbe6219bfc`, 28 sections.
**Findings:** `audits/h2-promotion-findings.md`, preserved verbatim: **gate open, 0 blockers,
3 majors, 5 minors, 7 notes.**
**Round 2:** `audits/h2-promotion-r2-pack.md`, with the revised design note
`audits/evidence/h2/r2/H2-design-r2.md` and the evidence in `audits/evidence/h2/r2/`.
**Base:** campaign commit **1781a230** (PR #84, fills-8), elaborated against its full olean
snapshot. Since round 1, fills-8 integrated the two B5a continuations into
`CodeSimulator.lean`; every round-2 check was rerun there (the round-1 move probe is stale for
24 proof bodies; §1.5 of the design note).

The auditor found no false copied contract and reproduced the fidelity and move checks. **The
seven copied contracts and their machines are unchanged in round 2** (code byte-identical to
round 1's draft, 58 of 58, `fidelity-r2-pass.log`). The repairs are in the additive results, the
design note, the scripts and the evidence.

## Findings

| # | Severity | Finding (short) | Resolution | Evidence |
|---|---|---|---|---|
| 1 | major | `roundTM_iterate` gives only `T ≤ t·B`; a stationary silent self-loop admits `T = 0`, so it does not supply U-1's divergence-preserving converse | **Repaired.** Restated with `∃ T, t ≤ T ∧ T ≤ t·B ∧ …` and **proved**: `0 ≤ 0` at `t = 0`; at `t + 1` the round time is positive (`roundTM_visited`'s `0 < T₁`, from `roundTM_effect`) and the inductive lower bound gives `t + 1 ≤ T₁ + T₂`. Its docstring states the cofinality argument (choose `t = u` for a horizon `u`). New additive **`roundTM_firstExit_unique`**: exactly one positive time is a first visit to `entry` or `halt`, so every witness of the contract is that time (the auditor's suggested uniqueness result; `Nat.find`/choice definitions are unambiguous). The reset/forward bridge (finding 4) is the named consumer obligation **CO-RF**, not an H2 theorem. The seven copied contracts are byte-identical. | Draft `StepBlockDraft-r2.lean.txt` (`roundTM_iterate`, `roundTM_firstExit_unique`); `elaboration.log`: draft 0 errors / 7 sorries; axiom probe: the two depend on `sorryAx` only through the main contract; **`MovePlusAdditive-r2`: both proved against the proved contract, standard triple**; `fidelity-r2-pass.log` (58/58 byte-identical to round 1). |
| 2 | major | H5 as "literal lockstep" does not fit a device whose virtual move costs several host steps | **Repaired** (design note §2.3a, O11). H5's requirement is a **positive, finite block simulation**: block length `1 ≤ L ≤ B_D` per live source step, intermediate frames, output (at most the one emission), exit cuts (no halt inside a live block), head envelopes; iterated, `t ≤ T ≤ S + B_D·t` (the pattern of `universal_block_run`). Literal lockstep is the special case `L = 1` (Z1, native). Resource guarantees are stated per consumer: `SU` needs the space ledger of the **ruler** device (`ℓ + 2` cells, `ℓ ≤ (2|α| + 6)·s`), by the user's 2026-10-13 decision to strengthen `space_universal` to `C·s` through the ruler device in the B6 hosts' gate and to state no binary-position device (`machine-library-design.md:3886`); C1 and U-1 need per-code time constants, U-1 also cofinality. The B6 draft's `exists_rulerHostTM` already fits as a checkpoint statement; recommended for the H5 gate: add `t ≤ t'` (or the one-block form). | Design note §2.3a; `audits/evidence/b6hosts/B6HostsDraft.lean.txt:1244`; `Build/VirtualInput.lean:188`, `:243`; `UniversalInterpreter.lean:859`. |
| 3 | major | Cited consumer sources missing; no import manifest; probe and replay conflated | **Repaired.** Bundled: `UniversalBlock.lean` (defines `universalBlockBound`, `:750`), `UniversalStartup.lean`, `ClassNP/TMSAT.lean`, the landed `Build/Contract.lean`, MIG-0b's draft (`RoundContract`), `Universal.lean`, `UniversalInterpreter.lean`, `NTimeHierarchy.lean`, the B6 host draft and note, `Configuration.lean`, `Deterministic.lean`, the facade. **Import manifest:** `importclosure.py` computes, from header `import` lines only, the reverse closure of `CodeSimulator` (6 modules) and of the proposed `StepBlock` under the proposed edges (7; the replay set is **8**, asserted), the forward closure of `StepBlock` (18 modules, without `CodeSimulator`, `CounterLoop`, `VirtualInput`), and the O3/O9 alternatives (24- and 224-module replays); the full graph is attached. The inventory is corrected (round 1's MIG-0a draft citation is replaced by the landed file). The probes run are listed separately from the H2-M replay still to come (design note §4.6). | `importclosure.out`, `import-graph.txt`; design note §§2.5, 3.3, 4.5, 4.6; `BUNDLE-FILES.txt`. |
| 4 | minor | Blanking the summary cell breaks `Rep` for the actual cumulative output; `roundTM_iterate` is about the silent block | **Recorded as CO-RF, in the auditor's form** (design note §2.3b): relate each reset seam to `{c with output := []}`; track the real output in the physical output or a buffer; prove reset/forward preservation, including the halting round (forward before the physical halt); transport the ledger. **Data-level steps checked**: blanking cell 0 gives `Rep tr {c with output := []} d'`; erasing the output keeps state and reads, and `a.apply {c with output := []} = {a.apply c with output := a.output.toList}`; the cell then holds the emission. To be added to `U₀`'s sketch and U-1's entry at H2-M. | `ResetProbe-tail.lean.txt` (three probe lemmas; 0 errors; standard axioms; not H2 surface), `elaboration.log`. |
| 5 | minor | O2's ownership list incomplete (import, summary-clock resolution, status text, H1 references) | **Repaired.** Declaration-based manifest `movemanifest.py`, computed **by name** and rerun at the integration base 1781a230: the 121 declarations (3 regions), the import, the **`section StepBlockClients` with `open StepBlock`** around the summary-clock family (text unchanged) and the 11 H1 clock declarations that fills-8 added (references renamed by the map: 35, all to public names), status text (9 lines), downstream files (none), layering (no moved code uses staying code). A single-file rehearsal of commit 1 elaborates (0 errors, the 2 headline sorries, 0 warnings). "Between continuations" is read as a coordinated window: H2-M lands after fills-8 and before the next B5a brief, never beneath an active H1 worker; a concurrent canonizer continuation only under a disjoint declaration carve-out. A negative control (a simulated next base) exits 1 with four failing checks. | `movemanifest.out`, `movemanifest-negctl.log`, `PostMove-CodeSimulator.lean.txt` and output; design note §4.3. |
| 6 | minor | `fidelity.py` exits 0 on mismatch, does not assert the inventory or whitelist additives | **Repaired.** `fidelity-r2.py`: exit 1 on any mismatch, kind change, missing, extra or duplicate declaration (draft or original), unexpected addition, or `sorry` outside the seven contracts (whose proofs must be exactly `by sorry`); asserts the full 58-name inventory and the 6-name whitelist; statements split let-aware. Passes on the round-2 draft (58/58); seven negative controls (the two round-1 mutations; a post-`let` statement mutation; missing; unexpected; duplicate; an admitted additive) each exit 1; the round-1 script exits 0 on three of them. | `fidelity-r2.py.txt`, `fidelity-r2-pass.log`, `negctl.py.txt`, `fidelity-r2-negctl.log`. |
| 7 | minor | No reason given for one ~3,350-line file against `policy.md` §1 | **Answered by layering and consumer reasons**, under the user's rule that size alone is never a reason to split (2026-10-11). No consumer imports the reader or skipper without the round; the parts share imports and form a chain no one imports partially; the replay set is unchanged; and a Record/Seek/Round split would have to publish or copy **19 declarations that round 2 keeps private** (MEASURED). Ruling: one module; resolution point: a consumer of the reader or skipper without the round, or a new layer (MIG-0b adapter, O8 sibling clause) imported separately. | `splitcost.py.txt`, `splitcost.out`; design note §6. |
| 8 | minor | Descriptive errors: table-dependent bound; `Key` 15/20; bytes vs characters; unqualified axiom claim; "three" vs four additives | **Corrected.** `roundTM_effect`'s docstring and the note: the bound depends on the table (indirectly on `k`, `n`, the actions), only `50` is uniform. `Key`'s docstring: 15 constructors, 20 values. Line length is counted in Unicode characters: the moved source had **83** lines over 100 (101 counted in bytes), round 1's renamed probe 75, both drafts 0 (MEASURED, reproducing the auditor); at 1781a230 the moved region has 14, and the module with the H2-M edits **0** (landing criterion, §4.4 of the note). The axiom claim is qualified: 10 of the draft's 64 declarations use `sorryAx`, the seven contracts and the three corollaries of the main contract. The additive section now says five (the sixth, `summaryEmit_none`, sits with the summary); six additives in all. Self-caught: round 1's rewrap put "class is irreversible." at the start of a docstring line, which the repository's style lint misreads as a declaration; rewrapped. | Draft docstrings; `linelen.out`; `elaboration.log`; `style-lint.out` (size line only). |

## Notes and rulings

- **NF1–NF7** (no findings): preserved. NF1's checks are rerun at 1781a230: the 121-declaration
  comparison with round 1's probe now shows exactly the 24 cleaned-up declarations changed (12 at
  the token level, all in proof bodies; 12 in whitespace or comments only); statements and
  definitions unchanged. NF6's verification against the missing Contract source is now possible
  (the landed `Build/Contract.lean` and MIG-0b's `RoundContract` are attached; design note §3.3).
  NF7's H2-M checks are scheduled (design note §4.6).
- **Consumer rulings.** H1/EXPCOM: as ruled, now demonstrated (fills-8's hosted clock consumes the
  contract unchanged). `U₀`: CO-RF, final-output forwarding before the halt, startup and host
  space composition: recorded. `SU`: the ruler block device. C1 and U-1: as ruled; O8 unresolved.
- **O1** resolved (backlog renamed). **O2** as finding 5. **O3, O9** counts now MEASURED (23 and
  223 reverse dependencies). **O4** unchanged. **O5** ruled: 15 helpers private, 56 public names,
  no contract changed (design note §4.2). **O6** included with finding 1's repair. **O7**: H1 now
  has a private `h1RoundTime`/`_spec` (by `Nat.find`); kept in `CodeSimulator` at H2-M, with a
  maintainer-owned dedup item to a public `StepBlock.roundTime` at MIG-0b's adapter (a dozen
  duplicated lines disclosed, ESTIMATE). **O8** recorded, no choice pre-approved. **O10**
  absorbed into commit 1 (§4.7 edits). **O11** as finding 2. **O12** qualified: the framed
  fixed-prefix read contract is the private `recordTM_read`; F7-1(c) stays open.
- **Suggested sanity results.** Cofinal iteration and first-exit uniqueness: proved (additives).
  Reset/forward bridge including a final emission: CO-RF, data-level steps probed, the rest the
  consumer's fill. Zero-tape/empty-input instance: proposed as an H2-M sanity example against the
  proved contract. C1's choice-lift action correspondence: C1's obligation.
- **Attestations.** Round 1's "maintainer's independent second elaboration" had no separate
  transcript: round 2 attaches every transcript it cites (`elaboration.log`, the probe outputs).

## The integration base and the H1 escalation (new since round 1)

- **Fills-8 (1781a230).** H1's cleanup rewrote 24 step-block proof bodies (no statement; 67 → 1
  linter warnings; 83 → 14 over-width lines); H1's 11-declaration hosted clock cites the
  contract; the canonizer's parse front end touches no moved declaration. The move manifest, the
  rehearsal and every elaboration were recomputed there.
- **H1's rule-11 escalation** (14 over-width lines in frozen signatures and definition bodies;
  the unused binder `hr` in `h1Seek_stateStep`'s statement): **handled in the H2-M move.**
  Whitespace re-wrapping of the 14 lines that exceed 100 characters after renaming (a different
  set from H1's 14: renaming fixes six and creates six), and `hr` → `_hr`. Neither changes any
  statement or definition up to α-equivalence: every edited declaration is token-identical to the
  unedited one (up to the binder name), and a probe checks the 11 edited statements equal to the
  unedited ones by `with_reducible rfl`; dropping the binder instead (`ite` for `dite`) fails that
  check (negative control). Recommended: `_hr`, not dropping. Design note §4.7;
  `AlphaProbe-tail.lean.txt`, `AlphaNeg-tail.lean.txt`, their outputs.
