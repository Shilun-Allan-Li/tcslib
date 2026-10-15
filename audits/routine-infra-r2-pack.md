# External audit pack — machine-routine layer (§12), round 2 (re-audit of the round-1 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), the §12
routine-layer statement gate, round 2. Round 1
(`audits/routine-infra-findings.md`, attached verbatim) returned
**0 blockers, 4 majors, 3 minors, 3 notes**; per `workflow.md` §3 the gate
did not close. This round audits the repairs. The gate closes on zero
blockers and zero majors.

Audited at commit `9a92fa1a` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/routine-infra-r2-repairs.diff`): **nine new sorried
statements and three new definitions** — the two returning embeddings with
their four contracts (R1), the three general-configuration seam theorems
(R2), the release adapter with its two contracts (R3) — plus the
witness-honest `pairMapSnd` sketch (R4), the three minor sketch repairs
(R5-R7), the R8/R9/R10 wording and scope notes, one new import
(`StateRenaming`, for `Cfg.mapState`), and the design document's §12.5
record. **No pre-existing statement changed**; the inventory grows from 47
to **56 sorried statements** (Embed 13, Seam 11, Catalog 32).

## Brief for the auditor

You have the round-1 report. For each finding, the table below states the
repair and where it lives; the complete change is the attached diff. Your
deliverables:

1. **Audit the nine new statements as fresh statement-phase surface** —
   blind restatements of `Turing.embedSilentRetTM`/`embedEmitRetTM`,
   `Turing.seamReleaseTM`, and the exact content of the six run/first-return
   contracts and three visited-set contracts; true-as-stated arguments; your
   round-1 counterexample traces replayed against them (the one-state
   halting emitter through `embedSilentRetTM_run` at `T = 1` — your S8; the
   two-step write-and-return call through `seamReleaseTM_firstReturn` —
   your S7; the head-at-`7`/nonempty-output seam through
   `seamCompTM_run_ofCfg` — your S9).
2. For **R4** and the minors **R5-R7**: verify the repaired sketches match
   your proposed fixes (the forwarding controller with coefficient `1` on
   `Sg`; the `C = 0`/`e = 0` splits; the exact `[-1, d]` and `2p + 2`
   counts) or say why a deviation is inadequate.
3. Report anything the repairs broke or newly misstate — in particular the
   `S ⊕ Unit`/`Unit ⊕ S` state plumbing, the `Cfg.mapState` seams, the
   through-halt handover configuration (`state := some (Sum.inr ())` over
   the transported halt), and whether the general seam theorems really
   derive their canonical instances — in the same findings-table format and
   severity scale as round 1.

Sources and conventions as in round 1 (the frozen `Build/` context files are
re-attached; `[Bon26]` citations unchanged).

## Scope

| Item | Where |
|---|---|
| Under audit | the attached diff: `Build/Embed.lean` (design paragraph, the two returning transformers, four new contracts, the capture-specialization wording), `Build/Seam.lean` (the chaining qualification, three general-configuration theorems, the release adapter and its two contracts), `Build/Catalog.lean` (the `pairMapSnd`, `polyBits`, `compare`, `increment`, `stripLast` sketch repairs and the R10 scope note), `machine-library-design.md` §12.5 |
| Unchanged, re-attached | every pre-existing §12 statement (byte-identity checkable in the diff), the frozen `Build/{Convention,Wrappers,Loop,Primitives}.lean`, and the newly imported `StateRenaming.lean` (`Cfg.mapState`'s home) |
| Declared, out of scope | the same commit range also contains the concurrent P4.3/P3.3/P3.2 repair commits (disjoint files; their own rounds) and the four returned findings files. Also out of scope: tactic proofs; round-1 items the auditor marked as not requiring change |

## Per-finding disposition (verify each)

| # | Round-1 finding | Repair |
|---|---|---|
| R1 | **major** — the closed embeddings cannot express the halt-to-live return; the final emission is lost to the halt or to premature dispatch | `Turing.embedSilentRetTM`/`embedEmitRetTM` on states `S ⊕ Unit`: live states run the shared core; a source action with successor `none` executes **in full** — tape effects and the final emission included — and lands in the live anchor `Sum.inr ()`, which idles stationarily until a seam consumes it. Contracts: `Sum.inl`-lockstep through live times, the handover configuration at the first source halt (`{ transported halt with state := some (Sum.inr ()) }`, residue and frame preserved), first-visit exactly there, and visited-set **equality** with the closed flavors at every time. Your trace's `c₁` now carries the emission *and* a live state |
| R2 | **major** — the seam theorems are canonical-only; arbitrary frames and output-carrying seams cannot be certified | `Turing.seamCompTM_run_ofCfg` + `_firstReturn_ofCfg` + `_visitedByTapeHead_ofCfg`: phase two starts from phase one's returned configuration with **only the control state replaced** (`Cfg.mapState (fun _ => entry)`), so displaced inactive heads, noncanonical contents, the input position, and accumulated output cross the one stationary, silent, write-free dispatch step intact. The canonical theorems are declared instances; your head-at-`7` and `[true]`-output seams are now expressible |
| R3 | **major** — the first-return cut excludes positive entry-equals-exit calls | `Turing.seamReleaseTM` on `Unit ⊕ S`: the fresh start executes the anchor's action **unconditionally**, control then lives in the `Sum.inr` copy, so the first re-arrival at `Sum.inr anchor` is a positive-time event with the transported cut (`seamReleaseTM_firstReturn`, time zero excluded by constructor disjointness); visited sets equal the source's. A seam then consumes `Sum.inr anchor` as its left exit |
| R4 | **major** — `pairMapSnd`'s documented witness is refuted (the capture tape visits `\|g b\| + 1` cells) | The sketch now **commissions a forwarding controller** and says so: validate/buffer the pair, emit the encoded first component, simulate the payload on the buffered second component **forwarding its output** (the E2 discipline — emissions never touch a work bank), coefficient `1` on `Sg` plus linear administration; the captured-payload machine is explicitly disclaimed as a witness. Statement unchanged, per your assessment that the existential is true |
| R5 | minor — `polyBits` at `C = 0` | The sketch splits: constant-output witness for `C = 0` and for `e = 0`; the buffered unary route only for `C > 0, e > 0`, where `n + 1 ≤ C(n+1)^e` |
| R6 | minor — compare's `[-1, min + 1]` interval argument | Replaced by your exact-position argument: turn at `d` (first mismatch or first word end, `d ≤ min`), trajectories exactly `[-1, d]`, `d + 2 ≤ min + 2` cells, uniformly over equal words, unequal lengths, and aliased indices |
| R7 | minor — increment's mixed count | Exactly `2p + 2 ≤ 2\|w i\|` (`p` carries, one turn, `p` rewinds, one entry), visited `[-1, p]`, `p + 1` never visited on success, `[false]` in two steps; the public `2\|w i\| + 2` declared slack |
| R8 | note — `stripLast` "replays" description | The sketch now describes the quadratic time contract as deliberate slack over the construction's linear-derived bound, with the guard and raw banks each linear |
| R9 | note — tape selection is not zone multiplexing | The Embed opening now states the scope precisely: whole distinct physical tapes, coordinates intact; the Hennie-Stearns/universal consumers' zone and virtual-input layers are separate, named work |
| R10 | note — loop sibling contracts not exported | The L-row carries the scope note: `exists_loopTM` only; same-witness conjunctions for `exists_loopCfgTM`/`exists_loopFindTM` are a recorded future addition, commissioned on consumer need |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/routine-infra-r2-sweep.log`, revision
  recorded at start: `9a92fa1a`): the three modules, 0 `error:` lines, fresh
  `.olean`s, exactly **56** `declaration uses 'sorry'` warnings
  (Embed 13, Seam 11, Catalog 32).
* Style lint (`audits/logs/ch34-r2-repairs-stylelint.log`, the combined
  repair-round log): `TuringMachine` tree 0 FAIL with 9 size WARNs — the 8
  pre-existing plus `Catalog.lean` now at 1012 lines, justified by the
  already-queued per-theme split (backlog §2, decision 12.2 option (c);
  recorded in the decision log with this pack's row); the other campaign
  trees 0 FAIL / 0 WARN.
* Statement-freeze baseline: commit `9a92fa1a`.
* The new-declaration inventory: 3 definitions (`embedSilentRetTM`,
  `embedEmitRetTM`, `seamReleaseTM`), 9 sorried contracts, 1 new import
  (`StateRenaming`), counted programmatically against the sweep log.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/routine-infra-r2-findings.md`; the gate closes on zero blockers and
majors.
