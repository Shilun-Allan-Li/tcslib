# GSW phase-6b fills (U12–U19) and EF-R1: staged Claude fill briefs

Records only, prepared 2026-11-18 at records tip `9b92d4ff2f2a5e63f1d2aeffbda696f4b837fa45` (branch
`cryptography/pass-shelat-ch2-4`), statically: git objects, `python3 -I`, grep. No Lean was run, nothing was committed
or pushed by the preparer. Inputs: plan section r3 §H7 (units U12–U19), the 6b rulings (Q-6B-W1–W3, F1, F2, Q-6B-1,
Q-C1, P6-Q10), Gate 46 (CLEAR, LE-g46, LE-g46b), the 2026-11-18 decision-log rows, efficiency audit r1 and rulings
r1 (Q2 A: EF-R1; P6-Q10 superseded), standing rules 15 and 16. Route: Claude for fills (standing ruling); delivery to
`inbox/fills/<unit>/` on `exchange/pass-shelat-ch5-8`; rules and checks in [COMMON.md](COMMON.md); the
pre-dispatch duplication sweep in [dup-sweep.md](dup-sweep.md) (binding must-reuse lists).

## Units

The 24 admitted targets of #377 (merged at `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`; [targets.txt](targets.txt))
in five proof units, plus EF-R1. Plan units sharing a fact are merged so that the fact is stated once (Q-6BF-2,
Q-6BF-3); every unit owns its files exclusively.

| Unit (folder) | Plan units | Owned files (`GSW/` = `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/`) | Targets | Size (fill lines) | Base | Workers | `sorryAx` allowed through |
|---|---|---|---|---|---|---|---|
| `gsw-6b-u12` ([U12](U12/brief.md)) | U12 | `GSW/Branching.lean` | G1–G3 (3) | 150–250 | B6 | 1 | none |
| `gsw-6b-u13` ([U13](U13/brief.md)) | U13 | `GSW/DecryptFormula.lean` | G5–G8 (6) | 200–330 | B6 | 1 | none |
| `gsw-6b-u14-u16` ([U14-U16](U14-U16/brief.md)) | U14, U16 | `GSW/Bootstrap.lean`, `GSW/Leveled.lean`; public helper `encrypts_bootGate` | G9, G10, G18, G12, G13, L2, L3 (7) | 460–740 + 40–80 | B6 | lead + 1 | U12's G3, U13's G7/G8 |
| `gsw-6b-u15-u17` ([U15-U17](U15-U17/brief.md)) | U15, U17 | `GSW/Circular.lean`, `GSW/LeveledSecurity.lean` | G15, L4, L5 (3) | 290–490 | B6 | lead + 1 | none |
| `gsw-6b-u18-u19` ([U18-U19](U18-U19/brief.md)) | U18, U19 | `GSW/PolyRatio.lean`, `GSW/Asymptotic.lean`; public helper `Parameters.ofFamily_columns_le` | G16, G17 ×2, A1, A3 (5) | 290–500 + 10–20 | B6 | lead + 1 | U14-U16's G12, G13, L3; U15-U17's L5 (A1: none) |
| `ef-r1-gsw-reductions` ([EF-R1](EF-R1/brief.md)) | EF-R1 (audit §5.1) | new `GSW/EncryptPoly.lean`, `GSW/ReductionMachines.lean`; facade `GSW.lean` (2 lines) | proves `ReductionEfficient F`, `LeveledReductionEfficient F L` for every `F`; wrappers `indCPA_of_dlwe`, `leveledINDCPA_of_dlwe` | 700–1,200 (new) | EF1 (stacked) | lead + 2 | predicates: none; wrappers: A1/A3 only |

**Totals.** 24 targets; 1,390–2,310 fill lines for the GSW units (r3 §H7's U12–U19 sum exactly) plus about 60–100 for
the two helpers; EF-R1 700–1,200 new lines (±40%); about 2.1–3.6k in all.

**Bases.** B6 = `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (tree `845bdc982fd8f79aba755796bb13188922c4655d`): the #377
merge itself, no synthetic merge needed; its Lean equals the records tip's and is olean snapshot #11 (adopted
2026-11-18 from `olean-replay-6b-stmt-g46b`; workers bootstrap their own trees). One shared build
order for all five GSW units: [order.txt](order.txt) (224 modules), [roots.txt](roots.txt) (102 Mathlib roots),
[closures.txt](closures.txt) (CHANGED, DOWN, INFO-DELTA, per-unit UNIT-DOWN), [base-sorries.txt](base-sorries.txt)
(42 declarations in 16 modules: the 24 targets and 18 older admissions), [SOURCE-SHA256SUMS](SOURCE-SHA256SUMS); made
by [tools/](tools/) from git objects (`graph.py` agrees with the records: 1,456 reachable modules, 216 admissions).
**EF1 is a stacked base** (it needs `NUPPT.RealizesOn` from `iO/phase-a-base` and EF-R2-R3's toolkit): see
[EF-R1/base.md](EF-R1/base.md), status **PENDING**.

## Where EF-R1 sits (Q-6BF-1, recommended A: its own unit)

- **It proves, it does not restate.** EF-R1 proves the two predicates as theorems for every family; A1/A3 keep their
  `heff` statements (ruling Q2 A) and become unconditional through two new one-line wrappers. Nothing in
  `GSW/Asymptotic.lean` changes, so U18-U19 can fill A1/A3 from `heff` now, in parallel.
- **Different base and tooling.** EF-R1 needs `Asymptotic/Realization` (#380, unmerged, on `iO/phase-a-base`) and the
  general-modulus arithmetic EF-R2-R3 is writing now (`Encoding/ModularArithmetic.lean`): a GSW ciphertext column is
  `[A | b]ᵀ R_{·,j} + μ G_{·,j}`, Regev's subset sum plus a constant. Writing that arithmetic again in EF-R1 would
  duplicate EF-R2-R3's series 1 (a major). Putting EF-R1 inside U18-U19 would hold A1/A3's analytic fill hostage to
  EF-R2-R3 and the iO PRs.
- **File size.** `Asymptotic.lean` (340 lines) plus U19's 150–280 plus 700–1,200 would pass the 1,000-line limit.
- **Route found by the sweep** (EF-R1 brief): the reductions' own coins — including the leveled seeds, which hold
  uniform residues and `χ`-seeds — are fixed by averaging (`CommitmentLemmas.exists_fixCoins`) into advice, the worst
  index is chosen by advice, and the realiser runs `D` on a polynomial-time splice of the challenge into the advice.
  No sampler is needed, so the predicates hold for **every** `LWE.Family` with no `EfficientFamily` and no `χ`
  hypothesis: R50/R51 move from class G to M once EF-R1 lands, and A1/A3's wrappers are unconditional once U18-U19
  lands as well.

## Parallelism

- **Now, in parallel (5 workers):** U12, U13, U14-U16, U15-U17, U18-U19. Under the proved-modulo rule every unit cites
  other units' targets as frozen statements, so none waits for another; C5's allowed traces say which `sorryAx`
  each may carry meanwhile.
- **EF-R1 after** EF-R2-R3's series 1 is accepted (its checkpoint 1 contains it) and `EF-R1/base.md` is filled
  (Q-6BF-4). Including U18-U19's accepted final in EF1 is optional (it lets EF-R1 use `ofFamily_columns_le`).
- **Lean processes.** Cloud workers recommended for all six units (a memory-sized pool each; COMMON §3). On a local
  host the cap is 3 Lean processes per machine across all jobs, and S2-A and wave-1 workers may already hold slots;
  each of these units would bootstrap 224 modules, so a local host fits at most one of them at a time.
- **Landing order** (maintainer; each unit lands as its own PR or two, per file): U12, U13, U15-U17 first (their
  targets end sorry-free), then U14-U16, then U18-U19, then EF-R1 after #374, #378, #380, #384 and EF-R2-R3's PR (or
  stacked). A fill gate (Codex) follows the GSW units, the number assigned when staged. After all five, the 6b modules
  hold 0 admissions and the base order's count falls from 42 to 18.

## Disjointness (checked mechanically, `sweep/`)

- **Cleanup Stage 2.** None of the eight GSW files, `GSW.lean` or EF-R1's two new files is an owner path of
  `scope.tsv` or `s2a-items.tsv` (204 paths) or changed on `cleanup/stage2-s2a` (local head `fc676daa…` when read,
  moving; origin `c119a3c4f1d8642b1328740f1d1d1165a92f5567`). EF-R1 imports `ZeroKnowledge/CommitmentLemmas.lean`,
  a J6 owner, read-only (Q-6BF-7): proof-level Stage 2 rows on other declarations, `exists_fixCoins` untouched.
- **Each other, #376/#377, wave 1.** The units' files are pairwise disjoint; #376/#377 are merged; wave 1's files
  (EF-R2-R3's six, the other jobs' new files) are disjoint from all of these.
- **Arora–Barak and Ladner.** 251 paths on `complexity/arora-barak-*` and `codex/ab34-*`, none under
  `TCSlib/Cryptography/`; 26 are in this folder's import closure (replay risk only; nothing here edits them).

## Questions for Seyoon (recommended option first)

- **Q-6BF-1 · EF-R1's placement.** **A** its own unit `ef-r1-gsw-reductions` with new files, dispatched when its base
  exists (above) · B inside U18-U19 (the owner of `Asymptotic.lean`): one owner for A1/A3 and their wrappers, but the
  file would pass 1,000 lines, and U19 would wait for EF-R2-R3 and the iO PRs.
- **Q-6BF-2 · Grouping.** **A** five GSW units as above: U14 with U16 (shared gate step), U15 with U17 (same transport
  technique; U15 is 60–120 lines), U18 with U19 (shared family bound) · B the plan's eight per-file units, with U16
  dispatched after U14 and U19 after U18 so the earlier unit publishes the shared helper · C one job for all 24 targets
  with a lead and three sub-agents (the 6a precedent): one bootstrap, but one long critical path.
- **Q-6BF-3 · Public helpers.** **A** allow exactly the two named public glue lemmas, `encrypts_bootGate`
  (`Bootstrap.lean`) and `Parameters.ofFamily_columns_le` (`PolyRatio.lean`), pure insertions, decls2 ADDED = 1 each,
  sealed with their own controls · B none: each file proves its copy privately and the maintainer records the pairs
  in the duplication ledger (not recommended: G44-01, disclosure is not acceptance).
- **Q-6BF-4 · EF-R1's base.** **A** a deterministic local merge (`tools/mkbase-ef-r1.sh`) of B6 with EF-R2-R3's
  maintainer-accepted head (checkpoint 1 or final, whichever is accepted first with series 1 frozen), plus U18-U19's
  accepted final if available; EF-R1 lands stacked · B wait until EF-R2-R3, #374, #378, #380 and #384 merge, base =
  the records tip then · C dispatch now on B6 ⊕ `iO/phase-a-base` and let EF-R1 write its own mod-`q` maps (not
  recommended: duplicates EF-R2-R3 series 1, a major).
- **Q-6BF-5 · EF-R1's names.** **A** `reductionEfficient`, `leveledReductionEfficient`, `indCPA_of_dlwe`,
  `leveledINDCPA_of_dlwe` (the string maps `encryptStr`, `spliceStr` in `GSW/EncryptPoly.lean`) · B the worker
  chooses, disclosed.
- **Q-6BF-6 · EF-R1's coins.** **A** fix all of each reduction's own coins by averaging into advice; `D'`'s coins are
  `D`'s; no sampler anywhere · B keep the binary `R` as `D'`'s own coins (closer to [GSW13]'s reduction, more coin
  bookkeeping), averaging only the leveled seeds.
- **Q-6BF-7 · `exists_fixCoins`.** **A** import `ZeroKnowledge/CommitmentLemmas.lean` read-only now, and record a
  promotion request to move the averaging pair (`exists_abs_uexp_le`, `exists_fixCoins`) to `Foundations/` after
  Stage 2's J6 · B a scope request to promote it first (waits for J6).

## Blocking

1. **The records pin.** This folder is committed in progress by the coordinator; `<RECORDS>` (the prompts' only
   placeholder) is the hash of the commit that files its final form with `rulings.md`.
2. **Rulings.** U12, U13 depend on none of the questions; U14-U16 and U18-U19 on Q-6BF-2 and Q-6BF-3; U15-U17 on
   Q-6BF-2; EF-R1 on Q-6BF-1 and Q-6BF-4 to Q-6BF-7.
3. **EF-R1 only:** EF-R2-R3's series 1 accepted and `EF-R1/base.md` READY.
4. **Local inputs (rule 16): none for any unit.** All sources are ingested; nothing is needed from Seyoon's machine.

## Maintainer steps before dispatch

1. Record Seyoon's answers in `rulings.md` in this folder (even "all as recommended"); adjust a prompt only where a
   dispatch file's header says how for a non-recommended option.
2. Re-check COMMON §1's input hashes at the commit about to become the pin (the handoff and plan move often); update
   the table if one changed, then regenerate `SHA256SUMS` (`sha256sum` of every file in the folder except itself).
3. Commit and push the records; `<RECORDS>` is that commit's full hash. Seyoon dispatches U12–U19 with the five
   prompts.
4. EF-R1, later: when EF-R2-R3's series 1 is accepted, run `tools/mkbase-ef-r1.sh`, fill `EF-R1/base.md` (READY,
   the toolkit names), regenerate `SHA256SUMS`, commit; that commit is EF-R1's `<RECORDS>`.

**Ready to dispatch (U12, U13) once `<RECORDS>` is filled; U14-U16, U15-U17, U18-U19 once Q-6BF-2/Q-6BF-3 are ruled;
Not yet ready to dispatch — EF-R1: its stacked base (EF-R2-R3's toolkit) does not exist yet.**
