# C1 fill plan: the NTIME hierarchy (maintainer draft, 2026-10-17)

**Where C1 stands** (at #118's round-3 head `531b98a2`):
- **The design** is `C1-design.md`, with all five recommendations answered (user, 2026-10-13).
- **The statements are landed:**
  - the five host contracts (PR #87, gate `audits/c1-hosts-statements-*`);
  - the guess-then-run assembly in `Build/NDHost` (gate `audits/c1-assembly-statements-*`);
  - H1's hosted counter loop (`Build/StepBlockLoop`, PR #94).
- **Every shared host the design waited on is proved:**
  - the step clock `exists_stepClockTMVia` (B6-F1, PR #103), which is design §5's "H3-clock";
  - H2's loop form (`Build/StepBlockLoop`);
  - H2-F (`Build/StepBlockForward`).

  No C1 stub waits on another campaign's host any more.

## The stubs: 11 sorried declarations in 6 files

| # | Stub | File:line | Kind | Cites (all gated statements) | Size (design §5; ESTIMATE) |
|---|---|---|---|---|---|
| W | `ndWriterTM_run_block` | `Build/NDHost:213` | a leaf, the worker's own machine | — | 150–400 |
| WC | `exists_inputWindowCopyTM` | `Build/InputWindow:82` | a device | the counter-loop calculus | 400–900 |
| E | `FinNDTM.exists_exhaustiveDecider` | `ClassNP/ExhaustiveReplay:65` | a host | the step clock, the replay lemma | 1,200–2,500 |
| R | `exists_ndInterpreterCore` | `NDCodeSimulator:145` | a host | H2's loop, Z1, RC and WC's statements, input locality | 1,500–3,000 |
| RC | `exists_replayCanonizer` | `NDCodeSimulator:94` | a code transducer | the bridge `CodeNDTM.serialize_eq_tableBitsK` (proved), the scheme's canonizer | 450–1,000 |
| UN | `exists_timed_universal_NDTM` | `Diagonalization/NTimeHierarchy:164` | the assembly | `guessRunTM`'s lemmas (proved modulo W), R, WC, `expandTM`, `skipBackTM` | 500–1,000 |
| BF | `exists_ndAcceptsWithin_decider` | `NTimeHierarchy:195` | a corollary | `ndAcceptsWithin_decider_of_universal` (proved) applied to UN and E | a few lines |
| NF | `FinNDTM.exists_codeNDTM_accepts_linear` | `NTimeHierarchy:238` | a construction (guess, then verify) | W's statement, the ND transfer, `relabelState` | 2,500–5,000 |
| H | `ntime_hierarchy` | `NTimeHierarchy:345` | the summit | UN, BF, NF, the step clock, and **C1-E's new pieces, not yet stated** (the locator, the ladder rows, the materialization writer, the diagonalizer `D`'s assembly) | 4,000–8,000 |
| H′ | `ntime_hierarchy_of_pos` | `NTimeHierarchy:359` | a corollary of H | `NTIME.mono` | about 30 |
| S | `NTIME_linear_ssubset_square` | `NTimeHierarchy:382` | the showcase | H′; `TimeConstructible (n + 1)` and `((n + 1)²)`, both instances of the proved `timeConstructible_poly` (`ClassNP/TMSAT`, at `C = 1` and `c = 0`, `1`; one authorized import) | about 50 (the design's 500–1,200 assumed new witnesses) |

**The one hard constraint:** one worker per file. `NTimeHierarchy` holds six of the eleven stubs, and
`NDCodeSimulator` holds two.

## Proposed order

- **First, the ND inventory API PR** (`lean/nd-api`, `audits/evidence/nd-api/`): 41 equations for the
  nondeterministic model. Under the "Everything" rule it lands before any C1 brief is dispatched.
- **Wave 1: five briefs in five files, all citing only gated statements:**
  - W (NDHost);
  - WC (InputWindow);
  - E (ExhaustiveReplay);
  - R (NDCodeSimulator, proved modulo RC's statement);
  - UN with the file's three small corollaries (NTimeHierarchy): BF (a citation of UN and E), H′ and
    S (both proved modulo H). UN is proved modulo W, WC and R.
- **Wave 2:**
  - RC, after R integrates (the same file);
  - NF, at the home decided below (in place, it waits for the UN brief to integrate).

  S needs no new statement: its two witnesses are `timeConstructible_poly`'s instances.
- **C1-E, the diagonalizer,** in parallel with wave 1: a statement phase (the maintainer's draft), then
  its statement gate, then the fills. **This is the longest chain** (4–8k lines), and none of it is
  stated yet, so its statement phase should start now.

## Open questions for the user

1. **The ND API PR:** push `lean/nd-api` (stacked on #118) as its own PR, with its own replay
   (102 modules) and gate? *Recommended:* every API PR gets its own gate.
2. **Wave 1's size:** all five briefs, or fewer? The six #118 briefs will be out at the same time.
   *Recommended:* all five. They are in distinct files and cite only gated statements.
3. **NF's home:**
   - **(a) In place in `NTimeHierarchy`:** it waits for the UN brief to integrate. After that it holds
     the file for 2.5–5k lines of work, so C1-E's fill of H must wait for it.
   - **(b) A new module** (say `ClassNP/NDNormalForm.lean`) with the gated statement verbatim under
     its own name, and `NTimeHierarchy`'s theorem as a one-line citation (one added import). That
     takes a small statement gate for the moved statement.

   *Recommended:* (b), for the parallelism (two workers cannot share a file), not for size. NF can then
   join wave 1.
4. **C1-E's statement phase now?** *Recommended:* yes, as maintainer drafting alongside wave 1.

**Answered (user, 2026-10-17): all four as recommended.**
1. The ND API is its own PR, #119, with its own replay and gate.
2. Wave 1 is all five briefs.
3. NF goes to a new module.
4. C1-E's statement phase starts now.

## The inventory

The seed-inclusive inventory and its judgements are in `audits/evidence/nd-api/NOTES.md`. Each brief's
own route inventory, crossed with its unfolding sites, runs when the brief is drafted.

## NF's writer (user, 2026-10-17)

NF guesses its display records with the writer's controller-stopped flavor, which has no contract,
and `ndWriterTM` is `Build/NDHost`'s. **Ruling: a public controller contract.** After W integrates, a
small statement PR states the controller flavor's contract in `Build/NDHost`, with its gate. A W
continuation fills it, and NF's brief cites it modulo. NF issues in wave 2.
