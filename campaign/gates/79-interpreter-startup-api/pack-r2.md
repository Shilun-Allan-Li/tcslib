# External audit pack — the interpreter startup (PR #169, A+, an API gate), round 2

**Round 1** (`findings.md`; resolutions `resolutions.md`): FAIL, 0 blockers, 1 major, 2 minors, 8
notes. Round 1 proposed no change to `Turing.exists_interpreterStartup` or to the re-pointed core.
- **The major:** the B5a consumer probe at `p = 0` was vacuous. B5a's hosted verdict loop needs
  its `F.k` work tapes blank, which `p = 0` does not give.
- **The minors:** the core's Implementation paragraph overstated the heads at `0`; the bundle
  lacked the core seal's source and five screen-population files.

**The user ruled (2026-10-26):**
- re-scope the consumer claim, with a non-vacuous probe at the right `p`, and record B5a's
  route;
- fix both minors.

**The head:** `lean/interpreter-startup` at `df992ad77aa5b6de6c53d5fda02702e724e13d43`. Since round
1's head `4bee8b09` it has one docstring-only commit, `df992ad7`
(`evidence/round2/df992ad7-docstring.patch`). Its Lean diff from the campaign branch is still
`Build/InterpreterStartup` and `NDCodeSimulator`. This bundle's Lean files are from `df992ad7`, and
its records from the records commit that the dispatch prompt names.

## Brief for the auditor

1. **The major.**
   - **The tape map** (the design note's "As built"; `resolutions.md`, finding 1): B5a's loop
     `h1HostedVerdictTM F.k` runs on `1 + (F.k + 2 + 1)` tapes. The startup's roles supply its
     buffer (`jwin`), counter (`jctr`), table (`jtbl`) and summary (`jsm`). Its `F.k` mirrored
     work tapes are the startup's `p = F.k` passive tapes, started blank.
   - **The probe** (`evidence/round2/B5aConsumerProbe2.lean.txt`, `b5aP_startup`): the startup at
     `p = F.k`, from all-blank tapes, with B5a's installer. It keeps the roles, the ten separation
     facts, the first-arrival cut and every threshold field, and adds that the reserved tapes
     come out blank at head `0`.

   Is the probe non-vacuous now, and is the map consistent with `h1HostedVerdict_effect`'s
   statement (`CodeSimulator`, in the bundle)? The junction itself (the embedded threshold as the
   loop's `vhostCfg` start, with the `Rep`) needs `CodeSimulator`'s private lemmas, so it is
   recorded for B5a's pre-ship, before B5a issues. Is that a sound place for it? Is anything
   missing from the startup's interface for this route?
2. **Minor 2.** Is `df992ad7`'s paragraph an exact reading of the startup's threshold clauses? Is
   the commit docstring-only? Do the design note's departures match the built statement?
3. **Minor 3.** The bundle now carries:
   - the core seal's exact sources, round 1's and the head's;
   - their recipe, `mksealcat.py.txt` with `c2seal-block.lean.txt`;
   - all 18 population files, `ClassNP/ExhaustiveReplay` among them.

   Does the recipe reproduce the sources? Can you now complete the semantic-duplication check
   against `ExhaustiveReplay`'s `xr_` idioms and the other hazards?
4. **No regression.** The elaboration recipe at `df992ad7` against `oleans-la1m` (the tree after
   #164) gives the kit and the core with no diagnostic, both on the standard three axioms, and
   `NTimeHierarchy` with only `ntime_hierarchy`'s sorry. The core seal at `df992ad7` gives no
   body error. Is anything else changed?
5. **Round 1's other points.** Is anything in round 1's resolutions unaddressed?

## Repository-side attestations (verify or challenge)

- **Elaboration and the core seal** (`evidence/round2/`, recipes `check.sh.txt` and
  `mksealcat.py.txt`): as in item 4. The core seal's 50 controls (`evidence/core/C2Ctl*`) are
  separate files, unchanged since round 1.
- **The probe:** `B5aConsumerProbe2.out`, 0 errors; `b5aP_startup` on
  `[propext, Classical.choice, Quot.sound]`.
- **Freeze:** `df992ad7` changes only `exists_ndInterpreterCore`'s docstring; the code is
  identical with comments stripped. No line over 100 characters.
- **Replay:** the kit's downstream closure (the module, `NDCodeSimulator`, `NTimeHierarchy` and the
  two facades). It is chained from the campaign's snapshot when #169 is next in line, after
  #167's 91-module replay, whose closure contains these five. **Pending.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/79-interpreter-startup-api/findings-r2.md`. The gate closes when it has zero
blockers and zero majors.

**Deliver your findings as a downloadable Markdown file named
`interpreter-startup-api-r2-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
