# RO1 CfgFacts-home held candidate

**Held for the import/home decision; not authorized to publish the import additions.**
The source worktree contains the complete uncommitted proposal. No commit, push, PR,
gate, canonical record change, screen, or full downstream replay was performed here.

The approved ruling is HANDOFF §3 item 4: the generic
`Turing.MultiTapeTM.runFrom_one` lives in CfgFacts, replaces the Bool-only
`Turing.runFrom_one`, and every site, including colleague-owned sites, is repointed.
The new generic theorem and mechanical removals/repoints implement that ruling.
Eight direct CfgFacts imports are explicitly held proposals. The Simulation site
remains unchanged because the ruled home is above it in the dependency graph.
The requested Deterministic-home alternative is separate proposal work after this
folder freezes; nothing in this option adopts a revised home.

The baseline source pin is `9b5dcf46408db681bcbc721930ef2203fa6bc47d` (whole MAC8).
The assigned worktree HEAD is `8e5f2266b6ababbd0784f717e65a4903a0e3a0f0`, branch
`codex/ab34-runfrom-one`; its Lean tree equals that baseline commit. The actual
worktree is `/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4`.
`final-pins-and-worktree.json` records the read-only Git checks and exact dirty list.

The final patch changes 60 owners:229 existing declaration bodies plus one new API,
and removes five old copies. Every retained declaration header is byte-identical.
The only changed definition body is `Turing.zr_cellContract`: only its `run` and
`env` proof fields change; every other field is byte-identical. The Bool public
copy and four private copies (`qy_run_one`, `xr_runFrom_one`, `satRed_one`,
`recordStep_runFrom_one`) are removed, and no former-name tokens remain.
The new API has no simp attribute. The positive explicit tactic-argument token
delta contains only the new theorem and `Nat.zero_add`, both theorem readers.

The eight precise import proposals are:

- `TCSlib/Complexity/ClassP/Examples.lean`
- `TCSlib/Complexity/TimeHierarchy/ClockMachine.lean`
- `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean`
- `TCSlib/Complexity/TuringMachine/CounterProg.lean`
- `TCSlib/Complexity/TuringMachine/Encoding.lean`
- `TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean`
- `TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean`
- `TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean`

Every addition is exactly `import TCSlib.Complexity.TuringMachine.CfgFacts`.
No new hub import is proposed. The complete proposed graph is acyclic, and all
new consumer citations have API visibility. The eighth import was discovered by
the full closure preflight for ObliviousCandidate; earlier seven-import counts
are retained as preliminary artifacts and superseded by `final-held-imports.json`.

The remaining exact Simulation pair is `bufferedScanCfg_run`, baseline line1125.
The existing dependency path is CfgFacts → StateRenaming → Simulation, so the
reverse import cycles. The separately frozen witness is
`/private/tmp/ab34-ro1-simulation-cycle/` (manifest
`f5362cc8ec626d4ca9c8321a4e8b583d51fc4457f189ae09d20e18b2208a5dcb`).
No alternate API or home is introduced in this candidate to bypass it.

| Executed check | Result and bound |
|---|---|
| Final changed-owner native checks |60/60 exact final source hashes pass,0 errors;575 warnings, including 4 unchanged RecordTable mathematical-sorry warnings outside the 230 changed/new roots. |
| AX current/baseline |230 current roots /229 baseline roots; every existing root has exactly the same axiom set. No checked RO1 root reaches sorryAx. New API: propext, Quot.sound. |
| Complete new API doc/header/body native and sealed |Both pass,0 errors/warnings/sorries, under all 6 ordinary reached foreign-definition guards. Imported theorem values are not traversed; projections/kernel abbreviations are classified separately. |
| Fresh opacity controls |12 actual kernel-checked positives pass; the exact same 12 point/abstract controls fail sealed, with expected exit 1 and 12 intended rfl errors. Action.apply's default simp unfolding is removed in both variants. No unsafe reducibility or transparency override. |
| Header/definition/admission comparison |0 retained-header changes. One contract's 2 proof fields only. Direct sorry-token counts unchanged across all 929 TCSlib sources; the 4 RecordTable warning declarations are byte-identical. |
| Snapshot provenance |Complete 895-object private MAC8 clone; own target outputs unlinked before leanelab-o. All 895 original MAC8 hashes unchanged; final whole private map retained. No splicing. |

Every elaboration used the approved wrapper, one own slot, local3/machine5,
four threads under nice10. Failed native/preparation attempts are preserved:
the first restricted wrapper could not access the shared lock and stopped before
Lean with exit130; subsequent proof failures exposed zero-plus-one simp matching
and fixed-time-two closures. The latter retain the outer successor equation and
cite the generic inner one-step equation. Corrected receipts are tied to the final
source SHA; failures are never counted as passes. Script assertions failed before
source writes and are preserved/disclosed in `failure-preparation-notes.json`.

`DECLARATION-DISPOSITIONS.md` enumerates all concrete changed/new declarations,
all five removals and the cycle obstruction. `fragment-dispositions.json` has 301
fragment/revision rows, including refinements; that is not a copy count.
`uncapped-shape-dispositions.json` retains all 970 lexical successor-equation
occurrences and 140 parsed literal-one applications across 929 sources, with
dispositions. Source capture/hash populations and listings are uncapped. These
shape searches, including inline calc/change/show/rfl/iterate-one/simp uses, are
candidate enumeration plus inspection, not a semantic exhaustiveness theorem.
Full original sources are in `source-before/`; final complete changed owners are
in `source-current/`, all as `.lean.txt`. `current-held-candidate.patch` is the
complete baseline-to-final diff. Intermediate captures/logs remain intact.

The pending FE/FH/CH7 drafts are not assumed merged. `pending-family-overlap.json`
maps known frozen roots and owner overlaps. In particular, SafeRun.cons is a
same-declaration overlap with CH7; root should preserve CH7's verified whole proof
when rebasing and reapply only any residual reader need. FH's three named roots
and CH7's five EmitIter facts/Hardness head-tail roots are unchanged by RO1.
Exact later remote-PR pin disjointness is not claimed without those final inputs.

The seven accepted SG 1 structural kinds, FE-LIVE/FH1/BLIVE separation, the 54-name
affected union (not 54 copies), the bounded class-image residual, and the prior
nine inherited Primitives AX closures remain unchanged. The 230-root AX result
does not convert those closures into direct admissions or establish global clear.
The remaining two-step rfl proof in CodePrefix and arbitrary-time/RProg/Oracle
variants are not literally the generic one-step statement and are retained.

Root owns the choice between this held-import option and any separately prepared
home revision, the final source commit, joint pending-family integration,
downstream replay on the then-current campaign tree, and audit/closure. The
consumer proofs were checked natively here; a full consumer opacity sweep or
post-other-PR merged-tree replay was not run or inferred.
