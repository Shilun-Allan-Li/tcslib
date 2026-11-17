# Claude fill · gsw-6a-fills: GSW phase 6a units U4, U5, U7, U9, U10, U11 (41 targets)

**Base** `05999162b77c1f0fef64b07427e1a041a31b43d2` (tree `7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3`): a
deterministic, unsigned local merge of #360's head `3ea428fd8b99ffe33cdfb8dbe8068d0eb000d032` (the Q3 owner-side
readers, branch `land/gsw-6a-readers`) into #359's head `73aedcdaaaffef7e69ab012d9b9195f150bae68d` (the 6a statements,
branch `land/gsw-6a-statements`, stacked on #358's head `a616adcac0760ab56b1b0a2a4869f4763843f9ab`, O1). It follows the
bb1-sim fill's "synthetic merge now" precedent (`briefs/pairings/fills/bb1-sim/issued-fill-r1/`). The merge is clean,
and its Lean is the records tip's plus exactly #358, #359 and #360 (21 Lean files). `tools/mkbase.sh` reproduces it.
**Your patches are against this base.**

**#358, #359 and #360 are unmerged draft PRs.** Gate 45 (Codex, dispatched 2026-11-17) audits #358 and #359 and may
still change a statement. Any such change is the maintainer's to handle (a re-issue or a replay at landing): stay on
the pinned base, do not chase the branches, and if you hear of a change, note it in `REPORT.md` without applying it.

**Unit** `gsw-6a-fills`: the 6a fill units that the maintainer is not filling in-house, from plan section r3 §H7
(units table). **Worker:** Claude in the cloud, a lead with **up to 3 sub-agents** on disjoint files. **Lean** 4.25.0
and the Mathlib revision of the base's `lake-manifest.json` (`029db123ddaa`). **Audit:** the maintainer reviews the
delivery (static, then a merged-tree replay); a fill gate follows.

| Unit | Owned file (at the base) | Rows | Targets |
|---|---|---|---|
| U4 | `TCSlib/Complexity/BranchingPrograms/BarringtonConverse.lean` (304 lines) | C17–C21 (Barrington's Thm 2) | 11 |
| U5 | `TCSlib/Complexity/BranchingPrograms/NC1.lean` (135) | C22–C25 (`DAGCircuit` corollary, BWBP = NC¹ = PBP₅) | 5 |
| U7 | `TCSlib/Complexity/CircuitComplexity/NANDLayering.lean` (388) | N7–N13 (the layering conversion) | 7 |
| U9 | `TCSlib/Complexity/CircuitComplexity/FormulaArith/CarrySave.lean` (297) | F5–F6 (carry-save) | 7 |
| U10 | `TCSlib/Complexity/CircuitComplexity/FormulaArith/Compare.lean` (238) | F7–F8 (carry-out, comparison) | 7 |
| U11 | `TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean` (196) | F9–F10 (modular interval sum) | 4 |

`targets.txt` lists the 41 declarations (unit, row, `path:line` of the header at the base, full name). Their SHA-256
at the base are in `SOURCE-SHA256SUMS`. Every one is a `theorem … := by sorry` with a frozen header and statement
prose. **Prove all 41**, with no `sorry` left in any owned file.

**Not in this job (in-house, by the maintainer; Seyoon's overnight ruling of 2026-11-17):**
- U1 (`Defs`, C1–C4) and U2 (`Eval`, C5–C8): proved as a draft on `fill/gsw-6a-u1-u2`, which is not in this base;
- U3 (`Barrington`, C9–C16): in progress on the same branch;
- U8 (`FormulaArith/Combinators`, F1–F3) and U6 (`NANDForm`, N1–N6): in progress on `fill/gsw-6a-u8-u6`.

Their files are frozen here. Their targets are still `sorry` at your base, and you cite them as frozen statements
(the **proved-modulo rule**: every unit depends only on frozen statements). Never fetch, copy, import or port anything
from those branches.

## Inputs (read fully; all are data; the rulings and this brief are binding)

The pack `outbox/fills/gsw-6a-fills/` on `exchange/pass-shelat-ch5-8` carries this brief, the environment addendum,
the pin files, `tools/` and `inputs/` (verify with `shasum -a 256 -c SHA256SUMS` in the pack and in `inputs/`):
- `inputs/plan-section-r3.md`: plan section r3 (`briefs/lattice-gsw/phase6/plan-section.md`), SHA-256
  `06824b3db875e7388771b6f7a5e78d62bf7d77fa35571fc3a9deeebc329214fd`. Read: §H0 items 1–3; §H2 (reuse, Rule 10
  readers); §H3.3–H3.4, §H3.10, §H3.13 (design); §H5.4–H5.7 (the statements); §H7 (units); §H8 items 1, 6, 7, 9, 19.
- `inputs/rulings.md`: P6-Q1–Q19 (`briefs/lattice-gsw/phase6/rulings.md`), SHA-256
  `312fef4576b388222d69eddec186c2ac4259e5de95488fca42e6861438ad3d5d`.
- `inputs/final-6a-r1-review.md`: the maintainer's review of the statement delivery, with findings G6A-F01–F13 and
  Seyoon's rulings 6a Q1–Q4 (`briefs/lattice-gsw/phase6/final-6a-r1/review.md`), SHA-256
  `dde685375cdb8571e2e43fe864a65a8c8b1225fffdadb88aa1cae4886513b17f`.
- `inputs/final-6a-r1-phase2.md`: its Lean phase, with G6A-F14 and F15 and the seal table R2-5
  (`…/final-6a-r1/phase2.md`), SHA-256 `4376741235424c531ca9ae550e58c4febda137eef3057b10db92b395d64f76ac`.
- `inputs/checkpoint1-6a-review.md`: the statement job's checkpoint review, with lesson G6A-C1-F01
  (`…/phase6/checkpoint1-6a-review.md`), SHA-256 `5968e98ac305cdbfd92dc79812745c8d89a1d414d4c12be30da5d4cf0d7cb232`.
- `inputs/readers-q3-review.md`: the build and checks of #360 (`…/phase6/readers-q3/review.md`), SHA-256
  `ae448305070fde33941c531f1d823f9a0c82cb268718620ee9b321a0df950f5a`.

On the records branch `cryptography/pass-shelat-ch2-4` at the records pin
`7cbd0c93cb053ab399aa40e9163a1229a1d99360`, with their SHA-256:
- `policy.md` (`6599b12230e3879bc0e1fb22c0376ea6201bca8b7edd79dfc55da43986f991d4`): §1 (layout, *Definitions land
  with their lemmas*, *Duplication*), §2 (attribution), §3 (proof sketches);
- `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2, the standing rules
  (`ec3789a127a648862e7ee4b714339200a0fc8adde9538aebae254b9df4271f58`);
- `briefs/pass-shelat-ch5-8/duplication-ledger.md` (`8a4d56c3e2a48d7fe8b8e0d07c8dea962cd13869a31dc41193c9390023dc087c`)
  with rows DL-55, DL-56 and DL-58 (the G44-01 and G48-01 precedents);
- `briefs/pairings/gates/48-bb1-sim-fill/findings-r1.md` (`9e44113b3be5e0a3c29e402294c4fee57fe6edcff2e4599612fbf042d5f4efe4`)
  and `briefs/pairings/gates/44-pairing-fills/findings-r1.md`
  (`48f6b28cbd04ed247a85c7315b403003bf784ec64bc434882721392bd0621180`);
- `briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py`
  (`fa81981add5de30d3a98b7e1614e73b17f149723e8be79558ac1a29b6fe67fbc`).

`workflow.md` on `main` at `b986b8620fc6117034462212df7070c80a79ff65` (fetch `main` by name, read with `git show`;
SHA-256 `6f986529280a265b72040576603ac3430841ececbf0ff19b685df868bd8155f9`): §4 (ground rules), §4.1 (*Lean
parallelism*; the delivery payload), §6.1 (merged-tree replays).

On `exchange/pass-shelat-ch5-8`: **the statement job's delivery** `inbox/fills/gsw-6a-statements/`, final commit
`d7a9adb5b70c70c1b6fb8dc3d0aa5a60d720c1ef` ("stmt gsw-6a: final"). Its `evidence/tools/` (`xr/` seal tools:
`mkcollect.py`, `mkseals_ab.py`, `mkseals_coe.py`, `runner_full.py`, `sealsum.py`, `build_controls.py`; and
`frozen_check.py`, `clash_scan.py`, `scan_unfold.py`, `admissions.py`, `sizes.py`, `sweep.py`) are your starting
tools. Its `evidence/probes/` (P7 `Converse`, P9 `Layering`, P10 `FormulaArith`, `P0_Axioms`) are regression probes
you may re-run. Copy what you use into `evidence/tools/`, adapt host paths, and record each change in the tool's
header.

At the base, the sources the targets cite: `blueprint/src/references/barrington-1989-bounded-width-bp.md`
(`0e14d97efe06b4c9f0e2f7672d744885b4e53fa2a3777c3694a664322620c71a`),
`brakerski-vaikuntanathan-2011-fhe.md` (`f415fdbd4488316e2044e0a8e767c75b69964ff48fb6294617b35ae125177eba`) and
`brakerski-vaikuntanathan-2014-fhe.md` (`3da79813fa63acfea4a83229c46f2f8947a7a754657fac8f4d6bf1e7891e9392`).

## Binding rulings (Seyoon; `inputs/rulings.md`, the 6a Q1–Q4 rulings in `inputs/final-6a-r1-review.md`)

- **P6-Q3, P6-Q18.** Barrington in both directions. Thm 2's circuit is a fan-in-2 `TreeCircuit` formula in Bar89's
  three sections, reaching `Language.InNC 1` through `Language.InTreeNC.inNC`; `toFormula` is `noncomputable`.
- **P6-Q5, P6-Q6.** The formula-arithmetic layer over `TreeCircuit` in `FormulaArith/`; `Parity.lean`'s private XOR is
  **not** copied or re-pointed here (dedup queue).
- **P6-Q14 B.** The layering conversion with double-NAND chains, a parity twin for odd gaps, and literal inputs.
- **P6-Q16 A.** NAND form is a predicate on `DAGCircuit`; NAND-form circuits are not `IsWellFormed` (disclosed).
- **6a Q1 A (LE-ren).** `TreeCircuit.rename` is gone; the public `TreeCircuit.reidx`, `reidx_eval`, `reidx_depth`
  (`BooleanAnalysis/LMN/CircuitReindex.lean`) are the reindexing family (DL-54 moves them later). Do not recreate
  a `rename`.
- **6a Q3 A.** The nine missing readers plus `gadgetCorrect_iff` land as one owner-side PR (#360) before the fills:
  they are in your base (*The Q3 readers*).
- **6a Q4 A.** N12 stays in the `args_lt` field form; fill it in that form.
- **Proved-modulo.** Units never share a file, depend only on frozen statements, and run in parallel.
- **Lean parallelism (user, 2026-11-17; `workflow.md` §4.1).** Cloud workers run a memory-sized pool of Lean
  processes (the addendum's adaptation).

## Feasibility and size (maintainer's assessment)

Feasible as one job; r3 §H7 estimates **1,130–1,870 fill lines** (U4 250–400, U5 180–320, U7 150–250 and up to about
300 by r3 §H8 item 19, U9 250–400, U10 150–250, U11 150–250). Every owned file stays under 1,000 lines (expected
about 300–700 each, filled). The statements were probed at the statement phase: C19–C21 on instances (P7), N7–N11 on
three circuits including the odd-gap case (P9), and the formula arithmetic exhaustively for small parameters (P10);
the maintainer re-derived every constant (`inputs/final-6a-r1-review.md`). No target is expected to be false.

The long mechanical steps are the 218-module bootstrap, the 9-module sweep, the seals of six owners in four variants
at head and base, and the controls. With the pool they run in parallel.

**Suggested split** (disjoint files; record any other split in `REPORT.md`):
- **lead**: U5 (`NC1`) and U11 (`ModSum`), the integration, every final check and the delivery;
- **sub-agent `bp`**: U4 (`BarringtonConverse`);
- **sub-agent `layer`**: U7 (`NANDLayering`);
- **sub-agent `fa`**: U9 (`CarrySave`) and U10 (`Compare`).

U5 cites U4's statements and U11 cites U9's and U10's: under the proved-modulo rule all six start at once.

## Base, branch and delivery

- **Checkout.** In your own clone, fetch by name `cryptography/pass-shelat-ch2-4`, `land/gsw-6a-statements` and
  `land/gsw-6a-readers`. If either `land/` branch has moved past the pinned head, fetch `refs/pull/359/head` and
  `refs/pull/360/head`, or the pinned commits by hash; if you cannot get both pinned commits, stop with **E-BASE**.
- **The base.** Run `bash <pack>/tools/mkbase.sh` in the clone: it must print
  `BASE 05999162b77c1f0fef64b07427e1a041a31b43d2 tree 7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3`. Equivalently, with
  a work tree:

  ```sh
  git checkout -b fill/gsw-6a-fills 73aedcdaaaffef7e69ab012d9b9195f150bae68d
  GIT_AUTHOR_NAME='TCSlib gsw-6a-fills staging' GIT_AUTHOR_EMAIL='staging@tcslib.invalid' \
  GIT_COMMITTER_NAME='TCSlib gsw-6a-fills staging' GIT_COMMITTER_EMAIL='staging@tcslib.invalid' \
  GIT_AUTHOR_DATE='2026-11-17T12:00:00+00:00' GIT_COMMITTER_DATE='2026-11-17T12:00:00+00:00' \
  git -c commit.gpgsign=false -c merge.log=false merge --no-ff --no-edit \
    -m 'gsw-6a fills base: merge #360 head 3ea428fd (Q3 readers) into #359 head 73aedcda (6a statements)' \
    3ea428fd8b99ffe33cdfb8dbe8068d0eb000d032
  git rev-parse HEAD HEAD^{tree}   # 05999162… and 7d551d6f…
  ```

  The maintainer ran both forms and got the same commit. If the tree or the commit differs, stop with **E-BASE**.
  Record the output in `REPORT.md`. The base is not delivered as a patch.
- **The branch** `fill/gsw-6a-fills`, from the base. One or more commits per unit, **each touching exactly one owned
  file**, with messages such as `fill gsw-6a-fills: U4 BarringtonConverse (C17-C21)`, so that the maintainer can land
  the units separately. Commit with `git -c commit.gpgsign=false`: the series must be **unsigned**, so that `git am`
  reproduces every hash. Keep every branch local.
- **Stay on the base.** Do not rebase onto the records tip, #358/#359/#360 or the in-house branches, whatever merges.
  The maintainer replays at landing (`workflow.md` §6.1). At delivery, record `git merge-tree --write-tree` of your
  head with the then records tip (expected clean; information only).
- **Deliver** every checkpoint and the final only under `inbox/fills/gsw-6a-fills/` on `exchange/pass-shelat-ch5-8`,
  in the standard payload (`workflow.md` §4.1):
  - `REPORT.md` (*Report*), naming the **full hash of the branch head it describes**;
  - `patches/`: `git format-patch 05999162b77c1f0fef64b07427e1a041a31b43d2..fill/gsw-6a-fills`, with `COMMITS.tsv`:
    one row per commit with its hash, the author's name, email and date, the committer's name, email and date, and
    its **signing** (`none`, or the format). Check in a scratch clone that `git am` at the base reproduces every hash,
    and say so;
  - `src/`: every owned file at the head, under its repository path;
  - `evidence/`, with its manifest `evidence/SHA256SUMS`;
  - a top-level `SHA256SUMS` of every delivered file except itself. The delivered paths must **equal** the manifests'
    paths: nothing missing, nothing extra, no leading `./`. Check this before each push.
- **Every checkpoint is a full payload for what it claims** (lesson G6A-C1-F01): its `REPORT.md` names the head hash,
  its `patches/` run to that head, and its `src/` holds every owned file it claims compiles, with the build logs that
  bind those sources to that head. A claim without `src/` and patches is not a claim.
- **Exchange commits.** Commit on the exchange as `fill gsw-6a-fills: checkpoint N` and `fill gsw-6a-fills: final`,
  with `git -c commit.gpgsign=false`. Pull with `git -c commit.gpgsign=false pull --rebase` (BSF-F01: a plain
  `pull --rebase` re-created an earlier worker's commit under the host's global signing setting). After the rebase
  and before the push, `git cat-file -p HEAD | grep -c gpgsig` must print `0`. **The maintainer expects unsigned
  commits throughout**; provenance rests on the pinned hashes and the maintainer's signed cherry-picks. If the
  platform signs an exchange commit anyway, disclose it in the next commit; never rewrite or force-push to remove it.
- Push only your path; never force-push; never touch another path (other fills, gates, `outbox/`,
  `arora-barak-ch3-4/`, `lwe-sis-constructions/`). **Never push a campaign branch.** If a push is refused, keep the
  commit and say so.

## The Q3 readers (#360, in your base) and the sketches that use them

The statement phase's reader census listed these as missing (G6A-F03), and several frozen sketches still say "missing
at the base; proposed". They are now published, pure insertions, none `@[simp]`:

| Reader (file:line at the base) | Form | Sketches that use it |
|---|---|---|
| `BoolCircuit.Lit.eval_eq` (`Basic.lean:114`) | `l.eval x = if l.sign then x l.idx else !x l.idx` | C17 (U4); F9 (U11) |
| `TreeCircuit.depth_lit` (`Basic.lean:217`) | `(lit l).depth = 0` | C17 (U4); F10 (U11) |
| `TreeCircuit.size_lit` (`Basic.lean:221`) | `(lit l).size = 1` | C24 (U5), if needed |
| `TreeCircuit.maxFanin_lit` (`Basic.lean:225`) | `(lit l).maxFanin = 0` | C17 (U4); F10 (U11) |
| `BoolCircuit.carryBit_zero`, `carryBit_succ` (`Adder.lean:382`, `:386`) | the two cases of `carryBit` | F7 (U10) |
| `BoolCircuit.gatesAcyclic_iff` (`DAGCircuit.lean:400`) | `GatesAcyclic n gs ↔ ∀ i (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < n + i` | N12 (U7), if you reason through `GatesAcyclic` |
| `DAGCircuit.isWellFormed_iff` (`DAGCircuit.lean:519`) | the body of `IsWellFormed` | C22 (U5) |
| `TreeCircuitFamily.isPolySize_iff`, `hasFaninTwo_iff`, `hasPolylogDepth_iff` (`TreeNCAC.lean:119`, `:128`, `:137`) | the bodies of the three predicates | C23, C24 (U5) |
| `Language.inTreeNC_iff` (`TreeNCAC.lean:153`) | the body of `Language.InTreeNC` | C23, C24 (U5) |
| `BoolCircuit.gadgetCorrect_iff` (`DAGTransform.lean:76`) | the body of `GadgetCorrect` | N2 (U6, in-house; not yours) |

`Lit.eval` itself carries `@[simp]` (`Basic.lean:109–110`, pre-existing): read it through `Lit.eval_eq` and do not
rely on `simp` unfolding it. The frozen statement prose stays as it is; you may refresh a target's
`**Proof sketch.**` (*Scope*) so that it names the reader it now uses.

If a proof needs another reader of a foreign definition, that is a **scope request** (*Scope*), never an unfold.

## Known context per unit

- **U4 (Thm 2).** Uses Defs' C1 (`yield_append`, `yield_nil`; U1's, frozen) and the readers `yield_eq`,
  `Instr.eval_eq`, `append_instrs`, `length_eq`; O1's proved `balanced_eval`, `depth_balanced_le`,
  `maxFanin_balanced_le` (`FormulaArith/Combinators.lean`). C19's constant is r3's; C21's `topDepth` is `+3`, one
  less than r3's draft (G6A-F08, re-derived by the maintainer). r3 §H8 item 6: a formula, not a DAG (size
  `l^{O(log w)}`). The composition tree is defined by well-founded recursion; read it only through `compTree_nil`,
  `compTree_singleton`, `compTree_cons_cons`.
- **U5 (classes).** Uses U3's C9, C13–C15 (frozen, in progress in-house), U4's C20–C21 (yours, proved-modulo), C1's
  `yield_nil`, `toTree_eval`/`toTree_depth_le`/`toTree_maxFanin_le` (`TreeDAG.lean`), `Language.InNC.inTreeNC_one`,
  `Language.InTreeNC.inNC`, `BoolCircuit.clog_poly_le` (`TreeNCAC.lean:309`, public) and the Q3 readers. r3 §H8
  item 7: `n = 0` goes through the accepting set (`[]` and `{id}` or `∅`). C22 needs `IsFaninTwo`, which includes
  `IsWellFormed`, exactly what the `toTree` lemmas need (G6A review). The σ 0 reading (G6A-F11) concerns C16 and 6b,
  not this unit: do not touch C16 or its note.
- **U7 (layering).** The odd-gap finding (layered NAND circuits over positive inputs compute only monotone or
  antimonotone functions, so XOR has none) is why the inputs are the `2n` literals; the parity twin and the literal
  inputs are part of the frozen definitions. Probe P9 (`evidence/probes/P9_Layering.lean` at `d7a9adb5`) checked N7–N11
  on an XOR circuit, on `oddC` (whose padding is an even double-NAND chain, G6A-C1-F07) and on a fan-in-0 gate, with
  the real `layerNAND`. The column invariant in the module docstring is the plan of every target. N12 is in the field
  form (6a Q4 A, G6A-F04). N7 uses U6's N1 `DAGGate.eval_of_isNAND` (frozen, in-house). **G6A-F14:** while N12–N13
  are admitted, `layerNAND`, `layerNAND_gates` and `layerNAND_output` carry `sorryAx` through them, and the five
  N7–N11 statements reach N12–N13 through `layerNAND`; once you fill N12–N13, those traces must be empty of N12–N13.
  r3 §H8 item 19: exact depths through `runWith` may need their own ledger; U7 may reach about 300 fill lines.
- **U9–U11 (formula arithmetic).** Uses U8's F1–F3 (`const_eval`, `xor3_eval`, `maj3_eval`, `and2_eval`, `or2_eval`,
  `neg_eval` and their depth and fan-in lemmas; frozen, in progress in-house) and `Adder.lean`'s `bitsVal`,
  `prefixVal`, `carryBit` through their readers (`bitsVal_eq_prefixVal`, `prefixVal_zero`/`_succ`/`_congr`/`_lt`,
  `prefixVal_add`, `carryBit_zero`/`_succ`). r3 §H3.3 and §H8 item 1: **no depth term linear in `log q`**, so no
  Shannon, DNF or truth-table step over a `log q`-bit value, in a definition or in a helper. The settled constants
  (G6A-F08) are frozen: F6 `csaLevels k ≤ 2⌈log₂ k⌉` (the maintainer re-checked it numerically for `k < 200000`, with
  the sketch's step `k₂ ≤ ⌈k/2⌉`), F7 `2⌈log₂ b⌉ + 3`, F8 `+7`, F10 r3's closed form. G6A-F09: F9's `lo ≤ hi` is
  unnecessary but stays.
- **G6A-F07 (optional, U7 only).** `NANDLayering.lean`'s `## References` line for [Bar89] reads "D. A. Barrington …
  J. Comput. Syst. Sci."; the ingest header and the other files read "D. A. Mix Barrington … J. Comput. System Sci.".
  You may correct that one line, disclosed.

## Scope

| File | Permitted change |
|---|---|
| the six owned files | the 41 proof bodies; **private** helper lemmas inserted between declarations, each before its first use; each target's `**Proof sketch.**` paragraph, only to describe the delivered proof (policy §3, *Synchronization*); in the module docstring, only the sentence(s) saying that the targets are admitted with `sorry`; new `import` lines only as *Imports* says; and, in `NANDLayering.lean`, the G6A-F07 reference line |

- **Frozen in the owned files:** every target's header (keyword through `:= by`) and its statement prose before
  `**Proof sketch.**`; every definition, its body and its readers; every `structure`, `instance`, `simps` attribute
  and `set_option`; namespaces and `variable` lines (add a `section` with its own `variable` if you need one).
- **Frozen elsewhere:** everything else, including the in-house units' files (`BranchingPrograms/{Defs,Eval,
  Barrington}.lean`, `NANDForm.lean`, `FormulaArith/Combinators.lean`), every file #358, #359 and #360 touch, the
  facades `BranchingPrograms.lean`, `FormulaArith.lean`, `CircuitComplexity.lean`, `ComputationalModels.lean`,
  `TCSlib.lean`, `machine-library-design.md`, `blueprint/`, `audits/` and everything under `Cryptography/`.
- **Imports.** A new `import Mathlib…` line in an owned file only to reuse a Mathlib lemma (addendum: fetch its roots).
  A new TCSlib import only of a module already in `order.txt` that does not import the owned file (no cycle), and only
  to reuse a published lemma. Disclose each with its reason.
- **No new module, no new public declaration.** Helpers are `private` (`workflow.md` §4, ground rule 1). A helper
  that belongs in a shared file (a general fact about `TreeCircuit`, `DAGCircuit`, `List`, `Nat`) is requested in
  the report for a later promotion, and lives `private` here until then; if Mathlib or TCSlib already has it, use that
  instead (*Duplication*).
- **Scope requests.** If a proof needs a change to a frozen file (a reader, a promotion, an import that creates a
  cycle, a new module because a file would pass 1,000 lines), stop that line of work and ask Seyoon in your session,
  giving the file, the diff and the reason; go ahead only on his approval. Record the request and his answer verbatim
  under `evidence/scope-request/` and in `REPORT.md`. Seyoon prefers routes with no frozen-file edit. A missing reader
  is always a scope request, never a definitional unfold.

**What you may not do.**
- Change a target's header, statement prose, name, file or position; weaken, strengthen or re-quantify any statement;
  change a definition.
- Add an admission (`sorry`, `admit`, `native_decide`, `axiom`) or any `set_option` that weakens checking.
- Unfold a foreign definition (*Rule 10*), or copy a private lemma of another file.
- Leave any re-derivation of a Mathlib or TCSlib lemma, disclosed or not (*Duplication*).
- Push anything but your delivery path.

If a target looks false as stated, do not change it: prove the counterexample in a probe outside the library (kernel
`decide` or `rfl`, `#eval` output recorded as evidence only) and report it as a question for Seyoon (**E-ROUTE**).

## Proof discipline

- **Rule 10 (readers only; policy §1).** Read other files' definitions only through their published readers and
  lemmas, including generated matchers and projections. Core and Mathlib definitions may reduce in a `rfl`, `decide`
  or `show` step but are never passed to `simp`, `rw` or `unfold`. Each owned file may read its own definitions
  directly; the six owned files are foreign to each other and to every other file.
  - **Seals.** Canonical seal is **coe-A**; strict A and B and coe-B are run and attributed (*Checks* 5).
  - **Notation, never sealed:** reducible abbreviations; `PolyExpr.eval`; projection coercions; the `FinDist`
    coercion (DW-10 Q3). Strict-only failures they cause are listed, not counted, and not "fixed".
  - **Paired controls** for any new public definition (none is allowed here, so none is expected), and one liveness
    pair per owner (*Checks* 5).
- **Duplication (binding; policy §1).** Search TCSlib, core, Batteries and Mathlib **before writing any helper**: by
  name, by `exact?`/`apply?`/`simp?` on its statement in a scratch probe, and by grep for its conclusion's shape.
  **An inline re-derivation of a Mathlib or TCSlib lemma is a major finding**, disclosed or not:
  - G48-01 (Gate 48): a local `have` in T2 re-derived Mathlib's `abs_sub_le_of_nonneg_of_le`; first accepted as debt
    (DL-58), then, by Seyoon's revised ruling, fixed at once by a landing edit (LE-g48; `PairingCryptographyPlan.md`,
    decision log, at the records pin);
  - G44-01 (Gate 44): disclosed re-derivations of public TCSlib facts still needed a recorded acceptance and a ledger
    row (DL-55, DL-56); disclosure is not acceptance.

  So: use the existing lemma (adding the Mathlib import if needed); never restate it as a private helper. Typical
  candidates here: `List.foldl`/`List.range`/`List.getD`/`List.take`/`List.sum_ofFn` facts, `Nat.clog`/`Nat.log`
  bounds (`Nat.clog_mono_right`, `Nat.clog_of_two_le`, `Nat.le_pow_clog`, `Nat.clog_le_of_le_pow`), `Nat.testBit`
  and binary-expansion facts, `Finset.sum` over `Fin`, `TreeCircuit` list lemmas in `Basic.lean`
  (`depth_le_maxDepth`, `maxFanin_le_maxFaninL`, `maxDepth_cons`, `maxFaninL_cons`, `size_succ_le_two_pow`),
  `DAGCircuit` depth and value readers (`depthAt_gate`, `DAGGate.depth_eq`, `values_getD_input`, `values_getD_gate`,
  `GatesAcyclic.snoc`/`.append`), `BoolCircuit.clog_poly_le`, and the `TreeCircuit.reidx` family. Do not copy
  `Parity.lean`'s private `xorNode`/`IsDual` or any `private` lemma of another file.
  Disclose every remaining overlap in `REPORT.md` § *Overlap and reuse* (nearest relative `path:line`, relation, why
  not reused) and list the searches you ran.
- **Docstrings and sketches (policy §2–§3).** Every private helper has a docstring that states it in words with its
  formula (arguments in Lean order) and says "Glue." (no source tag on helpers). Every nontrivial proof (about 20
  lines or more) has a `**Proof sketch.**` in its target's or helper's docstring, with step comments at the major
  `have`s of long proofs; the steps a sketch names are visible as `have`s or lemmas. A refreshed target sketch keeps
  the statement prose before it byte-identical. Never fabricate a quotation, location or anchor; add no tag.
- **Sizes and widths.** Every line at most 100 characters (Python `len`), every file at most 1,000 lines (policy
  target 600). No `@[simp]`, no global attribute. Identifiers use the Greek `μ` (U+03BC), never the micro sign.

## Multi-agent work (up to 3 sub-agents) and Lean parallelism

- **The lead owns the job:** the branch `fill/gsw-6a-fills`, every commit, the integration, the final sweep and checks,
  the delivery and `REPORT.md`. Only the lead commits on `fill/gsw-6a-fills`, runs `lake`, fetches the cache and
  pushes.
- Each sub-agent owns its files exclusively, works in its own git worktree with its own TCSlib olean tree and
  `.lake/packages` linked to the lead's, and hands its files to the lead as patches. A file is reassigned only
  through the lead, after its owner has stopped. Sub-agent logs go under `evidence/subagents/<name>/`; `REPORT.md`
  records who wrote what.
- **Lean pool** (addendum, *Adaptation*; `workflow.md` §4.1): all agents share one memory-sized pool of Lean
  processes (a counting semaphore), at most `nproc` and keeping about 2 GB or 15% of memory available, in dependency
  order, never two processes on one module or one output file. Record the pool size, its changes and peak memory.

## Checks and evidence

Run Python as `python3 -I`. Never run `lake build` or an unfiltered `lake exe cache get`; compile each module with
`scripts/lean_check_tree.sh` (the addendum). Count errors in both forms (`^\S+\.lean:\d+:\d+: error[:(]`) in every
log, and keep every raw log.

1. **Bootstrap and sweep.**
   - Bootstrap `order.txt` (218 modules) at the base: rc 0, 0 errors, and exactly the `sorry` warnings of
     `base-sorries.txt` (**115 declarations in 18 modules**).
   - **Sweep at the head:** rebuild every module whose source differs from its olean's source, then its downstream, in
     order; then check every module of `closures.txt`'s `DOWN` (9: the six owned files, `FormulaArith`,
     `CircuitComplexity` and `BranchingPrograms`), each rc 0 and 0 errors in both forms. Bind every checked source to
     `git show HEAD` (`evidence/build/summary.txt`: module, rc, errors in both forms, `sorry` warnings, source
     SHA-256). The root `TCSlib` is not built.
2. **Admissions.** At the head: exactly `base-sorries.txt` minus the 41 targets of `targets.txt`, which is **74
   declarations in 12 modules**; no `sorry` token in any owned file. A checkpoint lists every remaining `sorry`.
3. **Statements.**
   - `python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py . 05999162b77c1f0fef64b07427e1a041a31b43d2 <the six files>`
     at the head:
     **0 ADDED, 0 CHANGED, 0 REMOVED** (helpers are private).
   - A `StmtDump` probe printing the 41 targets with full names and types, at the base and at the head: identical.
   - **Frozen check** (a `python3 -I` script under `evidence/headers/`): in each owned file, everything except the 41
     proof bodies, the 41 sketch paragraphs (after `**Proof sketch.**`, inside the docstring), the inserted private
     helper blocks, the permitted module-docstring sentences, permitted imports and the G6A-F07 line is
     byte-identical to the base. Each control must FAIL with the stated count: a one-character header change; an edit
     that spills from a sketch into the statement prose; an edit to a definition's body; an edit to a reader; an
     unpermitted import; a deleted target. The unchanged file must PASS.
4. **Axioms.**
   - `#print axioms` of the 41 targets and every helper: `propext`, `Classical.choice`, `Quot.sound` (or a subset),
     plus `sorryAx` **only through frozen targets of the in-house units**.
   - A census of every stored constant of the six owned modules, and a **dependency trace** that names, for every
     constant reaching `sorryAx`, the admitted declarations through which it does. Every name in the trace must be an
     admitted declaration of `BranchingPrograms/Defs`, `Eval`, `Barrington`, `CircuitComplexity/NANDForm` or
     `FormulaArith/Combinators` at the base (expected: C1 for U4 and U5; C9, C13–C15 for U5; N1 for U7; F1–F3 for
     U9–U11), never a declaration of an owned file. `layerNAND`, `layerNAND_gates` and `layerNAND_output` must have
     an empty trace (G6A-F14). The statement job's `AxiomProbe.lean` (at `d7a9adb5`) is a ready form.
5. **Rule 10.**
   - **Seals** A and B, strict and coe (**coe-A canonical**), with `-DmaxErrors=0`, over the full TCSlib import
     closure, of the six owners at the head, and **base seals** of the same six at the base. Report each seal's
     request count and every failing declaration, attributed by its raw log. The maintainer's reference at #359
     (snapshot #5, `inputs/final-6a-r1-phase2.md`, R2-5): `BarringtonConverse` 243, `NC1` 333, `NANDLayering` 187,
     `CarrySave` 253, `Compare` 269, `ModSum` 273, 0 errors in all four variants; #360 adds only theorems.
     **No failing declaration at the head.** Use chunking (`SEAL_CHUNK`) if a run overflows (G6A-F10).
   - **Controls.** For each owner, one liveness pair: a negative that reads a foreign definition its proofs use by
     `rfl`/`unfold` in a consumer's context (passes unsealed, fails sealed exactly once) and a positive through the
     published reader (passes sealed). Pretest unsealed first; strict and coe both `ALL_OK True`. Any new public
     definition would need its own pair (none is allowed).
   - **Explicit-unfold scan** over the six files: 0 foreign.
6. **Frozen-file check.** `git diff --stat 05999162b77c1f0fef64b07427e1a041a31b43d2` lists only the six owned files.
7. **Lint.**
   - `python3 -I scripts/style_lint.py <the six files>`: 0 findings (0 at the base, the maintainer's run).
   - `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity --check8b` at the base and the head. The
     maintainer's run at the base: **25 FAIL / 390 WARN over 513 files**. Diff the line sets: no new FAIL or WARN
     line, except one you disclose and justify.
8. **Sizes and widths** of the six files at base and head, by a `python3 -I` script, against r3's estimates.
9. **Docstrings and sketches** as in *Proof discipline*: a hygiene scan listing every helper without a formula or a
   "Glue." note (expected: none), and every proof over about 20 lines without a sketch (expected: none).
10. **Name-clash and shadow scans.** (a) No new full name, private included, already exists in `TCSlib/` or `audits/`
    at the base (namespaces resolved). (b) List every new short name that exists elsewhere. (c) Show that no
    unqualified use in a `DOWN` module changes its resolution.
11. **Reuse and overlap** (*Duplication*; `REPORT.md` § *Overlap and reuse*), with the searches you ran.
12. **Reproduction.** `git am` of `patches/` at the base, in a scratch clone with `COMMITS.tsv`'s committer data,
    reproduces every hash; `src/` equals the head's six files byte for byte.

## Checkpoints

- **Checkpoint 1**, as soon as it is ready: the base reproduced (`mkbase.sh` output); the preflight, the cache and the
  bootstrap (check 1, first part); **at least two units fully proved**, with checks 2–5 for their files; for every
  other unit, an outline (each target mapped to the private helpers it will use, with their statements) and the
  duplication searches done so far. Deliver it as a full payload (*Base, branch and delivery*): head hash, patches,
  `src/` of every owned file at that head, and the logs binding them.
- Further checkpoints as units complete, in the same form.
- **The final** has everything, with no `sorry` in any owned file.

## Report

`REPORT.md` gives:
- the base (`mkbase.sh` output or the merge reproduction), the records tip seen at delivery and the merge-tree with
  it, the branch head (full hash) and every commit with its unit;
- the preflight figures, the pool size and its changes, peak memory, and who wrote what;
- the six files with their lines at base and head;
- per unit: each target proved, the private helpers added (full name, docstring formula), the readers used, any
  refreshed sketch (old and new text), and any import added with its reason;
- § *Statement changes*: none (any change is a blocker, not a report item);
- the checks 1–12 with their results;
- § *Overlap and reuse*; § *Promotion requests* (helpers that belong in a shared file); § *Scope requests* (none, or
  each with Seyoon's answer);
- questions for Seyoon, if any, numbered `GF-W1`, … with the recommended option first;
- the evidence, with its manifest.

### Evidence completeness

Every file that `evidence/SHA256SUMS` names is delivered: build and sweep logs with `summary.txt`, the admission
counts, decls2 output, the `StmtDump`s, the frozen check with its controls, the axiom prints and the trace, seal and
control sources, manifests, request records and raw logs, the unfold scan, lint outputs, the size script and output,
the clash and shadow scans, the duplication searches, the reproduction log, sub-agent logs, `pool.log` and the tools
used. If the evidence is too large for one commit, deliver it in several commits or numbered ZIP parts, each with an
entry list; leave nothing out for size.

## Blockers: stop and report

- **E-RES (environment).** The addendum's preflight or cache rules fail. Stop and report the numbers.
- **E-BASE.** The pinned commits cannot be fetched, or `mkbase.sh` (or the merge) gives another tree or commit.
- **E-SCOPE (frozen files).** A proof needs a reader, promotion, import or module the *Scope* does not permit. Stop
  that line of work and ask Seyoon (*Scope*); continue the other units meanwhile.
- **E-ROUTE (proof).** A target looks false or unprovable as stated, or the proof fails in a way no change inside the
  owned file fixes. State the exact obligation, with the failing goal or a counterexample probe.
- **How to report.** Push a checkpoint `fill gsw-6a-fills: checkpoint N (blocked: <code>)` whose `REPORT.md` opens
  with the blocker, the exact obligation or request, and the logs. Keep everything that already passes. Never work
  around a blocker by weakening a statement, adding a hypothesis, editing a frozen file without approval, unfolding a
  foreign definition, or using a private stand-in.

**Ready to dispatch**
