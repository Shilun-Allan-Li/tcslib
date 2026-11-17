# Claude job · Pass–shelat cleanup, Stage 1 (promotions): the general forms of the duplication ledger, additive only

**Issue base** `daa6e173cdd94cad1475b9a96eca613bce53ba61`, the head of #347 (DW-5, branch `cleanup/dw5-derand-readers`,
fetch it by name; also `refs/pull/347/head`). It sits on the records branch `cryptography/pass-shelat-ch2-4` at
`2da7e0f3cd65ec93ed71813b7828c3b66ba18942` with DW-5's two commits (the typed-view readers in `ModuleHost.lean` and
`IterateFindHost.lean`, and the re-derivations in `IterateFind.lean`). **Check base**: the prospective merge of the
records branch's last Lean state, `f99901fdc98f4c7703cf9485329600311a1ea655`, with the issue base. `git merge-tree
--write-tree` of the two is clean and gives tree `01cc6259480ccc9372181cd4d18d4511c87aa048`. The records tip at issue,
`8adee3e6ace3ec78171fc499b3d101a252534d55` (Seyoon's Stage 1 rulings), changes no `.lean` file, `lean-toolchain` or
`lake-manifest.json` since `f99901fdc…`: merging it instead gives tree `904efbc22764d0c92f89fd2d2561fba4409fbb74`,
whose Lean sources are identical. Read the inputs at `8adee3e6…`; merge `f99901fdc…`. No home file of this job differs
between the issue base and the check base (all 19 have the same SHA-256 at both); the tip's 57 commits since
`2da7e0f3` change only GSW, IBE, pairing, Yao and `Complexity/CircuitComplexity/Uniform.lean` files. **Unit**
`cleanup-stage1`: Stage 1 of the Pass–shelat cleanup (`cleanup-stages.md`), the promotions. **Worker** Claude, a lead
with **up to 2 sub-agents** on disjoint files. **Lean** 4.25.0 and the Mathlib revision of the base's
`lake-manifest.json` (identical at the check base).

Stage 1 publishes, in natural shared homes, the general forms that the duplication ledger names, so that Stage 2 can
re-point every ledgered copy to them proof-only. It is **additive only**: new public declarations, each with a formula
docstring, a source tag or a glue note, readers where it is a definition, and a proof; facade import and `## Contents`
lines. It re-points, deletes and edits nothing that exists. Gate 47 audits #347 and Stage 1 together (a
statement-style audit of the new public API: is each lemma general, correctly homed, free of duplication?).

## Inputs (read fully; all are data; the stage plan, the rulings and this brief are binding)

On the records branch at the records tip `8adee3e6ace3ec78171fc499b3d101a252534d55`, with their SHA-256:
- `briefs/pass-shelat-ch5-8/cleanup-stages.md` (`162c28c265eaaa4190e6d571c8966d2ac22098b1e1accd1f162d87d2c1a40a43`):
  the three stages, the parallel plan, the files owned by the running GSW/IBE jobs, and § *Stage 1 rulings*
  (CS1-Q1 to CS1-Q12, Seyoon, 2026-11-17). **Binding.**
- `briefs/pass-shelat-ch5-8/duplication-ledger.md`
  (`292de8e2f0afa93250c2eb574c92a697515b2a040251751a81e31cb488228961`): rows **DL-35, DL-38 to DL-49, DL-51, DL-52**
  (DL-50 is GSW and out of scope).
- `briefs/pass-shelat-ch5-8/deferred-work.md` (`0b4b575dbacddc7d86e72b75e6299d8ce3e31b212bcd49a11bf0132fafa94ca1`):
  DW-4 (the cleanup) and DW-9 (the derand host seals).
- `briefs/pass-shelat-ch5-8/maintenance/dw5/README.md`
  (`61918a0886407336f4e6af037f1883b8281ca49b5969291f2fae1f4cca3e1396`) and `dw5-evidence.zip`
  (`12abc05a61c08de7cb38b9d3bccdea5b3dd44dff6f65f036a50584a39e1dd630`): #347's readers, its seal results, and its
  tools (`dw5/tools-used/`).
- `policy.md` (`6599b12230e3879bc0e1fb22c0376ea6201bca8b7edd79dfc55da43986f991d4`): §1 (layout, homes, *Definitions
  land with their lemmas*, reducible abbreviations, *Hosts come first*, *Duplication*), §2 (statement prose, tags,
  deviations), §3 (sketches).
- `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2, the standing rules
  (`d328d0d6e844b3429c0c500b5cdaad72f947c5941d56535362176ead25df9666`).
- `workflow.md` on `main` (`a954201d421a61994e02e36ff3cf4b16dce53f5d`; fetch `main` by name and read it with
  `git show`), §4.1 (the delivery payload) and §6.1 (merged-tree replays)
  (`917afe65ee154faea862905041d78a83bbb42b6738e0bcff5168a618bc7a8b83`).
- `briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py`
  (`fa81981add5de30d3a98b7e1614e73b17f149723e8be79558ac1a29b6fe67fbc`).

On `exchange/pass-shelat-ch5-8` at `6a9b6e19f908bbcd666c0460fa5fea54f20c1e7b`, the worker requests behind the ledger:
- `inbox/fills/cca2-ett/REPORT.md` §4 (`34f769d043fc64ffac4da14b571a15748847e1d630a352a3257c0337e3f196ab`): DL-40;
- `inbox/fills/ext-nosrc/evidence/promotion-requests.md`
  (`28cf9b984067704b43e460fa0e22cecc527b6876a2d50226b3d8e43768dfb117`): DL-39;
- `inbox/fills/dl-crh/evidence/PROMOTION.md` (`36b3ef40c1aac88d8986a31dc8eee8d38e1d437009fe79f2ec8add13b84450dc`):
  DL-41;
- `inbox/fills/bb1-machine/evidence/tools/`: the seal, control, scan and build tools of the latest fill (as in DW-5).

## Binding rules for this stage (Seyoon, 2026-11-16/17; `cleanup-stages.md`, the ledger rulings)

- **Additive only.** Every change to an existing file is a pure insertion of new declarations, of a section header
  that holds them, of a module-docstring bullet that lists them, or (facades, and the one new import of
  `Games.lean`/`ZeroKnowledge.lean`) of an import line. No existing declaration, statement, proof, attribute,
  docstring or import line changes; nothing is deleted or moved. The insertion check (*Checks*, 5) proves it.
- **No re-pointing.** No existing copy is re-pointed to its promoted form, even where it is one line: that is Stage 2.
  The new forms have no consumer in the library after Stage 1; that is expected.
- **Every new public declaration** has a docstring that opens with its statement in words and states its formula; a
  `[Tag, location]` where the result has a source, otherwise a one-line glue note ("framework glue, no textbook
  counterpart", policy §2); readers when it is a definition (policy §1: an `_apply`/`_eq` equation or case lemmas
  covering every input, no `@[simp]`); and a proof (no `sorry`). Proofs of 15 lines or more carry a
  `**Proof sketch.**`.
- **Forbidden files** (the running GSW/IBE jobs own them): `TCSlib/Cryptography/Games/Probability.lean`,
  `Games/Relational.lean` (it does not exist yet; bb1-sim creates it), `Pairing/Group.lean`,
  `TCSlib/Complexity/CircuitComplexity/**`, `TCSlib/Complexity/BranchingPrograms/**`, `ComputationalModels.lean`,
  `machine-library-design.md`, and `TCSlib/Cryptography/AdvancedEncryption/**`. Do not edit them; importing them is
  fine. The DL-40 averaging bound (`abs_expect_sub_le_expect`) is promoted by bb1-sim into `Games/Probability.lean`:
  it is **not** part of this job. Facade import lines may be edited (they merge as unions); this job's facade
  insertions are placed so that they do not touch bb1-sim's anchors in `Games.lean` (after line 9 and line 42).
- **Names that already exist.** A new declaration whose short name already names a declaration anywhere in TCSlib at
  the check base (any namespace, public or private) is declared **`protected`** (the table marks them `P`). This keeps
  every existing unqualified reference resolving as before: Lean resolves a short name through the enclosing
  namespaces first and through `open` only when that fails, and a `protected` name is never found by its short name.
  The shadow scan (*Checks*, 11) proves it.
- **Hosts come first** (policy §1): this job introduces no host. The `fwdHandler` generalization of DL-42 is a host
  change and is not in this job (CS1-Q4).
- Standing rules: readers only (Rule 10: no foreign TCSlib definition passed to `simp`, `rw` or `unfold` or read by
  `rfl`/`show`; core and Mathlib definitions may reduce in `rfl`, `decide` or `show` steps only); line width at most
  100; no `@[simp]`; one Lean process at a time; `python3 -I`; full 40-character hashes from `git rev-parse`.

## Rulings CS1-Q1 to CS1-Q12 (Seyoon, 2026-11-17; `cleanup-stages.md` § *Stage 1 rulings*; binding)

The maintainer's staging asked twelve questions where the ledger left the resolution open. Seyoon ruled; nine follow
the recommended option, three (Q2, Q8, Q9) changed it. This brief implements the rulings.

| # | Ruling | Effect here |
|---|---|---|
| CS1-Q1 | Include DL-39: the 14 `FinDist` facts, protected, in `InformationTheory/{FinDist,Samples,Entropy}.lean`. The wider ext-nosrc request list (uniform-sampler layer, `take_poly`, the selector and block families) stays deferred. | S1-23 to S1-25 are in scope. |
| CS1-Q2 | **Changed.** The six statement/body changes are approved now; Stage 2 removes **both** DL-35 aliases of `blocks` (the private one in `Ensembles.lean` and the public one in `EnsemblesLemmas.lean`); the gate checks the six changes explicitly. | Stage 1 unchanged (S1-09). The six changes are named in *Stage 2 handover*. |
| CS1-Q3 | Stage 2 moves `MachineCodec.ext_of_fields` verbatim to `Games/Machines`. | No Stage 1 target; *Stage 2 handover*. |
| CS1-Q4 | The `fwdHandler` generalization is out of the cleanup; hosts change only by their own gated design. | No target. |
| CS1-Q5 | DL-41: the `splitBits` word readers in `Authentication/Encoding.lean`; no bridge. | S1-11. |
| CS1-Q6 | DL-48: `NUPPT.length_ofFn_coins` in `Complexity/Randomized/PPT.lean`, beside `Coins`. | S1-16. |
| CS1-Q7 | DL-51: `StatClose.of_uprob_ne` in `Asymptotic/Sampling.lean`. | S1-22. |
| CS1-Q8 | **Changed.** DL-49's ThreeColoring helpers go to a shared machine layer that both `ThreeColoring/Machines` and `ComposeSecurity/Machines` can import, additively in Stage 1; Stage 2 re-points both sides. | S1-26, S1-27 (home `ZeroKnowledge/EncodingMachines.lean`), reconciled with S1-19/S1-20 (one home per lemma). |
| CS1-Q9 | **Changed.** DL-43's `mul_prob_le_expect` is **not** in Stage 1: it goes to `Games/Probability.lean` in Stage 2, after the bb1-sim Games PR merges, as a noted additive exception; Lamport is then re-pointed. | S1-13 withdrawn; `Games/Hopping.lean` is not changed; *Stage 2 handover*. |
| CS1-Q10 | Near relatives that are not instances get no target; they stay as notes. | No target. |
| CS1-Q11 | Promotion requests with no ledgered copy are declined for now. | No target. |
| CS1-Q12 | DL-47: the Complexity-side inline chains stay; only the Cryptography-side copies are re-pointed. | S1-15's Stage 2 list. |

The near relatives of CS1-Q10 are: `PRFGame.ovr` (a lookup over the lazy state, `OracleFromPRF/Lazy.lean:102`),
`AdaptiveCPA.tapeImpl`/`simulate_tapeImpl_congr` (one lazily sampled index, `AdaptiveCPA/Hybrid.lean:116`, `:170`),
`HashSignFill.expect_simulate_sample_once` against `Games.expect_simulate_eager`, `PRFMAC.blocks`/`macState`/
`hits_nil_iff` against `GGMRed.tblEnc`/`lookup` (DL-44 F-03), `residueFinEquiv`/`boundedInputEquiv` against Mathlib's
`ZMod.finEquiv`/`Fin.snocEquiv` (DL-41), `flip0`/`flipAt` against `BooleanAnalysis.flipBit` (DL-45),
`Blocks.flatten_ofFn_update` against `CommitmentLemmas.ofFn_update_eq` (DL-43). The declined requests of CS1-Q11 are
DL-48's `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le` and cca2-ett's `logCount`,
`length_logCount_encodeLog`, `buildComp_cap`, `exists_capMachine`, `exists_halfMachine`. A worker who meets a further
open question does not decide it: it follows this brief and reports (`CS1-W1`, …).

## Feasibility and size (maintainer's assessment)

One job, feasible in one long session. **69 new declarations**, of which 7 are definitions with their readers; about
**850–1,050 Lean lines**: the new `Games/Tapes.lean` about 300–350 (the generic ETT tools restated in `Games`, with
their proofs), the new `ZeroKnowledge/InteractionWords.lean` about 50–70, about 120–150 in
`ZeroKnowledge/EncodingMachines.lean` (S1-27), and insertions of 5–60 lines in the other 16 existing files. Almost every proof exists already in a copy (cited per target); the work is
restating it in the general home and re-proving it there from that home's readers. The long steps are mechanical:
the bootstrap of the 847-module order, a 495-module sweep at the head (the changed homes include `Randomized/PPT`,
`Foundations/BitLists`, `Asymptotic/Adversary` and `InformationTheory/FinDist`, so almost every downstream module
rebuilds), and the canonical seals of 19 owners in four variants. One Lean process at a time, for all agents.

**Size concerns.** `Asymptotic/Sampling.lean` has 936 lines; S1-22 adds about 25 (keep it under 1000, or report).
`ZeroKnowledge/EncodingMachines.lean` grows from 694 to about 830.
The two DW-9 owners carry 26 pre-existing seal failures (`ModuleHost` 10, `IterateFindHost` 16; DW-5's README), which
the canonical seals of `IterateFindHost` will show again: they are Stage 2's, and this job attributes them to the base.

## Branches, checks tree and delivery

- **Checkout.** In your own clone, fetch `cleanup/dw5-derand-readers` and `cryptography/pass-shelat-ch2-4` by name.
  Check `git rev-parse FETCH_HEAD`/the branch heads: the issue base `daa6e173cdd94cad1475b9a96eca613bce53ba61` and the
  records tip `8adee3e6ace3ec78171fc499b3d101a252534d55` or a descendant. Merge `f99901fdc98f4c7703cf9485329600311a1ea655`
  (an ancestor of the records tip, with the same Lean sources) into the check tree, whatever the records tip is
  then; if a later records commit changes a `.lean` file, say so (the maintainer re-replays at landing).
- **The branch** `cleanup/stage1-promotions`, from the issue base. Suggested commits, each compiling at the check tree:
  1. `cleanup stage1: DW-9 view versions of the host control steps` (S1-01 to S1-03);
  2. `cleanup stage1: Games forms of simulation in law, coin tapes and tables (DL-40, DL-41, DL-42)` (S1-04,
     S1-05, S1-10, S1-12, the `Games` facade);
  3. `cleanup stage1: bit-list, coin, encoding and closeness readers (DL-35, DL-40, DL-41, DL-46, DL-47, DL-48, DL-51)`
     (S1-06 to S1-09, S1-11, S1-14 to S1-17, S1-22);
  4. `cleanup stage1: history encoding and the shared machine helpers (DL-38, DL-45, DL-49)` (S1-18 to S1-21, S1-26,
     S1-27, the `ZeroKnowledge` facade);
  5. `cleanup stage1: finite-distribution facts (DL-39)` (S1-23 to S1-25).
  Commit with `git -c commit.gpgsign=false`; keep the branch local.
- **The check tree** (local only, never delivered): `git checkout -b check/stage1-merged daa6e173…` and
  `git merge --no-ff f99901fdc…`; its tree must be `01cc6259480ccc9372181cd4d18d4511c87aa048` (record it). Every build,
  sweep, seal, axiom print and control runs here, with the Stage 1 commits applied on top (`git cherry-pick` or
  `git merge` of the branch head). At the end, `git merge-tree --write-tree f99901fdc… <stage1 head>` must equal the
  check head's tree (record both), so the evidence is the maintainer's merged-tree replay (`workflow.md` §6.1).
- **Deliver** every checkpoint and the final only under `inbox/fills/cleanup-stage1/` on `exchange/pass-shelat-ch5-8`,
  in the standard payload (`workflow.md` §4.1):
  - `REPORT.md` (*Report*);
  - `patches/`: `git format-patch daa6e173…..cleanup/stage1-promotions`, with `COMMITS.tsv` (one row per commit:
    hash, author name, email and date, committer name, email and date, and its **signing**, `none` or the format), so
    that `git am` at the issue base reproduces every hash; check the reproduction in a scratch clone before you push
    and say so;
  - `src/`: every new or changed file at the branch head, under its repository path;
  - `evidence/`, with its manifest `evidence/SHA256SUMS`;
  - a top-level `SHA256SUMS` of every delivered file except itself. The delivered paths must **equal** the manifests'
    paths: nothing missing, nothing extra, no leading `./`. Check before each push.
- Commit on the exchange as `fill cleanup-stage1: checkpoint N` and `fill cleanup-stage1: final`. Pull with rebase
  before pushing; push only your path; never force-push; never touch another path (other fills, gates,
  `arora-barak-ch3-4/`, `lwe-sis-constructions/`). Never push a campaign branch. If a push is refused, keep the
  commit and say so.
- **Checkpoint 1** as soon as every target's statement elaborates at the check tree (proofs may still be `sorry` at
  the checkpoint only): the `StmtDump` of all new constants, decls2, the shadow scan and the reuse table. It feeds the
  Stage 1 gate early. The final has everything, with no `sorry`.

## Base and parallel work

- **#347** (DW-5) is open and is the issue base: Stage 1 is stacked on it (DW-9's view versions live in its host
  files). The two merge together or #347 first.
- **The GSW/IBE jobs** run in parallel and own the forbidden files. The bb1-sim statement job edits `Games.lean`
  (import after line 9, `## Contents` entry after line 42), `Games/Probability.lean` and `Pairing/Group.lean`, and
  creates `Games/Relational.lean`. This job's `Games.lean` insertions are after line 11 and line 47.
- **The PS10 ch. 5–8 ingest** (docs only) runs in parallel; this job adds no blueprint or reference file.
- **Stage 2** (after Stage 1 and the bb1-sim Games PR merge) re-points every copy listed in the target tables; it is
  why each target lists its copies with `path:line`. Lines are at the records tip `f99901fdc…` (equal at the check
  base), except `IterateFind.lean`, which is at the issue base.

## Scope

**The branch may change exactly** (lines and SHA-256 at the issue base, equal at the check base):

| File | Lines | SHA-256 | Permitted change |
|---|---|---|---|
| `TCSlib/Complexity/Randomized/Build/IterateFindHost.lean` | 390 | `3cc80298eb7384b489c8b56b5bf0f8329e629d964191f527a13fa5c61ddd89ef` | S1-01–03 after line 388 (end of `host_halt`), before `end Complexity.IterateFind`; `## Main results` bullet |
| `TCSlib/Complexity/Randomized/PPT.lean` | 486 | `97248e5603fc118c4343d564b60747bddba1443fa86c3ea60e74018e95da63ff` | S1-16 after `Coins` (line 222); bullet |
| `TCSlib/Cryptography/Foundations/BitLists.lean` | 192 | `79be625b3c19ad313f6998e58266be2ea1ee38e4b0b639755872db96aad82802` | S1-15 after `headD_drop_ofFn`; S1-06 after `zipWith_xor_cancel_left`; S1-07 in a new section; bullets |
| `TCSlib/Cryptography/Asymptotic/Adversary.lean` | 452 | `9ab69ef62a368c35c818fc1a4e65b36370df35bc4023f10d5641bead6edae7c3` | S1-09 after `FunFamily.ofFn_blocks`; bullet |
| `TCSlib/Cryptography/Asymptotic/Sampling.lean` | 936 | `353f3dd6e00625151a7d01c14b550fa84fab1f1e3b9c5f9da80ee28cba401c8a` | S1-22 in `section StatClose`; bullet |
| `TCSlib/Cryptography/Authentication/Encoding.lean` | 47 | `d9ebad935ac9fb11fc0133237502cc32befc5c8de0dc8534736aa6f026c400ce` | S1-11 after the `simps` attribute of `splitBits`; `## Main results` line |
| `TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean` | 340 | `077525a8b0ef06acf2df7e5a19afb201db04ca77b3f275476cae14495ee8f129` | S1-14 after `encodeList_nil` (line 141); bullet |
| `TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean` | 570 | `538a16cf4d148be7a65027634680c3d274d304af725476f2ded8c7a33419e419` | S1-17 after `pkPredictor` (line 283); bullet |
| `TCSlib/Cryptography/Games/Machines.lean` | 278 | `f5f17670a3b12d009bddb56ac2e1a9be7b58facf2a27aa860bc64cd91637fd36` | S1-12; bullet |
| `TCSlib/Cryptography/Games/Efficiency/Strings.lean` | 570 | `2795eaeeb0a03b125f9433c1c5e21784b379569c66e6becd24b97c41aadb423f` | S1-05 after `length_encodeLog_le`; bullet |
| `TCSlib/Cryptography/Games/Bridges/Experiments.lean` | 136 | `e2f7b36536c12b6cff3f91a8ba3e434952515c87e09867cac85b231a14a9735f` | S1-10 after `prob_sample_eq_uprob`; bullet |
| `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean` | 480 | `22f1839835c70ff61593671a58651049616541e509eb52678a8f8fdc86c4c8c2` | S1-08 after `toOracleAdversary_boundedBy` (line 339); bullet |
| `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean` | 565 | `e41ec92da068e10d5f35278fe7b23c2f757c3997df5194c28c30cd3e0823f4ab` | S1-18–20 and S1-26 after `pairFstD_encodeMsgs`; bullets |
| `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean` | 694 | `9996b7e0938a90433d7cdc3c667f9c66118604f01090c7019099f195cb6c3474` | S1-27 in a new section before `end TCSlib.Cryptography.EncodingMachines` (line 694); bullets |
| `TCSlib/InformationTheory/FinDist.lean` | 200 | `e17e81d5ecfaccbfd548018f00ad9298c705c263d14f2e4b5792d5dc0351eeb6` | S1-23; bullet |
| `TCSlib/InformationTheory/Samples.lean` | 155 | `67d09a767a7d4a07fe81e17444ff904fde10deeba9a82977234405a4d39d6a72` | S1-24; bullet |
| `TCSlib/InformationTheory/Entropy.lean` | 215 | `7bc4054d47022caa7c39314345e7e72e80b2498176c365efc643045f48200037` | S1-25; bullet |
| `TCSlib/Cryptography/Games.lean` | 64 | `dd67d6952d872a95cc03e34f477dace41bcfb96d50a79daa383064a7d64f2693` | `import TCSlib.Cryptography.Games.Tapes` after line 11; `## Contents` entry after line 47 |
| `TCSlib/Cryptography/ZeroKnowledge.lean` | 67 | `ae88d10a0e728953fec3a829fe17bf7200cec922b650d49afe82c1c4bbbdd918` | `import TCSlib.Cryptography.ZeroKnowledge.InteractionWords` after line 7; `## Contents` entry after line 41 |
| `TCSlib/Cryptography/Games/Tapes.lean` | new | | S1-04; imports `TCSlib.Cryptography.Games.Hopping` only |
| `TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean` | new | | S1-21; imports `ZeroKnowledge.Interaction` and `Complexity.ClassP.BinaryArith.Words` only |

"Bullet" means one `## Main results` (or `## Main definitions`) line naming the new declarations. **Frozen:** every
other file, including `ModuleHost.lean`, `IterateFind.lean`, every file that holds a copy, `TCSlib.lean`, the
forbidden files (in particular `Games/Probability.lean`; S1-13 is Stage 2's, CS1-Q9) and `blueprint/`. No new
`import` in an existing non-facade file.
- **Scope requests.** If a target needs any other change (an import, a reader in another file, a statement that does
  not elaborate as written), stop that line and ask Seyoon in your session with the file, the diff and the reason;
  record the request and the answer verbatim under `evidence/scope-request/` and in `REPORT.md`. Prefer routes with
  no frozen-file edit; a statement may be repaired minimally only if the repair keeps every listed copy an instance,
  and the repair is reported under *Statement changes*.

## The targets

Each row gives the exact statement (variables as in the home's section where it says so), its home and namespace,
its readers (for a definition: the readers it lands with; for a theorem: the published readers its proof goes
through, Rule 10), and the copies that Stage 2 re-points to it, as `path:line` (paths under `TCSlib/Cryptography/`
unless they start with `TCSlib/`). `P` marks a `protected` declaration (see *Binding rules*). Proofs: the cited copy's
proof, re-done at the home through that home's readers.

### DW-9: view versions of the host control steps (S1-01 to S1-03)

Home `TCSlib/Complexity/Randomized/Build/IterateFindHost.lean`, namespace `Complexity.IterateFind` (with `open
Turing`), after `host_halt`. `ModuleHost.hostTMView` is #347's reducible typed view, so the configurations type
without reading `hostTM`'s fields. Write `H M K hk` below for
`ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)` (spell it out; no new
abbreviation).

```lean
theorem host_dispatch_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w : List Bool) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w)

theorem host_branch_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
      Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w)

theorem host_halt_view (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w o : List Bool) :
    (ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)).tm.step
        {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
      {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w)
        with state := none, output := o}
```

- **Readers (proofs go through):** `ModuleHost.hostTMView_step_inl`, `hostCtrl_eq`, `Cfg.ofWords_state`,
  `Cfg.ofWords_def`, `Cfg.workTapeSymbols_eq`, `Cfg.ofWords_workTapes`, `Cfg.ofWords_workTapePos`, `stateWord_eq`,
  `FinTM.bufferTape_eq`, `FinTM.controlAction_apply`, `moveInputPos_zero`: exactly the proofs of `hdisp`, `hbranch`,
  `hhalt` in E1 (`TCSlib/Complexity/Randomized/Build/IterateFind.lean:373–396` at the issue base), which pass the
  seals there. The new statements and proofs must add **no** seal failure to `IterateFindHost` (its 16 pre-existing
  ones, 10 of them in the statements of `host_dispatch`/`host_branch`/`host_halt`, stay and are Stage 2's).
- **Tags:** glue (the host's control table; the module cites [PS10] and [AB09] already). Docstrings state the step
  formulas, as `host_dispatch`'s do, and say that they are the typed-view versions.
- **Stage 2:** `TCSlib/Complexity/Randomized/Build/IterateFind.lean:373` (`hdisp`), `:378` (`hbranch`), `:390`
  (`hhalt`), in `computesFunInTime_find`, at the issue base. The unused originals
  `TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:352`, `:364`, `:380` are DW-9's to delete or restate.

### DL-40: simulation in law, coins in advance and tables, in `Games` (S1-04)

New module `TCSlib/Cryptography/Games/Tapes.lean`, namespace `TCSlib.Cryptography.Games` (with
`open ProbComp`), importing `TCSlib.Cryptography.Games.Hopping` only. Title "Simulation in law, coins in advance,
and functions overridden by a table". It restates, generically and in `Games`, the content of
`Encryption/PrivateKey/EncryptThenTag/Tools.lean` (the module says these are "candidates for promotion to the `Games`
layer"), with `AdaptiveCPA.extTape` replaced by a `Games` copy. Every declaration is `P` (each short name exists in
`ETTGame` or `AdaptiveCPA`). Statements, with `variable {ι : Type} {spec : OracleSpec ι} {σ σ₁ σ₂ τ α : Type}` and,
for the table section, `variable {κ β : Type} [DecidableEq κ]`:

```lean
protected theorem expect_simulate_abs (impl₁ : QueryImpl spec σ₁ unifSpec)
    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
    (hcnt : ∀ i x s, cnt s < κ → (impl₂ i x s).AllOutputs fun p => cnt p.2 ≤ cnt s + 1)
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2)

protected theorem expect_simulate_abs_inv (impl₁ : QueryImpl spec σ₁ unifSpec)
    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (P : σ₂ → Prop) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, P s → cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
    (hcnt : ∀ i x s, P s → cnt s < κ →
      (impl₂ i x s).AllOutputs fun p => P p.2 ∧ cnt p.2 ≤ cnt s + 1)
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂) (hP : P s)
    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2)

protected noncomputable def freshImpl [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) : QueryImpl spec σ unifSpec :=
  fun i x s => (sample τ).bind (K i x s)
protected theorem freshImpl_apply [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (i : ι) (x : spec.dom i) (s : σ) :
    Games.freshImpl K i x s = (sample τ).bind (K i x s)

protected noncomputable def extTape {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) (m : ℕ) : C :=
  if hm : m < κ then T ⟨m, hm⟩ else Classical.arbitrary C
protected theorem extTape_of_lt {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) {m : ℕ}
    (hm : m < κ) : Games.extTape T m = T ⟨m, hm⟩
protected theorem extTape_of_not_lt {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) {m : ℕ}
    (hm : ¬ m < κ) : Games.extTape T m = Classical.arbitrary C
protected theorem extTape_update {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) (j : Fin κ)
    (r : C) {m : ℕ} (hm : m ≠ j) : Games.extTape (Function.update T j r) m = Games.extTape T m

protected def tapeImpl (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ) :
    QueryImpl spec (σ × ℕ) unifSpec :=
  fun i x s => (K i x s.1 (T s.2)).bind fun p => .pure (p.1, (p.2, s.2 + 1))
protected theorem tapeImpl_apply (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (T : ℕ → τ) (i : ι) (x : spec.dom i) (s : σ) (j : ℕ) :
    Games.tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => .pure (p.1, (p.2, j + 1))
protected theorem simulate_tapeImpl_congr (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (T T' : ℕ → τ) (c : OracleComp spec α) (s : σ) (j : ℕ) (hT : ∀ m, j ≤ m → T m = T' m) :
    simulate (Games.tapeImpl K T) c (s, j) = simulate (Games.tapeImpl K T') c (s, j)
protected theorem expect_simulate_tapeImpl [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (κ : ℕ) (G : α → ℝ) (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m)
    (s : σ) (j : ℕ) (hj : j + m ≤ κ) :
    expect (sample (Fin κ → τ))
        (fun T => expect (simulate (Games.tapeImpl K (Games.extTape T)) c (s, j)) fun p => G p.1) =
      expect (simulate (Games.freshImpl K) c s) fun p => G p.1

protected def ovr : List (κ × β) → (κ → β) → κ → β
  | [], R => R
  | e :: M, R => Function.update (Games.ovr M R) e.1 e.2
protected theorem ovr_nil (R : κ → β) : Games.ovr ([] : List (κ × β)) R = R
protected theorem ovr_cons (p : κ) (y : β) (M : List (κ × β)) (R : κ → β) :
    Games.ovr ((p, y) :: M) R = Function.update (Games.ovr M R) p y
protected theorem ovr_of_not_mem {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst)
    (R : κ → β) : Games.ovr M R p = R p
protected theorem ovr_of_mem {M : List (κ × β)} {p : κ} (hp : p ∈ M.map Prod.fst)
    (R R' : κ → β) : Games.ovr M R p = Games.ovr M R' p
protected theorem ovr_update {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst) (R : κ → β)
    (y : β) : Games.ovr M (Function.update R p y) = Function.update (Games.ovr M R) p y
protected theorem ovr_append (A B : List (κ × β)) (R : κ → β) :
    Games.ovr (A ++ B) R = Games.ovr A (Games.ovr B R)
protected theorem expect_sample_ovr [Fintype κ] [Fintype β] [Nonempty β] (M : List (κ × β))
    {p : κ} (hp : p ∉ M.map Prod.fst) (F : β → (κ → β) → ℝ) :
    expect (sample (κ → β)) (fun R => F (R p) (Games.ovr M R)) =
      expect (sample β) fun y =>
        expect (sample (κ → β)) fun R => F y (Games.ovr ((p, y) :: M) R)
```

- **Readers:** the definitions land with `freshImpl_apply`; `extTape_of_lt`, `extTape_of_not_lt` (the two cases) and
  `extTape_update`; `tapeImpl_apply`; `ovr_nil`, `ovr_cons` (the two constructors). The proofs read the `Games` API
  through `simulate_pure`, `simulate_query`, `expect_pure`, `expect_bind`, `expect_const`, `expect_sample_coord`,
  `expect_expect_sample`, `expect_congr_of_allOutputs`, `OracleComp.costBoundedBy_query`, `OracleComp.bind_assoc`,
  `OracleComp.pure_bind`, as the ETT proofs do; `extTape`'s own body is read only in its own file.
- **Tags:** framework glue; the module's `## References` cites [PS10] as the ETT module does (Theorem 170.4, the
  first consumer), with no declaration-level tag. Docstrings carry the formulas of the ETT copies.
- **Facade:** `Games.lean`, the import after line 11 and a `## Contents` entry after line 47:
  `* TCSlib.Cryptography.Games.Tapes: simulation through a state abstraction in law, coins drawn in advance on
  tapes, and functions overridden by a table.`
- **Stage 2:** `Encryption/PrivateKey/EncryptThenTag/Tools.lean:65` (`expect_simulate_abs`), `:88` (`_inv`), `:116`
  and `:122` (`freshImpl`, `_apply`), `:130` and `:135` (`tapeImpl`, `_apply`), `:145` (`simulate_tapeImpl_congr`),
  `:167` (`expect_simulate_tapeImpl`), `:219`, `:224`, `:228`, `:234`, `:246`, `:262`, `:281` (the `ovr` family and
  `expect_sample_ovr`); `Encryption/PrivateKey/EncryptThenTag/Lazy.lean:175` (`ovr_append`, at `κ = Fin (2n) → Bool`);
  `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:211`, `:215`, `:221` (`extTape` and its two readers); consumer
  `Authentication/MAC/FromPRF/Random.lean:125` (uses `ETTGame.expect_sample_ovr`). `AdaptiveCPA.tapeImpl` and
  `PRFGame.ovr` are near relatives (CS1-Q10).

### DL-40: the remaining general forms (S1-05 to S1-08)

**S1-05** `TCSlib.Cryptography.Games.EffFill.length_le_length_encodeLog` (`P`), home
`Games/Efficiency/Strings.lean`, after `length_encodeLog_le` (the ledger's home):

```lean
protected theorem length_le_length_encodeLog {ι α : Type} {spec : OracleSpec ι}
    (codec : MachineCodec spec α) (h : QueryLog spec) : h.length ≤ (codec.encodeLog h).length
```
- Readers: `MachineCodec.encodeLog_nil`, `MachineCodec.encodeLog_cons`, `length_pairEncode`. Tag: glue.
- Stage 2: `Encryption/PrivateKey/EncryptThenTag/Machines.lean:95` (private) and
  `Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean:108` (private); delete both.

**S1-06** `TCSlib.Cryptography.zipWith_xor_cancel_right` (fresh), home `Foundations/BitLists.lean`, after
`zipWith_xor_cancel_left` (the other orientation):

```lean
theorem zipWith_xor_cancel_right : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
```
- Readers: core `List.zipWith_cons_cons`; Bool cases. Tag: glue.
- Stage 2: `Encryption/PrivateKey/FromPRF.lean:174`, `Encryption/PrivateKey/FromPRG.lean:147`,
  `SecureComputation/SpecialEncryption.lean:101` (private `zipWith_xor_xor_self`),
  `Encryption/PrivateKey/EncryptThenTag.lean:338` (private `zipWith_xor_xor_self'`),
  `Encryption/PrivateKey/EncryptThenTag/Lazy.lean:295` (public `ETTGame.zipWith_xor_cancel`).

**S1-07** `TCSlib.Cryptography.recordBits` and readers (fresh), home `Foundations/BitLists.lean`, a new section
"Records of an optional bit vector":

```lean
def recordBits (w : ℕ) : Option (Fin w → Bool) → List Bool
  | none => false :: List.replicate w false
  | some c => true :: List.ofFn c
theorem recordBits_none (w : ℕ) : recordBits w none = false :: List.replicate w false
theorem recordBits_some (w : ℕ) (c : Fin w → Bool) : recordBits w (some c) = true :: List.ofFn c
theorem length_recordBits (w : ℕ) (o : Option (Fin w → Bool)) : (recordBits w o).length = w + 1
```
- Readers: `recordBits_none`, `recordBits_some` (by `rfl`, the two constructors), `length_recordBits`. Tag: glue.
- Stage 2: `Encryption/PrivateKey/EncryptThenTag/Handler.lean:134`, `:139`, `:143`, `:147` and
  `Encryption/PrivateKey/OracleFromPRF/Handler.lean:109`, `:114`, `:117`, `:121` (`recBits n` is
  `recordBits (ettCt.eval n)`, resp. `recordBits (ctP.eval n)`; their bodies become that, their readers corollaries).

**S1-08** `Complexity.NUPPT.eval_toOracleAdversary_padFin` (fresh), home
`Pseudorandom/Functions/Asymptotic/Defs.lean` (where `NUPPT.toOracleAdversary` is defined), after
`toOracleAdversary_boundedBy`, written `_root_.Complexity.NUPPT.…` as its neighbours are:

```lean
theorem _root_.Complexity.NUPPT.eval_toOracleAdversary_padFin (D : NUPPT) (n q : ℕ)
    (c : D.Coins n) {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b)
    (f : (Fin a → Bool) → (Fin b → Bool)) :
    (D.toOracleAdversary n a b q c).eval f =
      (D.toOracleAdversary n a' b' q c).eval
        (fun x => padFin b' (List.ofFn (f (padFin a (List.ofFn x)))))
```
- Readers: `padFin_ofFn` (after `subst`). Tag: glue. All three copies are instances: `a = b = ℓ`, `a' = b' = ℓ'`
  (ETT); `a = b = n`, `a' = b' = m` with `m = n` (PRF); `a = b = n`, `a' = m₁`, `b' = m₂` (MAC).
- Stage 2: `Encryption/PrivateKey/EncryptThenTag/Machines.lean:348` (`ETTGame.eval_toOracleAdversary_len`),
  `Encryption/PrivateKey/OracleFromPRF/Reduction.lean:228` (`PRFGame.eval_toOracleAdversary_width`),
  `Authentication/MAC/FromPRF/Bound.lean:48` (`eval_toOracleAdversary_width₂`).

Not in this job (DL-40): the averaging bound (bb1-sim); the private `prfAdv_prfReduction`
(`Encryption/PrivateKey/OracleFromPRF.lean:286`), which Stage 2 re-derives from the public
`TCSlib.Cryptography.prfAdv_eq_expect` (#314, `Pseudorandom/Functions/Defs.lean:118`); the requests without a copy
(CS1-Q11); `PRFGame.ovr` and `AdaptiveCPA.tapeImpl` (CS1-Q10).

### DL-35: the canonical block reader (S1-09)

**S1-09** `TCSlib.Cryptography.FunFamily.ofFn_blocks_symm_eq_flatMap` (fresh), home `Asymptotic/Adversary.lean`, after
`FunFamily.ofFn_blocks` (upstream of `EnsemblesLemmas`, which does not import `OneWay`, the home of the `flatten`
form `FunFamily.ofFn_blocks_symm`):

```lean
theorem FunFamily.ofFn_blocks_symm_eq_flatMap {q ℓ : ℕ} (V : Fin q → Fin ℓ → Bool)
    (F : ℕ → List Bool) (hF : ∀ i (h : i < q), F i = List.ofFn (V ⟨i, h⟩)) :
    List.ofFn ((FunFamily.blocks q ℓ).symm V) = (List.range q).flatMap F
```
- Readers: `FunFamily.blocks_symm_apply`, Mathlib `List.ofFn_mul`, `finProdFinEquiv` arithmetic. Tag: glue (the
  block encoding of [PS10, Theorem 35.1] is cited at `FunFamily.blocks`).
- Stage 2 (CS1-Q2, changed: both aliases go): the six approved statement/body changes, the alias removals and the
  remaining alias uses are listed in *Stage 2 handover*, item 1. Stage 1 itself only adds S1-09.

### DL-41 and DL-44 F-02: the sample bridge and the `splitBits` words (S1-10, S1-11)

**S1-10** `TCSlib.Cryptography.Games.Bridge.expect_sample_eq_uexp` (`P`), home `Games/Bridges/Experiments.lean`,
after `prob_sample_eq_uprob` (its probability form):

```lean
protected theorem expect_sample_eq_uexp {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) :
    expect (sample α) f = uexp f
```
- Readers: `ProbComp.expect_sample`, `uexp_def`. Tag: glue.
- Stage 2: `Hashing/FromDiscreteLog/Probability.lean:40` (`FromDiscreteLog.expect_sample_eq_uexp`; needs the import of
  `Games.Bridges.Experiments`, which it lacks).

**S1-11** `TCSlib.Cryptography.Authentication.ofFn_splitBits_fst` and `…_snd` (`P`), home
`Authentication/Encoding.lean` (CS1-Q5), after `attribute [simps …] splitBits`:

```lean
protected theorem ofFn_splitBits_fst {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).1 = (List.ofFn w).take a
protected theorem ofFn_splitBits_snd {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).2 = (List.ofFn w).drop a
```
- Readers: `splitBits_fst`, `splitBits_snd` (the file's own `simps` projections); Mathlib `List.ofFn_add`,
  `List.take_left'`, `List.drop_left'`. No new import. Tag: glue.
- Stage 2: `Hashing/FromDiscreteLog/Encoding.lean:45`, `:55` (the public `FromDiscreteLog` copies, re-derived);
  `Authentication/MAC/FromPRF/Reduction.lean:140`, `:145`, `:147` (`decide_fnForge`'s `hw`, `htake`, `hdrop`,
  DL-44 F-02). Also DL-41's `inputWord_split`/`inputWord_take` are already re-pointed (#307).

### DL-42: the cost fact (S1-12); DL-43 is Stage 2 (S1-13 withdrawn)

**S1-12** `TCSlib.Cryptography.Games.OracleComp.exists_eq_pure_of_costBoundedBy_zero` (fresh), home
`Games/Machines.lean` (the ledger's home):

```lean
theorem OracleComp.exists_eq_pure_of_costBoundedBy_zero {ι α : Type} {spec : OracleSpec ι}
    (c : OracleComp spec α) (h : c.CostBoundedBy (fun _ => 1) 0) : ∃ a, c = .pure a
```
- Readers: `OracleComp.costBoundedBy_query`. Tag: glue.
- Stage 2: `Authentication/Signatures/HashAndSign/OneQuery.lean:36` (`HashSignFill.eq_pure_of_cost_zero`),
  `Authentication/Signatures/Lamport/Planted.lean:226` (`exists_pure_of_cost_zero`). The codec fact moves in Stage 2
  (CS1-Q3); the `fwdHandler` generalization is out of the cleanup (CS1-Q4).

**S1-13 is withdrawn** (CS1-Q9). DL-43's general averaging lemma `ProbComp.mul_prob_le_expect` belongs in
`Games/Probability.lean`, which the GSW/IBE jobs own now; Stage 2 adds it there as a noted additive exception after
the bb1-sim Games PR merges (*Stage 2 handover*). This job does **not** add it anywhere, and does not change
`Games/Hopping.lean`. The reuse search (check 12) still records the existing relatives (`HardcoreBit.uprob_mul_le_uexp`,
`HardcoreBit/Basic.lean:142`; the Lamport copy `Authentication/Signatures/Lamport/Averaging.lean:129`) for Stage 2.

### DL-46, DL-47, DL-48, DL-51: encodings, entries, coins, closeness (S1-14 to S1-17, S1-22)

**S1-14** `TCSlib.Cryptography.PrivateKeyScheme.encodeList_eq_flatMap` (`P`), home
`Encryption/PrivateKey/EnsembleSecurity.lean`, after `encodeList_nil` (beside the definition, the ledger's home):

```lean
protected theorem encodeList_eq_flatMap (l : List (List Bool)) :
    encodeList l = l.flatMap fun c => pairEncode c []
```
- Readers: `encodeList_nil`, `encodeList_cons`, `pairEncode_eq` (`TCSlib/Complexity/TuringMachine/Encoding.lean:141`).
  Tag: glue.
- Stage 2: `Asymptotic/BlockEncryptor.lean:60` (public `TCSlib.Cryptography.encodeList_eq_flatMap`),
  `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean:65` (public `MultiMsg.encodeList_eq_flatMap`),
  `Encryption/PrivateKey/FromPRF.lean:251` (private, unused; the frozen-file exception of DL-46).

**S1-15** `TCSlib.Cryptography.getD_ofFn` (fresh; no `List.getD_ofFn` in core or Mathlib at this pin), home
`Foundations/BitLists.lean`, after `headD_drop_ofFn` (the G32-01 plan):

```lean
theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) (d : α) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩
```
- Readers: `headD_drop`, `headD_drop_ofFn` (its proof: `rw [← headD_drop]; exact headD_drop_ofFn f ⟨i, hi⟩ d`).
  Tag: glue.
- Stage 2 (headers of the declarations at the tip; inline chains by their enclosing declaration):
  - onto `headD_drop_ofFn`: `Pseudorandom/NextBit.lean:454` (inline); `Foundations/BitLists.lean:88`
    (`headD_ofFn_one`); `ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280` (`headD_ofFn_block`);
    `Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88` (private `eq_const_headD`);
    `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449` (in `step_eq`, `:435`; the exact copy);
    `Asymptotic/HardCoreLoops.lean:260` (`orbit_eq`);
  - onto `getD_ofFn`: `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61` (`GI.getD_ofFn_lt'`),
    `ZeroKnowledge/GraphIsomorphism/Proofs.lean:818` (`GI.getD_ofFn_lt`),
    `ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110` (`GIZK.getD_ofFn_lt`),
    `ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391` (`ColProofs.ofFn_getD_lt`),
    `SecureComputation/Yao.lean:614` (private `getD_ofFn'`), `:620` (`yaoBobTables_yaoMsg`),
    `ZeroKnowledge/ThreeColoring/Simulator.lean:861` (inline, in `statClose_colRealView`, `:813`),
    `ZeroKnowledge/ThreeColoring/Language.lean:423` (private `ofFn_getD_tape`),
    `ZeroKnowledge/Encoding.lean:359` (inline, in `coinTable_ofFn`, `:352`),
    `SecureComputation/Garbling.lean:202` (private `map_range_getD_ofFn`), `:374` (`garbledValues_getD`),
    `SecureComputation/Garbling/CoinBlocks.lean:74` (inline, in `pushesUniform_bits_of_blocks`, `:51`),
    `Encryption/PublicKey/BitwiseCPA.lean:98` (private `ofFn_half`),
    `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72` (private `ofFn_splitHalf_bit`),
    `Encoding/BooleanVector.lean:142` (`expandPoly_encode`), `Hashing/SIS/CollisionOutput.lean:188`
    (`collisionOutputPoly_pairEncode`);
  - forbidden now, for a later window: `AdvancedEncryption/Homomorphic/GSW/Eval.lean:263` (in `eval_encrypts`,
    `:250`; GC-01) and the `TCSlib/Complexity/CircuitComplexity/` copies; Complexity copies: CS1-Q12.

**S1-16** `Complexity.NUPPT.length_ofFn_coins` (`P`), home `TCSlib/Complexity/Randomized/PPT.lean`, namespace
`Complexity.NUPPT` (with its `variable (A : NUPPT)`), after `Coins` (CS1-Q6):

```lean
protected theorem length_ofFn_coins (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n
```
- Readers: `List.length_ofFn`, `coinLen_eq`. Tag: glue.
- Stage 2: `Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41` (`NMSim.length_ofFn_coins`),
  `SecureComputation/ObliviousTransfer/Simulators.lean:210` (`OT.length_ofFn_coins`).

**S1-17** `TCSlib.Cryptography.pkPredictor_apply` (fresh), home `Encryption/PublicKey/Trapdoor.lean`, after
`pkPredictor` (the DL-48 reader the ledger asks to publish; `pkPredictor` has none):

```lean
theorem pkPredictor_apply {α ρ : Type*} (D : α × Bool → ρ → Bool) (flip : Bool) (y : α)
    (c : Bool × ρ) : pkPredictor D flip y c = xor (if D (y, c.1) c.2 then c.1 else !c.1) flip
```
- Readers: none (`rfl`, own file). Tag: [PS10, Theorem 104.4, proof], as `pkPredictor`'s docstring.
- Stage 2: `SecureComputation/ObliviousTransfer/ViewB.lean:71`, `:101` (`OT.uprob_signedPredictor_false/_true`,
  re-derived from `exists_pkPredictor`, `Encryption/PublicKey/Trapdoor.lean:337`); and DL-48's `OT.splitLen`
  (`SecureComputation/ObliviousTransfer/Simulators.lean:52`, `:57`) becomes `(EnsembleLemmas.coinsEquiv h).symm`
  (`Asymptotic/EnsemblesLemmas.lean:141`, `:145`) with no new form.

**S1-22** `TCSlib.Cryptography.StatClose.of_uprob_ne` (fresh, CS1-Q7), home `Asymptotic/Sampling.lean`, in
`section StatClose` after `StatClose.mono` (the ledger's home):

```lean
theorem StatClose.of_uprob_ne {σ γ : Type*} [Fintype σ] (X Y : σ → γ) :
    StatClose X Y (uprob fun s => X s ≠ Y s)
```
- Readers: `statClose_iff`, `uprob_mono`, `uprob_or_le`, `OneWay.uprob_congr` (the DDH proof). Tag: glue (the
  coupling bound; its uses are [PS10, Theorem 107.3] in DDH and [PS10, Theorem 163.7] in Yao).
- Stage 2: `Candidates/DDH.lean:145` (`Candidates.statClose_of_uprob_ne`); its users
  `Encryption/PublicKey/ElGamal.lean:1154`; `SecureComputation/Yao/HybridProof/StatisticalSwitch.lean:46`
  (`statClose_of_eq_off`, re-derived with `StatClose.mono` and `uprob_mono`) and `:68` (`distAdv_le_of_eq_off`).

### DL-38, DL-45, DL-49: the history encoding and the shared machine helpers (S1-18 to S1-21, S1-26, S1-27)

Home of S1-18 to S1-20 and S1-26: `ZeroKnowledge/Interaction.lean`, namespace `TCSlib.Cryptography.Strategy`, after
`pairFstD_encodeMsgs` (beside `encodeMsgs`). S1-21 needs `BinArith.encWords`, which `Interaction` does not import
and should not (it would add 14 Complexity machine modules to the closure of every ZK file): it goes in the new
module `TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean`, namespace `TCSlib.Cryptography.Strategy`,
importing exactly `TCSlib.Cryptography.ZeroKnowledge.Interaction` and `TCSlib.Complexity.ClassP.BinaryArith.Words`
(neither imports the other; no cycle). Title "The history encoding as a word list"; `## References` [PS10, §4.4].

```lean
theorem encodeMsgs_eq (h : List (List Bool)) : encodeMsgs h = h.foldr pairEncode []      -- S1-18, fresh
protected theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :                         -- S1-19, P
    encodeMsgs l = l.flatMap fun m => pairEncode m []
protected theorem iterate_pairSndD_encodeMsgs (hist : List (List Bool)) (i : ℕ) :         -- S1-20, P
    pairSndD^[i] (encodeMsgs hist) = encodeMsgs (hist.drop i)
protected theorem msgAt_encodeMsgs (hist : List (List Bool)) (i : ℕ) :                    -- S1-26, P
    pairFstD (pairSndD^[i] (encodeMsgs hist)) = hist.getD i []
-- in InteractionWords.lean:
protected theorem encodeMsgs_eq_encWords (L : List (List Bool)) :                         -- S1-21, P
    encodeMsgs L = Complexity.BinArith.encWords L
```
- Readers: S1-18 is the missing equation lemma of `encodeMsgs` (`rfl`; policy §1). The others go through
  `encodeMsgs_nil`, `encodeMsgs_cons`, `pairEncode_eq` (S1-19), `pairSndD_pairEncode` (S1-20),
  `Strategy.iterate_pairSndD_encodeMsgs` with `pairFstD_encodeMsgs` and core `List.head?_drop`,
  `List.getD_eq_getElem?_getD` (S1-26), and `Strategy.encodeMsgs_eq_flatMap` with `BinArith.encWords_def` (S1-21). Tags: glue. Facade `ZeroKnowledge.lean`:
  the import after line 7 and a `## Contents` entry after line 41: `* InteractionWords — the history encoding as a
  word list (BinArith.encWords).`
- Stage 2:
  - S1-18/S1-19: `Randomness/Learning/Sample.lean:58` (`LearnPRF.foldr_pairEncode_nil`, DL-45);
    `SecureComputation/ComposeSecurity/Machines.lean:150`, `ZeroKnowledge/ThreeColoring/Machines.lean:912`,
    `ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean:503` (the three `encodeMsgs_eq_flatMap`, DL-49);
  - S1-20: `ZeroKnowledge/ThreeColoring/Machines.lean:919`, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean:101`
    (the ZK pair of DL-38);
  - S1-26: `SecureComputation/ComposeSecurity/Machines.lean:137` (`ComposeMachines.msgAt_encodeMsgs`, DL-49) and
    `ZeroKnowledge/ThreeColoring/Protocol.lean:112` (`msgAt_encodeMsgs`, its instance for `i < |l|`, through the
    file's own `msgAt_eq`);
  - S1-21: `SecureComputation/Yao/HybridProof/Lengths.lean:83` (`YaoHybridProof.encodeMsgs_eq_encWords`),
    `Composability/SequentialZK/Normalization.lean:40` (`SequentialZK.encodeMsgs_eq_encWords`);
  - DL-49's other copies re-point to existing public forms (no Stage 1 target):
    `SecureComputation/ComposeSecurity/Probability.lean:110` → `EnsembleLemmas.negligible_polyExpr_mul`
    (`Asymptotic/EnsemblesLemmas.lean:377`; a new import); `SecureComputation/ComposeSecurity/Accept.lean:52`
    (`appendCoins`) → `EnsembleLemmas.coinsEquiv`; `SecureComputation/ComposeSecurity/Runs.lean:71` →
    `FunFamily.ofFn_blocks_symm` (`Asymptotic/OneWay.lean:380`); the ThreeColoring helpers: S1-27.

**One home per lemma (CS1-Q8 reconciled with S1-19/S1-20).** The ruling's list is `encodeMsgs_eq_flatMap`,
`msgAt_encodeMsgs`, the `padTo` family, `polyTimeComputable_flatMap_range`, `flatMap_range_ite` and `iterSnd_poly`.
The two history-encoding facts (`encodeMsgs_eq_flatMap`, S1-19; `msgAt_encodeMsgs`, S1-26) need only `encodeMsgs`, so
their one home is `Interaction.lean`, beside the definition and beside `pairFstD_encodeMsgs` and S1-20, from which
S1-26 follows; DL-45's Learning copy and S1-21 need them there, without any machine layer. The machine helpers (no
`encodeMsgs` in them) have their one home in the shared machine layer, S1-27. No lemma has two homes, and the
machine layer does not restate the encoding facts.

**S1-27, the shared machine helpers.** Home `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean`, namespace
`TCSlib.Cryptography.EncodingMachines` (with its `open Complexity Turing Complexity.StateLoop`), a new section
"Concatenation loops, iterated projections and zero padding" before `end TCSlib.Cryptography.EncodingMachines`
(line 694). **Why this home:** it is the campaign's shared unary FP toolkit (`cstep`, `cstep_iterate`, `cbound`,
`cstep_horbit`, `ltTest_poly`, `unaryLength_poly`, `truncate_poly`, `loopState`, `polyTimeComputable_loopState`,
`polyTimeComputable_of_getD`, `flatMap_range_ite_eq`), which every proof below already uses; both consumers already
import it directly (`ZeroKnowledge/ThreeColoring/Machines.lean:8`, `SecureComputation/ComposeSecurity/Machines.lean:6`),
so Stage 2 needs no new import; it imports neither consumer (no cycle), is not a forbidden file, and stays near 830
lines. A new module would have needed new import lines in both consumers. Both consumers `open TCSlib.Cryptography.EncodingMachines` and keep
same-named copies, so **every S1-27 declaration is `P`**. Statements:

```lean
protected theorem flatMap_range_ite (E : ℕ → List Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then E i else []) =
      (List.range (min N L)).flatMap E
protected theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z)
protected theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
    PolyTimeComputable fun z => pairSndD^[i z] (s z)
protected theorem zeros_poly {L : List Bool → ℕ}
    (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => List.replicate (L x) false
protected def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L
protected theorem padTo_eq (L : ℕ) (w : List Bool) :
    EncodingMachines.padTo L w = (w ++ List.replicate L false).take L
protected theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => EncodingMachines.padTo (L x) (s x)
protected theorem length_padTo (L : ℕ) (w : List Bool) : (EncodingMachines.padTo L w).length = L
protected theorem getD_padTo (L : ℕ) (w : List Bool) {i : ℕ} (hi : i < L) :
    (EncodingMachines.padTo L w).getD i false = w.getD i false
protected theorem padTo_of_length {L : ℕ} {w : List Bool} (h : w.length = L) :
    EncodingMachines.padTo L w = w
```
- **The `padTo` family** is `padTo` with `padTo_eq` (its reader, `rfl`), `padTo_poly`, `length_padTo`, `getD_padTo`,
  `padTo_of_length`, and `zeros_poly`, which `padTo_poly` needs (the ThreeColoring proof's zero word; it is ColMachines'
  statement). The two `ofFn_padFin` copies (`List.ofFn (padFin L w) = padTo L w`) are **not** targets: `padFin` lives
  in `Asymptotic/Adversary.lean`, outside this home's closure, and Stage 2 re-derives both from the existing
  `ofFn_padFin_eq_take` (`Asymptotic/CollectionsLemmas.lean:95`, imported by both consumers) and `padTo_eq`.
- **Readers (proofs go through):** the toolkit lemmas above, `polyTimeComputable_iterateEmit`
  (`TCSlib/Complexity/Randomized/Repetition.lean:351`), `PolyTimeComputable.output_length_le`, `polyTimeComputable_ite`,
  `polyTimeComputable_const`, `PolyTimeComputable.pairEncode`, `pairFstD_pairEncode`, `pairSndD_pairEncode`,
  `length_pairEncode`, `PolyExpr.eval_normal`, `PolyExpr.eval_mono`. `iterSnd_poly`: through
  `polyTimeComputable_loopState` (the ComposeSecurity proof's `GI.iterUnary_poly` and the ThreeColoring proof's
  `polyTimeComputable_loopState'` are not in this home's closure; re-prove, do not import). Proofs over 15 lines carry
  a sketch (the copies' sketches apply). Tags: glue (the module cites its sources already).
- **Stage 2** (both sides, CS1-Q8):
  - `flatMap_range_ite`: `SecureComputation/ComposeSecurity/Machines.lean:61`,
    `ZeroKnowledge/ThreeColoring/Machines.lean:142`, `ZeroKnowledge/ThreeColoring/SimulatorMachine.lean:160`;
  - `polyTimeComputable_flatMap_range`: `ComposeSecurity/Machines.lean:81`, `ThreeColoring/Machines.lean:159`;
  - `iterSnd_poly`: `ComposeSecurity/Machines.lean:117`, `ThreeColoring/Machines.lean:190`;
  - `zeros_poly`: `ThreeColoring/Machines.lean:292`;
  - `padTo` family: `ComposeSecurity/Machines.lean:223` (`padTo`), `:226` (`padTo_eq`), `:232` (`padTo_poly`),
    `:239` (`length_padTo`), `SecureComputation/ComposeSecurity/Assembly.lean:98` (`padTo_of_length`);
    `ThreeColoring/Machines.lean:303` (`padTo`), `:306` (`padTo_poly`), `:312` (`length_padTo`), `:316`
    (`getD_padTo`); re-derived, not targets: `ComposeSecurity/Machines.lean:244`, `ThreeColoring/Machines.lean:327`
    (`ofFn_padFin`);
  - the two `padTo` definitions become `EncodingMachines.padTo` (a body change of a definition; its header is
    unchanged), or are removed with every use re-pointed, as the Stage 2 brief decides.

### DL-39: finite-distribution facts (S1-23 to S1-25; CS1-Q1)

Namespace `TCSlib.InformationTheory`, all `P` (each name exists in `Randomness.Rejection`; several are common Mathlib
short names), with `variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]`. The copies are in
`Randomness/Extraction/Rejection.lean` (DL-39 also re-points `Rejection.tupleEquiv`, `:144`, to Mathlib's
`(Fin.consEquiv _).symm`, with no new form).

S1-23, home `InformationTheory/FinDist.lean` (they need only `FinDist`, `map`, `prod`, `uniform`, `probTrue`):
```lean
protected theorem FinDist.map_uniform_equiv [DecidableEq β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (FinDist.uniform α).map e = FinDist.uniform β                                   -- Rejection.lean:45
protected theorem FinDist.sum_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (∑ b, (p.map f) b * g b) = ∑ a, p a * g (f a)                                   -- :65
protected theorem FinDist.probTrue_nonneg (p : FinDist α) (D : α → Bool) : 0 ≤ p.probTrue D  -- :93
protected theorem FinDist.probTrue_le_one (p : FinDist α) (D : α → Bool) : p.probTrue D ≤ 1  -- :98
protected theorem FinDist.uniform_prod [Nonempty α] [Nonempty β] :
    (FinDist.uniform α).prod (FinDist.uniform β) = FinDist.uniform (α × β)          -- :134
protected theorem FinDist.uniform_probTrue [Nonempty α] (D : α → Bool) :
    (FinDist.uniform α).probTrue D =
      ((Finset.univ.filter (fun a => D a = true)).card : ℝ) * (Fintype.card α : ℝ)⁻¹  -- :343
```
S1-24, home `InformationTheory/Samples.lean` (they need `FinDist.expect`):
```lean
protected theorem FinDist.expect_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (p.map f).expect g = p.expect (fun a => g (f a))                                -- :81
protected theorem FinDist.probTrue_map [DecidableEq β] (p : FinDist α) (f : α → β) (D : β → Bool) :
    (p.map f).probTrue D = p.probTrue (fun a => D (f a))                            -- :88
protected theorem FinDist.map_apply_expect [DecidableEq β] (p : FinDist α) (f : α → β) (b : β) :
    (p.map f) b = p.expect (fun a => if f a = b then 1 else 0)                       -- :104
protected theorem FinDist.map_map [DecidableEq β] [DecidableEq γ] (p : FinDist α) (f : α → β)
    (g : β → γ) : (p.map f).map g = p.map (fun a => g (f a))                        -- :113
protected theorem FinDist.map_prod_snd [DecidableEq β] [DecidableEq γ] {δ : Type*} [Fintype δ]
    [DecidableEq δ] (p : FinDist α) (q : FinDist β) (f : β → γ) (g : α × γ → δ) :
    (p.prod (q.map f)).map g = (p.prod q).map (fun z => g (z.1, f z.2))             -- :122
```
S1-25, home `InformationTheory/Entropy.lean` (it needs `FinDist.IsSource`):
```lean
protected noncomputable def FinDist.mixture (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p q : FinDist α) : FinDist α                                                    -- :395
protected theorem FinDist.mixture_apply (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (p q : FinDist α)
    (a : α) : FinDist.mixture w hw0 hw1 p q a = w * p a + (1 - w) * q a              -- :406
protected theorem FinDist.mixture_isSource (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (p q : FinDist α)
    (k : ℝ) (hp : FinDist.IsSource k p) (hq : FinDist.IsSource k q) :
    FinDist.IsSource k (FinDist.mixture w hw0 hw1 p q)                              -- :413
```
- Readers: `FinDist.ext`, `map_apply`, `prod_apply`, `uniform_apply`, `probTrue_eq`, `expect_eq`,
  `probTrue_eq_expect`, `expect_prod`, `hasMinEntropy_iff`, `isSource_iff_hasMinEntropy` (all public at the homes);
  `mixture` lands with `mixture_apply`. Tags: glue (the copies carry none).
- Stage 2: the `Rejection.lean` lines above.

### Rows with no Stage 1 target

- **DL-38:** besides the ZK pair (S1-20) and the B3 aliases (CS1-Q2), its copies re-point to existing forms:
  `InteractiveHandler.impl_of_query`, `finish_of_ret`, `Games.polyTimeComputable_ansRead`, `FunFamily.ofFn_blocks`,
  `Games.iterEmit` (opportunistic folds, Stage 2).
- **DL-44:** F-01 is paid (#314, #317); F-02 is S1-11; F-03 is CS1-Q10; the private `prfAdv_prfReduction` is Stage 2.
- **DL-45:** items 1–2 are paid (#313); `blk`/`length_blk` (`Randomness/Learning/Sample.lean:88`, `:92`) re-point to
  `MultiMsg.histBlock`/`length_histBlock` (`Encryption/PrivateKey/FromPRF/ReductionMachine.lean:82`, `:91`);
  `foldr_pairEncode_nil` is S1-18/S1-19; `flip0`/`flipAt` are CS1-Q10; the short-name clashes `relabel`/`relabel_eq`
  (DL-36 family) and `flipAt` are renames, outside the cleanup's proof-only Stage 2.
- **DL-52:** Stage 2 derives `SecureComputation/Yao/HybridProof/OTAnswerWords.lean:41`, `:94` from #324's
  `HybridProtocol.length_answersB`/`length_answersA` (`SecureComputation/ComposeSecurity/Lengths.lean:60`, `:52`)
  with `otFunctionality`'s output lengths; no new form.

## Stage 2 handover (recorded here for the Stage 2 brief and its gate; nothing of it is done in this job)

1. **DL-35, both aliases (CS1-Q2, changed).** The six approved changes, each from `EnsembleLemmas.blocks`/the private
   `blocks` to `FunFamily.blocks` (definitionally equal), for the gate to check one by one:
   1. statement of `EnsembleLemmas.exists_copiesRed`, `Asymptotic/EnsemblesLemmas.lean:815` (alias at `:821`–`:823`);
   2. statement of `EnsembleLemmas.ofFn_blocks_symm`, `Asymptotic/EnsemblesLemmas.lean:433` (then a corollary of
      S1-09);
   3. statement of `EnsembleLemmas.take_drop_ofFn_blocks`, `Asymptotic/EnsemblesLemmas.lean:427` (then
      `(FunFamily.ofFn_blocks …).symm`);
   4. statement of `CommitmentLemmas.ComLoop.emit_init_of_lt`, `ZeroKnowledge/CommitmentLemmas.lean:486`;
   5. body of `PRFGame.pkTapes`, `Encryption/PrivateKey/OracleFromPRF/Handler.lean:139` (alias at `:141`);
   6. body of `Ensemble.copies`, `Asymptotic/Ensembles.lean:223` (the private alias at `:225`).

   Then the aliases go: the private `blocks` and `blocks_eq` (`Asymptotic/Ensembles.lean:214`, `:218`) and the public
   `EnsembleLemmas.blocks`, `blocks_eq`, `blocks_apply`, `blocks_symm_apply` (`Asymptotic/EnsemblesLemmas.lean:400`,
   `:404`, `:407`, `:413`; decls2 REMOVED, approved). The other alias uses are proofs and docstrings
   (`Asymptotic/Ensembles.lean:514`, `:550`–`:552`; `Encryption/PrivateKey/OracleFromPRF/Handler.lean:150`, `:160`;
   `Asymptotic/EnsemblesLemmas.lean:835`–`:850`). **Found at staging, not in the six:** the **body** of
   `ETTGame.dTape` (`Encryption/PrivateKey/EncryptThenTag/Handler.lean:178`, alias at `:179`) also uses
   `EnsembleLemmas.blocks`; removing the public alias needs a seventh body change of the same kind. It needs Seyoon's
   confirmation before Stage 2 (the maintainer asks; this job does not decide it).
2. **DL-43, `ProbComp.mul_prob_le_expect` (CS1-Q9, changed).** Stage 2 adds, as a noted additive exception to a
   proof-only stage, after the bb1-sim Games PR merges and frees `Games/Probability.lean`, in its `ProbComp` section:
   `theorem mul_prob_le_expect {α : Type} (c : ProbComp α) (P : α → Prop) (q : α → ℝ) (b : ℝ)
   (hq : ∀ a, 0 ≤ q a) (hP : ∀ a, P a → b ≤ q a) : b * prob c P ≤ expect c q` (fresh name; readers
   `prob_eq_expect`, `expect_const_mul`, `expect_mono`; glue, with the Lamport averaging step [PS10, proof of
   Theorem 137.2] as its first use; the `ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Then it re-points
   `Authentication/Signatures/Lamport/Averaging.lean:129` (`LamportReduction.expect_favourable_of_success`).
3. **DL-42, `MachineCodec.ext_of_fields` (CS1-Q3).** Stage 2 moves it verbatim from
   `Authentication/Signatures/HashAndSign/CodecReaders.lean:46` to `Games/Machines.lean` (a REMOVED/ADDED pair with an
   identical statement, recorded as a move) and re-points Lamport's private `lamport_codec_ext`
   (`Authentication/Signatures/Lamport.lean:771`).
4. **DL-49 (CS1-Q8, changed).** Stage 2 re-points the ThreeColoring copies **and** the ComposeSecurity copies to S1-19,
   S1-26 and S1-27 (the lists under S1-18 to S1-27).
5. **Everything else:** the per-target Stage 2 lists above, and the worker's § *The Stage 2 re-point table*.

## Multi-agent work (up to 2 sub-agents)

- **The lead owns the job:** the branch, every commit, the check tree, the integration, the final checks, the delivery
  and `REPORT.md`. Only the lead commits, runs `lake`, fetches the cache and pushes.
- **Suggested split** (disjoint files; record any other split):
  - lead: `Games/Tapes.lean` (new), `Games.lean`, `Games/Machines.lean`,
    `Games/Efficiency/Strings.lean`, `Games/Bridges/Experiments.lean`, `Pseudorandom/Functions/Asymptotic/Defs.lean`;
  - sub-agent A: `Foundations/BitLists.lean`, `Asymptotic/Adversary.lean`, `Asymptotic/Sampling.lean`,
    `Authentication/Encoding.lean`, `ZeroKnowledge/Interaction.lean`, `ZeroKnowledge/InteractionWords.lean` (new),
    `ZeroKnowledge/EncodingMachines.lean`, `ZeroKnowledge.lean`;
  - sub-agent B: `IterateFindHost.lean` (DW-9), `Randomized/PPT.lean`, `Encryption/PrivateKey/EnsembleSecurity.lean`,
    `Encryption/PublicKey/Trapdoor.lean`, and the three `InformationTheory` files.
- Each sub-agent works in its own git worktree with its own TCSlib olean tree and `.lake/packages` linked to the
  lead's, and hands its files to the lead as patches. **One Lean process at a time on the host**, for all agents,
  through one lock (`flock <clone>/.lean.lock …`), released between modules. A file is reassigned only through the
  lead, after its owner has stopped. Sub-agent logs go under `evidence/subagents/<name>/`; `REPORT.md` records who
  wrote what.

## Checks and evidence

Run Python as `python3 -I`. Never run `lake build` or an unfiltered `lake exe cache get`; check one module at a time
with `scripts/lean_check_tree.sh` (the addendum). Count errors in both forms (`^\S+\.lean:\d+:\d+: error[:(]`) in every
log; keep every raw log. Tools: adapt DW-5's (`dw5-evidence.zip`, `dw5/tools-used/`: `rule10_dw5.sh`,
`seal/rule10_b.sh`, `seal/review/{mkcollect,mkseals_ab,mkseals_coe,ctlcheck2,sealsum,touched}.py` with
`archived-gate10-tools/`, `mkctl_dw5.py`, `seal/scan1_g40.py`, `seal/scan2.py`, `seal/decls2.py`, `nameclash.py`,
`tipcensus.py`, `downorder.py`, `stateplan.py`) and T4's (`inbox/fills/bb1-machine/evidence/tools/`). Copy what you use
into `evidence/tools/`, change host paths, and record each change in the tool's header.

1. **Bootstrap and sweep** (at the check tree).
   - Bootstrap `order.txt` (847 modules, the upstream closure of the sweep, root excluded) at the check base: rc 0,
     0 errors, and the `sorry` warnings of `base-sorries.txt`.
   - **The replay-style sweep at the check head:** rebuild every module whose source differs from the source its
     olean was built from, then everything downstream of it, in order; then check the two new modules (inserted at
     the positions `closures.txt` gives) and every module of `closures.txt`'s `DOWN` (493, root excluded): 495
     modules, each rc 0 with 0 errors in both forms. Bind every checked source to `git show HEAD`
     (`evidence/build/summary.txt`: module, rc, errors in both forms, `sorry` warnings, source hash).
   - **The root** `TCSlib` (1,419 modules at the check base) is not built; the facades `Games.lean` and
     `ZeroKnowledge.lean` are in the sweep, the name-clash and shadow scans cover the root's risk, and the maintainer
     replays the root at landing.
   - Record the final `git merge-tree --write-tree f99901fdc… <stage1 head>` and the check head's tree; they must be
     equal.
2. **Admissions.** At the check head: exactly `base-sorries.txt` (26 declarations in 12 modules of the order), and no
   `sorry` in any new or changed file.
3. **Statements.** `python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py . daa6e173… <new and changed
   files>` on the branch head: **ADDED** exactly the targets (S1-01 to S1-27 without S1-13: 69 declarations),
   **0 CHANGED, 0 REMOVED**. A `StmtDump` probe prints every new constant with its full name and type; a `python3 -I`
   check compares each header with this brief's text (PASS, or each difference listed under *Statement changes*).
4. **Axioms.** `#print axioms` of every new constant: `propext`, `Classical.choice`, `Quot.sound` only (or a subset);
   no `sorryAx` anywhere in the new constants.
5. **Insertion check** (every changed existing file), a `python3 -I` script under `evidence/insertion/`: removing the
   inserted blocks restores the issue base byte for byte; each block sits at its anchor (*Scope*); final hashes
   recorded. Controls, each giving the stated result: one character changed in a base line: FAIL, exactly one
   difference; one base line deleted: FAIL, exactly one removal; one extra line elsewhere: FAIL; a block moved: FAIL.
   With decls2's 0 CHANGED, this is the proof that no existing proof is touched.
6. **Rule 10.** Readers only (policy §1). Each owner reads its own definitions directly.
   - **Canonical seals** A and B, strict and coe (the coe-variant seal A canonical), with `-DmaxErrors=0`, over the
     full TCSlib import closure, of every new or changed owner at the check head (17 existing owners and the 2 new
     modules), and **base seals** of the 17 existing owners at the check base. Report each
     seal's request count and every failing declaration, and attribute every difference from the base by its raw log:
     new theorems add requests only where they are seal rows; **no failure may sit in a new declaration**.
     `IterateFindHost`'s 16 pre-existing failures must reappear unchanged (DW-5's attribution). The facades declare
     nothing: no seal, and the report says so.
   - **Paired controls** on every new or changed owner: a negative that reads one of the owner's definitions from a
     probe by `rfl`/`unfold`/`show` (for the new modules and `BitLists`, `Entropy`, `EncodingMachines`: a new
     definition, e.g. `Games.tapeImpl`, `Games.ovr`, `recordBits`, `FinDist.mixture`, `EncodingMachines.padTo`;
     for an owner whose new content defines nothing, an existing definition of it, as DW-5 and bb1-sim did), and a positive through its reader. Each sealed negative
     fails exactly once, each positive passes, all pass unsealed (pretest first); strict and coe both
     `ALL_OK True`.
   - **The explicit-unfold scan** over the new declarations: 0 foreign. Pre-existing foreign items of the changed
     files (DW-5: 27 in `IterateFindHost`'s untouched proofs) are listed, identical at the base.
   - **Notation, never sealed:** reducible abbreviations (`ModuleHost.hostTMView`, `ModuleHost.State`,
     `QueryImpl`, `ProbComp`, `NUPPT.Coins`, `Turing.Cfg.Halted`), `PolyExpr.eval`,
     projection coercions.
7. **Frozen-file check.** `git diff --stat daa6e173…` lists only the files of *Scope*.
8. **Lint.** `python3 -I scripts/style_lint.py <new and changed files>`: no finding that is not already at the base on
   the same declaration (diff the two). `python3 -I scripts/campaign_style_lint.py <area> --check8b` at the check base
   and head for `TCSlib/Cryptography` (the maintainer's baseline at the records tip: **92 FAIL / 104 WARN over 518
   files**), `TCSlib/InformationTheory` (**5 FAIL / 2 WARN over 7 files**) and `TCSlib/Complexity` (compute it at the
   check base): diff the line sets; no new FAIL or WARN line (check 8 must show no new definition without a lemma),
   except one you disclose and justify.
9. **Sizes and widths.** Lines and maximum width of every new and changed file at the head: every line at most 100
   characters, every file at most 1000 lines (`Asymptotic/Sampling.lean` is the one near the limit).
10. **Docstrings and sketches.** Every new public declaration opens with a statement in words and states its formula;
    a tag or a glue note per *The targets*; a `**Proof sketch.**` on every proof of 15 lines or more. Module
    docstrings of changed files list the new declarations; the new modules have the full header (policy §1, §2).
11. **Name-clash and shadow scans.** (a) No new full name, public or private, already exists in `TCSlib/` or `audits/`
    at the check base. (b) Every new short name that exists elsewhere (namespaces resolved) is `protected`, and the
    report lists each such hit (they are the Stage 2 copies). (c) **Shadow scan:** for every new full name `N.x`, list
    each unqualified use of `x` in a module of `DOWN` whose enclosing namespace is `N` or lies under `N`, or that opens
    `N`, and show that its resolution is unchanged (with `protected`, it is; list any exception as a blocker).
12. **Reuse and overlap** (`REPORT.md` § *Overlap and reuse*; policy §1, *Duplication*: an undisclosed duplicate of a
    public lemma is a major). For **each** target: search TCSlib, core and Mathlib for an existing equal or more
    general form (name search, `exact?`/`apply?` on the statement in a probe, ripgrep for the conclusion's shape);
    list the searches and their hits. Confirm or correct the copy list given here; add every further copy you find to
    the Stage 2 table (it is the ledger's input). If a target already exists in a more general public form, do not add
    it: report it as a finding with the existing name.

**Checkpoints** (at least one mid-way): checkpoint 1 when every target's statement elaborates at the check tree
(*Branches*), with checks 3, 11 and 12 on it; the final with everything.

## Sources and citations

Tags only where *The targets* gives one (`pkPredictor_apply`: `[PS10, Theorem 104.4, proof]`, as `pkPredictor`).
Everything else is framework glue (policy §2): say so in one line, and name the first consumer in words where useful
(for example "the averaging step of the Lamport reduction [PS10, proof of Theorem 137.2] is its first use"), without
inventing a location. The new modules' `## References` use the repository's existing [PS10] entry verbatim:
```
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
```
followed by the location the module concerns (`Games/Tapes`: "Theorem 170.4 (book p. 170): the first consumer";
`InteractionWords`: "§4.4"). Do not add reference files, edit `blueprint/` or run `scripts/sources.py`. Identifiers use
the Greek `μ` (U+03BC), never the micro sign.

## Report

`REPORT.md` gives: the issue base, the records tip used, the check base tree and the check head's tree (with the
`merge-tree` equality), the branch head and every commit; who wrote what; the changed files with lines at base and
head; § *The new declarations* (a table: target id, full name, home, kind, `protected`, readers); § *Statement changes*
(none, or each with the reason); the builds and admissions (checks 1–2); statements and axioms (3–4); the insertion
and frozen checks (5, 7); Rule 10 seals, base seals, controls and the scan (6); lint, sizes and docstrings (8–10); the
clash and shadow scans (11); § *Overlap and reuse* (12) with § *The Stage 2 re-point table* (every copy as
`path:line`, the target it re-points to, and anything the brief missed); § *Scope requests* (none, or each with
Seyoon's answer); questions for Seyoon, if any (numbered `CS1-W1`, …, recommended option first); the evidence, with
its manifest.

### Evidence completeness

Every file that `evidence/SHA256SUMS` names is delivered: seal and control sources, manifests and request records,
the insertion check with its outputs and controls, the decls2 output and the `StmtDump`, the axiom prints, the clash
and shadow scans, the reuse searches, every raw log and `results.jsonl`, the sub-agents' logs, and the tools used. If
the evidence is too large for one commit, deliver it in several commits or numbered ZIP parts, each with an entry
list; leave nothing out for size. Check before each push that the delivered paths are exactly the manifests' (top
level and `evidence/`), with no leading `./`.

## Blockers: stop and report

- **E-RES (environment).** The addendum's preflight or cache rules fail. Stop and report the numbers.
- **E-SCOPE (frozen files).** A target needs a change outside *Scope* (an import in an existing non-facade file, a
  reader in another file, a forbidden file). Stop that line and ask Seyoon in your session (*Scope*).
- **E-ROUTE (statements).** A target's statement does not elaborate even after the smallest repair, is false, or does
  not have every listed copy as an instance. Do not weaken it silently: keep it out of the branch and put the error,
  the counterexample or the missing instance, and your proposed statement in `REPORT.md` as a question for Seyoon.
- **E-DUP (reuse).** The reuse search finds the target already public in an equal or more general form: do not add
  it; report the existing name (the Stage 2 table then points there).
- **E-SHADOW.** A new declaration changes the resolution of an existing unqualified name (check 11 (c)) and
  `protected` does not prevent it. Stop that target and report.
