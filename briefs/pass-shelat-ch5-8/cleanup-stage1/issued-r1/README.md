# Claude job `cleanup-stage1` (Pass–shelat cleanup, Stage 1: promotions)

Claude is the worker, a lead with up to 2 sub-agents on disjoint files (standing ruling: Claude for fills and all
other external jobs). The job is Stage 1 of Seyoon's three-stage cleanup (`../../cleanup-stages.md`, 2026-11-17): it
publishes, additively, the general forms that the duplication ledger names for the Pass–shelat rows (DL-35, DL-38 to
DL-49, DL-51, DL-52; DL-50 is GSW and out of scope) and DW-9's view versions of `host_dispatch`, `host_branch` and
`host_halt`, so that Stage 2 can re-point every ledgered copy. Target groups S1-01 to S1-27 (S1-13 withdrawn by
CS1-Q9): **69 new declarations**, 7 of them definitions with their readers, in 17 existing files and two new modules
(`Games/Tapes.lean`, `ZeroKnowledge/InteractionWords.lean`), with their facade lines. Nothing existing is re-pointed,
edited or deleted. Gate 47 audits #347 and Stage 1 together.

**Rulings.** Seyoon ruled CS1-Q1 to CS1-Q12 on 2026-11-17 (`cleanup-stages.md` § *Stage 1 rulings*, records tip
`8adee3e6ace3ec78171fc499b3d101a252534d55`); the brief implements them. Changed against the staging's
recommendations: **Q2** (Stage 2 removes both DL-35 aliases; the brief's *Stage 2 handover* names the six approved
changes), **Q8** (DL-49's ThreeColoring helpers are promoted in Stage 1: S1-26 in `ZeroKnowledge/Interaction.lean`,
S1-27 in the shared toolkit `ZeroKnowledge/EncodingMachines.lean`, one home per lemma), **Q9** (DL-43's
`mul_prob_le_expect` leaves Stage 1 for `Games/Probability.lean` in Stage 2; `Games/Hopping.lean` is not changed).
**Staging finding for Seyoon (before Stage 2):** the public alias `EnsembleLemmas.blocks` is also used in the body of
`ETTGame.dTape` (`EncryptThenTag/Handler.lean:178`), a seventh change of the same kind, outside the approved six. It
does not affect Stage 1.

**Base.** Issue base `daa6e173cdd94cad1475b9a96eca613bce53ba61`, the head of #347 (DW-5, `cleanup/dw5-derand-readers`),
on the records branch at `2da7e0f3cd65ec93ed71813b7828c3b66ba18942`. **Check base:** the merge of
`f99901fdc98f4c7703cf9485329600311a1ea655` (the records branch's last Lean state; the records tip `8adee3e6…` changes
no `.lean` file after it) into the issue base; `git merge-tree --write-tree` is clean and gives tree
`01cc6259480ccc9372181cd4d18d4511c87aa048`. All 19 home files are byte-identical at both; the tip's Lean commits since
`2da7e0f3` touch only GSW, IBE, pairing, Yao and `CircuitComplexity/Uniform.lean`. Every build and check runs at the
check tree (a merged-tree replay, `workflow.md` §6.1); the patches are on the issue base.

**Parallel work.** The job edits none of the files the running GSW/IBE jobs own (`Games/Probability.lean`,
`Games/Relational.lean`, `Pairing/Group.lean`, `Complexity/CircuitComplexity/**`, `Complexity/BranchingPrograms/**`,
`ComputationalModels.lean`, `machine-library-design.md`, `AdvancedEncryption/**`). Its `Games.lean` insertions (after
lines 11 and 47) avoid bb1-sim's (after lines 9 and 42). The DL-40 averaging bound is bb1-sim's, not this job's.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md) (v1 with an adaptation for
this job). Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory. The stage plan with the
rulings, the ledger, the deferred-work register and DW-5's README are on the records branch at the records tip; the
brief lists their SHA-256s.

- [Build order](order.txt): 847 TCSlib modules at the check base, in import order (a subsequence of the depth-first
  post-order of the 1,419 modules reachable from `TCSlib.lean`, imports in file order): the upstream closure of every
  module downstream of a changed module, the root `TCSlib` excluded. Insert `Games/Tapes` after module 477
  (`Games/Hopping`) and `ZeroKnowledge/InteractionWords` after module 558 (`ZeroKnowledge/Interaction`).
- [Closures](closures.txt): `CHANGED` (the 19 existing modules the job may change, with their positions) and `DOWN`
  (493 modules, root excluded: the sweep, with the two new modules 495).
- [Mathlib roots](roots.txt): 166, the Mathlib modules the 847 modules import directly.
- [Source hashes](SOURCE-SHA256SUMS) of the 847 files at the check base, read from the git objects of tree
  `01cc6259…`.
- [Base admissions](base-sorries.txt): 26 declarations in 12 modules of the order, from a syntactic scan (comments
  and strings stripped, `sorry` tokens attributed to the enclosing declaration; the same scanner reproduces the 6a
  package's 229). The final adds none.

Claude returns at least one checkpoint and the final only at `inbox/fills/cleanup-stage1/` on the exchange; it never
pushes a campaign branch. Seyoon dispatches with the prompt in the records' `dispatch.md` (beside this file in
`briefs/pass-shelat-ch5-8/cleanup-stage1/issued-r1/`; it is not part of the pack).

**Size** (maintainer's assessment). About 850–1,050 Lean lines, almost all restated from existing copies with their
proofs. The long steps are mechanical: the 847-module bootstrap, the 495-module sweep (the homes include
`Randomized/PPT`, `Foundations/BitLists`, `Asymptotic/Adversary` and `InformationTheory/FinDist`, so nearly the whole
downstream rebuilds), and four-variant canonical seals of 19 owners with base seals of 17, one Lean process at a time.
`Asymptotic/Sampling.lean` (936 lines) ends near 960 and `ZeroKnowledge/EncodingMachines.lean` (694) near 830, below
the 1,000-line limit. `IterateFindHost`'s 16 pre-existing seal failures (DW-9) reappear in its seals and are
attributed to the base. One job is right; the suggested split gives the lead the `Games` files, sub-agent A the
bit-list, encoding and ZK files, and sub-agent B the Complexity, InformationTheory and two encryption files.

**Maintainer steps before dispatch:** commit this folder to the records, write that commit's full hash for
`<RECORDS-PIN>` in `dispatch.md`, and push the exchange commit named there. If it is replayed onto a newer exchange
tip, its hash changes: put the pushed hash in `dispatch.md` (and its parent) before dispatching.

**Ready to dispatch**
