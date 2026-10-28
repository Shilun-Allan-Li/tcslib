# External audit pack — `NP` is closed downward under `≤ₚ` (PR #177, an API gate)

**Why this PR.** The space hierarchy's fill (B6's H, `SpaceComplexity/Hierarchy.lean`) proves the
corollary `SPACE_linear_ne_NP` by pulling a padded language back along the padding reduction,
which needs `NP`'s closure under polynomial-time reductions. No published lemma gave it (only
`mem_P_of_polyTimeReducible`). **The user ruled (2026-10-27): the maintainer publishes it by an API
PR, beside `mem_P_of_polyTimeReducible` (`ClassNP/Reductions`), before H's fill issues.**

**The PR:** #177 on `lean/np-closure`, head `ce00b6d3d7ca57501bf66eb949a05b90d90f0452`, two commits
on the campaign tip after #174 (`evidence/patches/`): `bfc2a395`, the theorem and the import;
`ce00b6d3`, `prefixTM_copy`'s proof sketch (an existing private, so that the policy linter is clean on
the file). The file's blob: `b5bfef1c`.

## What changed (verify)

| Class | Declarations |
|---|---|
| **New public** | `Complexity.mem_NP_of_polyTimeReducible {L L' : Language Bool} (h : L ≤ₚ L') (h' : L' ∈ NP) : L ∈ NP` |
| **Imports** | `Reductions` imports `ClassNP/PClosure` (13 modules join its closure: `PClosure`, `CoNP`, the block-loop and counter-program families; no cycle, since `PClosure`'s closure does not contain `Reductions`) |
| **Text** | the module docstring's main results; `prefixTM_copy`'s docstring gains a `**Proof sketch.**` |
| **Unchanged** | every other declaration (`evidence/freeze-Reductions.txt`: 10 → 11 public, 16 → 16 private) |

## Brief for the auditor

1. **The statement.** Is it the right public form ([AB09, §2.2]: `NP` is closed downward under
   Karp reductions), with no hypothesis beyond the two memberships?
2. **The proof.** `L'` is read through `mem_NP_iff_exists_length_le` (the bounded-certificate form):
   a verifier `V ∈ P` and the bound `C (|y| + 1) ^ c`. With `f` the reduction and
   `|f x| ≤ A (|x| + 1) ^ d` (`PolyTimeComputable.output_length_le`), the verifier for `L` accepts
   `⟨x, u⟩` exactly when `|u| ≤ C (|f x| + 1) ^ c` and `⟨f x, u⟩ ∈ V`: `inter_mem_P` of
   `lenLe_preimage_mem_P` (against `1 ^ (C (|f x| + 1) ^ c)`, by `polyTimeComputable_polyUnary`) and
   `preimage_mem_P` (under `z ↦ ⟨f (pairFstD z), pairSndD z⟩`). The bound for `L` is
   `C (A + 1) ^ c (|x| + 1) ^ (d c)`. Is it correct? In particular: the backward direction uses the
   length test to keep a certificate longer than `f x`'s bound from being accepted; is anything
   else needed?
3. **The home and the import.** Beside `mem_P_of_polyTimeReducible`, as ruled; the alternative home
   `PClosure` (which `Hierarchy` does not import, while it does import `Reductions`) would have needed
   no new import. Is the import's cost acceptable?
4. **Rule 10** (with the scope of 2026-10-23). The theorem, sealed over the six other-file
   definitions it reaches (`NP`, `P`, `PolyTimeComputable`, `pairFstD`, `pairSndD`, `pairEncode`) with
   the three `@[simp]` TCSlib definitions of the closure erased (`Action.apply`, `Cfg.init`,
   `MultiTapeTM.initCfg`), elaborates with 0 diagnostics (`evidence/ReductionsSealed.*`); its six
   controls close unsealed and fail sealed, each at its own goal (`evidence/ReductionsSealControl.*`).
   `PolyTimeReducible` is this file's own definition (destructured). Its `simp only` arguments are
   Mathlib's `Set.mem_setOf_eq`, `Set.mem_preimage`, core's `List.length_replicate` and
   `PolyTimePairing`'s theorems `pairFstD_pairEncode`, `pairSndD_pairEncode`. Is any other-file
   definition unfolded or closed by reduction?
5. **Duplication.** The screen (9 files: the file, the files its proof cites, and the classes'
   closure neighbours; base at `b7f69d00`, whose Lean is the base's, head at `ce00b6d3`;
   `evidence/screen/`): 405 → 406 declarations, 206 → 207 pairs, one new and none gone
   (`pairdiff.txt`). The new pair: the theorem reproduces 61 of the 65 characters of
   `PolyTimePairing`'s `polyTimeComputable_pairSwap` (94%), whose whole body is the invocation
   `polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD`; the shared text is the
   names of those three public rows, which the new proof invokes for a different map
   (`z ↦ ⟨f (pairFstD z), pairSndD z⟩`). Disclosed as an idiom pair (a public row's invocation; no
   lemma re-derived). Is that disposition right, and does the new proof re-derive anything
   published?
6. **The inherited sketch** of `prefixTM_copy`: is it accurate?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lnfapi4` (the snapshot of the tree after #174, the tip's Lean):
  the module with an axiom print, 0 diagnostics; the theorem on `[propext, Classical.choice,
  Quot.sound]` (`evidence/ReductionsAx.*`).
- **API copies:** no ref of 112 has a declaration named `mem_NP_of_polyTimeReducible`,
  `mem_NP_of_reduc*` or `NP_closed_under*` (`evidence/api-copy-search.txt`).
- **Lint:** `ClassNP` 0 FAIL, 16 WARN over 21 files, the base's (`evidence/lint-*.txt`); the policy
  linter: 0 findings on the file (the base's one finding, `prefixTM_copy`'s missing sketch, fixed).
  No line over 100 characters.
- **Replay:** `replay-lnpc.sh` (`evidence/merged-tree/`), the downstream closure of `Reductions`, 86
  modules, from `oleans-lnfapi4`, pinning the blob; precheck passed. **Pending** (a merge condition
  of its own). The closure overlaps PR #175's (`SpaceComplexity`); whichever merges second takes a
  merged-tree replay of the overlap.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/88-np-closure-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `np-closure-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
