# bb1-sim-statements — final

Claude statement job `bb1-sim-statements` (issued-stmt-r1). The lead, with one sub-agent (`probe`).
Three deliverables, all complete:
1. **Series 1, `stmt/games-relational`:** `Games/Relational.lean` (the target `expect_simulate_rel` and
   `expect_sample_rel` `sorry`'d, `prob_simulate_rel` proved from the target), the public averaging
   bound `ProbComp.abs_expect_sub_le_expect` in `Games/Probability.lean` (proved), and the facade's import
   and `## Contents` line.
2. **Series 2, `stmt/pairing-group-helpers`:** the four Q10 helpers in `Pairing/Group.lean`, proved.
3. **The probe** (not for landing): **ten readers** are needed, not one. See the headline below and
   [`probe/READERS-TO-INSERT.md`](probe/READERS-TO-INSERT.md).

No blocker, no scope request, no frozen file changed. One question for Seyoon (the reader set, Q7) and
two observations about the pack are at the end.

**Exchange history of this delivery:** checkpoint 1 is `8899115b8292b0ff001dd325bea9a8054074d279`
(the probe and series 2). This final adds series 1 and every remaining check.

## Headline for the scope ruling (Q7)


**The single reader of Q7 is not enough under the development seals, and neither are Q7(B)'s three.**
T2's step M reads the real game through **ten** readers: six in `Defs.lean` and four in
`BonehBoyen.lean`. All ten are theorems, each proved owner-side by `rfl` or in one line, and none needs
a change to a definition. So this is not a blocker. It is the probe's answer: the reader set Seyoon is
asked to rule on.

With the ten readers, the consumer probe proves P-1 (all nine cases), P-2 (every row of design §3.1's
step-M table) and P-3, natively and under devseal A and B, with 0 errors. **T3 needs no reader beyond
T4's.** The exact text, its anchors, the dropped candidates and their failing logs are in
[`probe/READERS-TO-INSERT.md`](probe/READERS-TO-INSERT.md).

| # | Reader | Owner (anchor at T4's head) | Proof |
|---|---|---|---|
| 1 | `IBEScheme.sidImpl_zero_onSpec` | `Defs.lean` (after line 430) | `(OracleComp.bind_pure _).symm` |
| 2 | `IBEScheme.sidImpl_two_onSpec` | `Defs.lean` | `(OracleComp.bind_pure _).symm` |
| 3 | `IBEScheme.sidImpl_one_onQuery` | `Defs.lean` | `rfl` |
| 4 | `IBEScheme.sidImpl_two_onQuery` | `Defs.lean` | `rfl` |
| 5 | `IBEScheme.sidImpl_keyGen_ne_onSpec` | `Defs.lean` | `S.sidImpl_keyGen_ne …` |
| 6 | `IBEScheme.sidImpl_challenge_fresh_onSpec` | `Defs.lean` | `S.sidImpl_challenge_fresh …` |
| 7 | `bb1Scheme_setup_eq` | `BonehBoyen.lean` (after line 412) | `rfl` |
| 8 | `bb1Scheme_keyGen_bind` | `BonehBoyen.lean` | `simp only [bb1Scheme_keyGen, …]` |
| 9 | `bb1Scheme_enc_bind` | `BonehBoyen.lean` | `rw [padFin_ofFn]; simp only [bb1Scheme_enc, …]` |
| 10 | `ofFn_bb1Scheme_encCT` | `BonehBoyen.lean` | `rfl` |

**Why the candidates of the brief fail**, each with a sealed log under
`evidence/subagents/probe/alternatives/`:
- **`sidImpl_eq_oracleImpl`, whole-function and pointwise** (`whole-fn/`). The reader elaborates and
  the consumer's `rw` with it succeeds. But `oracleImpl_zero_onSpec` then finds no instance, under
  seal A: its `init` would be `S.sidImpl b κ pp msk 0`, whose type equals the typed handler type
  only through the sealed `inLens`/`outLens`. The same file passes natively. The lead re-read this
  log: `Tactic rewrite failed: Did not find an occurrence of the pattern IBEScheme.oracleImpl ?S ?κ
  ?init ?key ?chal 0 ?x ?s`, then an application type mismatch at the explicit instance.
- **Q7(B)'s three `sidImpl_{zero,one,two}_onSpec`** (`q7b-three-onSpec/`, 9 errors sealed):
  - the typed `⊥` answers are `zeroBits (S.outLens κ i)` and do not go through an answer cast;
  - the sampling cases of `KeyGen` and `Challenge` are binds typed at `(Fin … → Bool) × σ`.
  
  Two of the three survive in other forms (#1, #2). Readers #3–#6 cover the rest.
- **No `encCT` reader, comparing by `congrArg`** (`encCT-congrArg/`, 1 error sealed). `bb1SimCt_eq`
  reads `decodeT _ m` at the width `(bb1Scheme G ℓ).msgLen`, while `Encrypt` reads it at `G.wT`, so
  `ofFn_bb1Scheme_encCT` (#10) is needed after all.
- **The generated `simps` lemmas in place of #7–#9** (`simps-lemmas/`, 8 errors) and the `.pure ⟨d, k⟩`
  equation forms (`bb1-mk-readers/`, 2 errors) fail on `Σ`-typed values that a sealed consumer cannot
  match.

**A design point for the fill (no reader).** A consumer cannot write `⟨d, pp⟩ : (bb1Scheme G ℓ).PP κ`,
as T4 found. P-2 therefore takes the setup's output map `o : … → PP κ × MSK κ` with the facts the real
handler reads from it (`RealReads`). The probe lemma `setup_out` obtains both from `bb1Scheme_setup_eq`
by an existential.

**Alternative left to Seyoon.** Nine uniform per-case readers `sidImpl_*_onSpec` (one per typed reader)
would also work, with consumer-ready right sides. The probe proposes the six that suffice.


## Bases and heads

| | Commit |
|---|---|
| Issue base (records tip at issue, fetched by name; `git rev-parse HEAD` at start) | `bdcadd858cbe043e8c41e465a96e81feb1eecda1` |
| Records commit with this issue (`issued-stmt-r1`, equal to the pack, `dispatch.md` aside) | `6fa1e1024291284c7d539910f58c5454c536db88` |
| `cryptography/pass-shelat-ch2-4` tip when fetched (the base is an ancestor; work stays on the base) | `c32ca85754ad561711fbc334834ce98919732105` |
| Series 1 head, `stmt/games-relational` | `d742bf025d471c3ba0ef889bd4e8986ff9062aeb` |
| Series 2 head, `stmt/pairing-group-helpers` | `fc9cf2f510622a6a1027c14a614c1d453da5d520` |
| Probe base: `fill/pairings-bb1-machine` tip | `7c0a55e0239c14786612d0cd4462e64238543ca1` |
| Probe base after `git am` of T4's three delivered patches (with `COMMITS.tsv`'s committer data) | `c90273fad3511ada7c9c1a53e1abdd8478237cee` (reproduced, hash for hash) |
| Probe head, `probe/bb1-sim-readers` (local; never delivered as patches) | `82e14ef6c9990fdff382f7cbae65dc24c1c089bd` |

Every branch is local, and every commit was made with `commit.gpgsign=false` (signing `none` in both
`COMMITS.tsv`).

**Inputs verified:**
- The pack, with `shasum -a 256 -c SHA256SUMS`: 8 OK.
- T4's delivery, with its top-level `SHA256SUMS`: 1,040 OK. Its `order-final.txt` has SHA-256
  `f17ade1e…`.
- T4's issued pack `checkpoint/`: OK.
- The ten input files of the brief: their SHA-256s at the base equal the brief's.

**Reproduction.** `git am` of each series' patches at the base in a scratch clone reproduces every
hash (`evidence/delivery/am-check-*.out`: games-relational 2/2, group-helpers 1/1).

## Who did what

- **Lead:**
  - environment, cache and the three olean trees;
  - series 1 and series 2;
  - the Mathlib search;
  - every check of both series (builds, admissions, statements, axioms, insertion and header checks
    with controls, Rule 10, lint, sizes, clash scans, overlap);
  - the probe's formal clash scan;
  - the lead's re-run of every probe check at the committed probe head;
  - this report, every commit and the delivery.
- **Sub-agent `probe`:** Deliverable 3. It wrote:
  - the probe sources `PlProbe/BB1SimReaders.lean`, `BB1SimStepM.lean`, `BB1SimAxioms.lean` and the
    sealed variants;
  - the scratch alternatives;
  - `probe/READERS-TO-INSERT.md`;
  - every log under `evidence/subagents/probe/` (`NOTES.md` gives the order of its runs).
  
  It used its own worktree and tree P, ran Lean only through the shared lock, and never ran `lake`.
  The lead committed its files on `probe/bb1-sim-readers`.

## Changed files

| File | Lines at base → head | Max width | Change |
|---|---|---|---|
| `TCSlib/Cryptography/Games/Relational.lean` | new → 134 | 97 | the module of design §2.2 (citations per Q11) |
| `TCSlib/Cryptography/Games/Probability.lean` | 409 → 423 | 99 | two pure insertions: bullet after line 48, lemma after line 403 |
| `TCSlib/Cryptography/Games.lean` | 64 → 67 | 98 | two pure insertions: import after line 9, `## Contents` entry after line 42 |
| `TCSlib/Cryptography/Pairing/Group.lean` | 304 → 338 | 97 | two pure insertions: four bullets after line 62, helper block after line 232 |

`git diff --stat` against the base touches exactly these files (`evidence/statements/diffstat-*.txt`).
Every other file is unchanged, including `Hopping.lean`, `Simulate.lean`, `TCSlib.lean`, `IdentityBased/`,
`Forgery.lean` and `blueprint/`. Sizes: `evidence/sizes/sizes.txt`.

## New declarations

| Name | Series | Body |
|---|---|---|
| `TCSlib.Cryptography.Games.ProbComp.expect_simulate_rel` | 1 | `sorry` (target) |
| `TCSlib.Cryptography.Games.ProbComp.prob_simulate_rel` | 1 | proved from `expect_simulate_rel` (design §2.2's three lines, unchanged) |
| `TCSlib.Cryptography.Games.ProbComp.expect_sample_rel` | 1 | `sorry` (target) |
| `TCSlib.Cryptography.Games.ProbComp.abs_expect_sub_le_expect` | 1 | proved (the ETT copy's proof, unchanged: it elaborated as given) |
| `TCSlib.Cryptography.Pairing.BilinearGroup.pow_val_add` | 2 | proved |
| `TCSlib.Cryptography.Pairing.BilinearGroup.pow_val_neg` | 2 | proved |
| `TCSlib.Cryptography.Pairing.BilinearGroup.pow_val_bijective_of_ne_one` | 2 | proved |
| `TCSlib.Cryptography.Pairing.BilinearGroup.natCast_inj_of_lt` | 2 | proved |

No `@[simp]`, no attribute, no definition (so no reader is owed), and no `open` in the new module.

## Statement changes against design r1

**None.** The three headers of `Relational.lean` (keyword, name, binders, type, up to `:= by`) are
byte-identical to design §2.2's, and so are its two import lines
(`evidence/headers/games-relational/relational-headers.out`: PASS). A control mutating `(hst : R s t)`
gives FAIL on the two headers that contain it (`relational-headers-control.out`).

The docstrings are design §2.2's prose with the supersessions of the brief:
- the citation placeholders are replaced by the review's strings (*Citations* below);
- the `**Deviation:**` of `expect_simulate_rel` is the F4 note verbatim, plus the one permitted
  sentence on the per-call hypothesis;
- the module's `## References` are the brief's two entries verbatim;
- `prob_simulate_rel` gains a short `**Proof sketch.**` and the [Sho04] tag.

Design §2.2's module prose, `## Main definitions` (None) and `## Main results` are kept.

**`abs_expect_sub_le_expect`'s name** stays the ETT copy's short name. The sweep compiles `Forgery.lean`,
which declares its private copy in `ETTGame` and calls it at line 545, with rc 0 and 0 errors, so no
ambiguity and no rename.

## Series 1: `stmt/games-relational`

Two commits, each compiling:
1. `912a343e5` `stmt games-relational: public averaging bound in Games/Probability (Q6)`;
2. `d742bf025` `stmt games-relational: Games/Relational, the relational simulation statements (Q1-Q4)`.

Commit 1 changes only `Probability.lean`. That source is identical at both commits. The base facade
at commit 1, checked against the same oleans (its seven imports are byte-identical at both commits),
gives rc 0 and 0 errors (`evidence/build/games-relational-commit1/`).

**Citations** (`evidence/citations/relational-citations.txt`: PASS). Every bracketed citation is one of
the brief's strings:
- `expect_simulate_rel` cites, against their anchors at the base:
  - `[BGZ09, §4.1, lemma (=⟦⟧)]` (the conclusion form);
  - `[BGZ09, §4.2, ⊨_φ]` (the invariant carried as pre- and postcondition);
  - `[BGZ09, §4.1, Def. 5]` (judgments);
  - `[BGZ09, §3.4]` (a well-formed adversary is free to call oracles);
  - `[BGZ09, §5.2, Lemma 1]` (an equivalence inside an arbitrary context, which §5.2 applies to replace
    one oracle by another; the ingest's Lemma 1 is the lazy/eager lemma, described as such);
  - `[Sho04, §1.1, bridging steps]` and `[Sho04, §4.2, Game 2]`.
- `prob_simulate_rel` cites `[Sho04, §1.1, bridging steps]`.
- `expect_sample_rel`, `abs_expect_sub_le_expect` and the group helpers carry no tag.

The F4 note is verbatim. No `[BGZ09, rule …]` appears, and no "adversary rule". No micro sign appears.
No reference file, `blueprint/` edit or `sources.py` run.

## Series 2: `stmt/pairing-group-helpers`

One commit: `fc9cf2f51` `stmt pairing-group-helpers: group helpers in Pairing/Group (Q10)`. No import
changed.

| Helper | Statement |
|---|---|
| `BilinearGroup.pow_val_add` | `(x : B.G) (a b : ZMod B.order) : x ^ (a + b).val = x ^ a.val * x ^ b.val` |
| `BilinearGroup.pow_val_neg` | `(x : B.G) (a : ZMod B.order) : x ^ (-a).val = (x ^ a.val)⁻¹` |
| `BilinearGroup.pow_val_bijective_of_ne_one` | `{g : B.G} (hg : g ≠ 1) : Function.Bijective fun a : ZMod B.order => g ^ a.val` |
| `BilinearGroup.natCast_inj_of_lt` | `{m n : ℕ} (hm : m < B.order) (hn : n < B.order) : (m : ZMod B.order) = n ↔ m = n` |

The names are the brief's suggestions, and all are clash-free. The proofs follow the file's own
patterns:
- `pow_val_add` is `pow_val_mul`'s rewrite chain;
- `pow_val_bijective_of_ne_one` is `pow_val_bijective`'s proof with `orderOf g = p`;
- `pow_val_neg` goes through `pow_val_add`;
- `natCast_inj_of_lt` is `ZMod.natCast_eq_natCast_iff'` with `Nat.mod_eq_of_lt`.

No further exponent law was added: the probe's P-2 needs none beyond these, `pow_val_mul(_GT)` and
`bilinear_pow`.

**Mathlib reuse decisions** (`evidence/mathlib-search/`). Each statement was posed in a generic form
in a scratch probe with Mathlib imports only and closed by `exact?`: a group with `x ^ n = 1` for (1)
and (2), a finite group with `|G| = p` prime for (3), `ZMod p` for (4). All four `exact?` fail. The
name checks find only building blocks:
- `ZMod.val_add` (`(a + b).val = (a.val + b.val) % n`);
- `ZMod.neg_val` and `ZMod.val_neg_of_ne_zero`;
- `pow_eq_pow_iff_modEq`, `orderOf_eq_prime`, `zpow_mod_orderOf`, `pow_mod_orderOf`;
- `ZMod.natCast_eq_natCast_iff'` (`(a : ZMod c) = b ↔ a % c = b % c`), `ZMod.val_natCast_of_lt`.

None states a helper in a form the fill can use directly, so the four are inserted. A grep of the
Mathlib sources for natural-cast injectivity lemmas in `Data/ZMod/` finds only `natCast_eq_iff`.

## Builds and admissions (checks 1–2)


- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4.
  - **Memory:** no cgroup memory controller, so the headroom is `MemAvailable`, 15.17 GiB (≥ 4 GiB).
  - **Disk:** the clone's ext4 filesystem has 14.29 GiB free (≥ 12 GiB).
  
  Before the preflight, the lead removed two worktrees of its own finished bb1-machine job in this
  session. Free space before the removal was 10.98 GB. No dependency tree was copied, moved or
  deduplicated.
- **One clone, one cache.** The clone is `/home/user/fill/tcslib`, the lead's clone of the bb1-machine
  job in this same session. `lake-manifest.json`, `lean-toolchain` and the lakefile are identical at
  both bases and at that clone's earlier head. Its `.lake/packages` already matched the manifest
  before this job (`evidence/logs/packages-before-cache.log`).
  
  The worktrees for series 1, series 2 and the probe symlink `.lake/packages` to the clone's.
- **Cache.** The store held 2,339 archives (116,781,456 bytes) before this job's fetch. They are the
  cache tool's own, from the bb1-machine job's narrowed fetch on this host
  (`evidence/logs/cache-store.log`).
  - The narrowed `lake exe cache get` of the 124 roots (`roots.txt`, equal to the roots computed from
    `order.txt`) exited 0.
  - It attempted 79 downloads, all done, and decompressed 2,418 files.
  - Checks:
    - no zero-size olean among 2,427;
    - packages check: `PACKAGES-CHECK PASS (every present package matches its manifest URL and
      revision)`, with `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` ABSENT;
    - a probe importing the first root elaborates, rc 0 (`evidence/logs/cache-probe/`).
- **Olean trees** (`evidence/build/bootstrap-{P,S}/`; `results.jsonl` per module with times, max
  RSS, source and object hashes):
  - **Tree P** (the probe): T4's `order-final.txt`, 189 modules at `c90273fa`. All rc 0, 0 errors in
    both forms, 56 `sorry` warnings.
  - **Tree S:** `order.txt`, 612 modules at the issue base. All rc 0, 0 errors, 28 `sorry`
    warnings (the 28 of `base-sorries.txt`). Peak RSS 3.67 GB.
  
  The series trees S1 and S2 are copies of tree S's TCSlib oleans, the alternative the addendum
  names. Tree S stays at the base for the base seals.
- Every Lean process ran under `flock /home/user/fill/tcslib/.lean.lock`, one at a time, for both
  agents. No `lake build`, no unfiltered cache fetch. Python ran as `python3 -I`.


**Sweeps.** Each `summary.txt` gives module, rc, errors in both forms, `sorry` warnings and source hash,
with every source bound to `git show HEAD`.
- **Series 2** (`evidence/build/group-helpers/`, tree S2 = a copy of tree S): `Group` and the other
  10 non-root modules of `DOWN-GROUP`, among them `BonehBoyen`, `BonehBoyenMachine`,
  `BonehBoyenSecurity` and the facades. 11/11 rc 0, 0 errors, 11/11 sources bound.
- **Series 1** (`evidence/build/games-relational/`, tree S1 = a copy of tree S): the 150 non-root
  modules of `DOWN-PROBABILITY` plus `Relational`, inserted after `Games/Simulate` in the order
  (`order-s1.txt`), 151 modules, `Forgery.lean` and the facade `Games` among them. 151/151 rc 0,
  0 errors, 151/151 sources bound. Peak RSS 2.90 GB.
- The changed modules (`Group`; `Probability`, `Games`, the new `Relational`) and everything
  downstream of them in the order are exactly what each sweep rebuilt.
- The root `TCSlib` was not built (brief: the maintainer builds it at landing). Its only new consumer
  edge, the facade `Games`, is in the sweep.

**Admissions** (`evidence/admissions/`). Every `declaration uses 'sorry'` warning is attributed to the
declaration named at its line and column, with the sweep's logs overriding the bootstrap's module by
module:

| Head | Admissions | Against |
|---|---|---|
| Issue base (bootstrap S) | 28 declarations | `base-sorries.txt`: PASS |
| Series 2 head | 28 declarations, the same | `base-sorries.txt`: PASS |
| Series 1 head | 30 declarations: the 28 plus `Games/Relational`: `expect_simulate_rel`, `expect_sample_rel` | PASS |

`prob_simulate_rel` has no `sorry` of its own.

## Statements, axioms and the dependency trace (checks 3–4)

- **decls2** (`briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py`, identical to the copy in
  `tools/seal/`):
  - series 1: ADDED exactly the three `Relational` declarations and `abs_expect_sub_le_expect`;
  - series 2: ADDED exactly the four helpers;
  - 0 CHANGED and 0 REMOVED in both (`evidence/statements/decls2-*.tsv`, empty `.err`).
- **`StmtDump`** (`evidence/axioms/*/runs/mods/StmtProbe_Stmt.log`, `STMTDUMP` lines): every new
  constant with its full name and elaborated type. The probe runs at each head against its tree,
  rc 0.
- **Axiom census.** Over every stored constant of the changed owners:
  - `Relational` and `Probability`: 60 constants, non-standard axioms only in `expect_simulate_rel`,
    `prob_simulate_rel` and `expect_sample_rel` (`sorryAx`);
  - `Group`: 83 constants, none non-standard.
- **`#print axioms`:**
  - `abs_expect_sub_le_expect` and the four helpers: `[propext, Classical.choice, Quot.sound]`;
  - `expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel`: those three and `sorryAx`.
- **Dependency trace** (the constants reached, through types and values, whose own type or value uses
  `sorryAx`):
  - `prob_simulate_rel` reaches exactly `expect_simulate_rel`;
  - each target reaches only itself;
  - `abs_expect_sub_le_expect` and the four helpers reach none.

## Insertion and frozen-file checks (checks 5, 7)

`evidence/headers/insertion_check.py`: each block must be at its anchor, and removing the blocks must
restore the base byte for byte.

| File | Blocks (base anchor) | Result | Head SHA-256 |
|---|---|---|---|
| `Probability.lean` (base `a7d79d12…`) | bullet (48), lemma (403) | PASS | in `insertion-check-Probability.out` |
| `Games.lean` (base `dd67d695…`) | import (9), `## Contents` entry (42) | PASS | in `insertion-check-Games.out` |
| `Group.lean` (base `ae72aa9c…`) | bullets (62), helpers (232) | PASS | `235b0646…` |

The controls (`insertion_controls.py`, on head copies) give the stated results for all three files,
`ALL_OK True`:
- a character changed in a base line: FAIL, exactly one difference (replace);
- a base line deleted: FAIL, exactly one difference (delete);
- an extra line elsewhere: FAIL;
- the first block moved: FAIL (not at its anchor);
- unchanged: PASS.

The frozen check is the `git diff --stat` above together with these checks.

## Rule 10: seals, base seals, controls and scan (check 6)

The tools are T4's delivered seal tools (`tools/seal/`), driven by `tools/drivers/rule10_stmt.sh`.
Every probe ran `lean -DmaxErrors=0` without `-o` over the full TCSlib import closure, one at a time,
with errors counted in both forms.

**Canonical seals at the heads** (`evidence/rule10/<series>/seals-*.tsv`). The columns are requests,
rc, errors, install/EOF records, and failing declarations:

| Owner | strict A | strict B | coe A (canonical) | coe B |
|---|---|---|---|---|
| `Games/Relational` (new) | 53, rc 0, 0 | 53, rc 0, 0 | **52, rc 0, 0** | 52, rc 0, 0 |
| `Games/Probability` | 36, rc 1, 1: `dist_apply` | 36, rc 1, 1: `dist_apply` | **35, rc 0, 0** | 35, rc 0, 0 |
| `Pairing/Group` | 567, rc 0, 0 | 568, rc 0, 0 | **567, rc 0, 0** | 568, rc 0, 0 |
| `Pairing/Assumptions` (control carrier only, below) | 644, rc 0, 0 | 645, rc 0, 0 | 643, rc 0, 0 | 644, rc 0, 0 |

Every probe has its install and EOF records. The facade `Games.lean` declares nothing, so it has no
seal. B equals A for the `Games` owners because `PolyExpr.eval` is not in their closure.

**Base seals at the issue base** (`evidence/rule10-base/`: lead clone at `bdcadd85`, tree S, its own
collector at the base):

| Owner | strict A | strict B | coe A | coe B |
|---|---|---|---|---|
| `Games/Probability` | 36, rc 1, 1: `dist_apply` | 36, rc 1, 1: `dist_apply` | 35, rc 0, 0 | 35, rc 0, 0 |
| `Pairing/Group` | 567, rc 0, 0 | 568, rc 0, 0 | 567, rc 0, 0 | 568, rc 0, 0 |

**Attribution** (`evidence/rule10/attribution/`):
- The request sets of `Probability` and `Group` at the heads **equal** those at the base, name for
  name, in all four variants (`requests-vs-base.txt`). New theorems add no request.
- `Probability`'s strict seals fail once, in `ProbComp.dist_apply`, identically at the base and at the
  head (the same `Type mismatch` at `rfl`; the probe line moves by one, with the inserted bullet). The
  strict-only request is exactly `TCSlib.InformationTheory.FinDist.instCoeFunForallReal`, the
  `FinDist` `CoeFun` instance (`probability-strict-vs-coe.txt`). `dist_apply` (`dist c a = prob c
  (· = a) := rfl`, base line 290) reads `dist c a` through that coercion.
- This is pre-existing at the base, outside this job's insertions. The canonical coe-variant seal,
  which keeps projection coercions open as notation (the brief's notation list), passes at both.

**Paired controls** (`evidence/rule10/<series>/controls-{strict,coe}/`, `ctlcheck-*.log`). They were
generated by `mkctl_bb1s.py`: T4's generator with one row added, `ProbComp.expect`. Its negative is
`expect (pure a) g = g a := rfl`; its positive is `ProbComp.expect_pure a g`.
- **`Probability`**: the `ProbComp.expect` row is exercised where `expect` is foreign, in
  `ControlS_*_Relational` (and in `Assumptions`). `Probability`'s own record exercises the inherited
  `OracleComp.AllOutputs` row.
- **`Group`**: the inherited rows `BilinearGen.inst` (`ctlInst`, positive `inst_eq`) and
  `BilinearGen.desc` (`ctlDesc`, positive `desc_eq`). `Group`'s own definitions are foreign only to
  its consumers, so they are exercised in the **control carrier** `Pairing/Assumptions`, the smallest
  direct consumer of `Group`. Its record is sealed for the controls only and passes all four seals
  too. `Group`'s own record exercises its inherited foreign rows (`runAtL`, `ofPolyTime`,
  `advInput`, `uprob`, and `PolyExpr.eval` in B).
- **Pretest first:** every unsealed control passed before the seal run (`pretest/summary.txt`).
- Then every sealed negative fails exactly once, every positive passes, and all pass unsealed:
  strict and coe both `ALL_OK True` for both series. Series 1 has 6 expected sealed failures per
  harness, series 2 34.
- `Relational` defines nothing, so no row targets it.

**Explicit-unfold scan** (`evidence/scan/<series>/`): 0 foreign in both.
- Series 1 (`Relational`, `Probability`, `Games`): 101 items, kinds probe rc 0.
- Series 2 (`Group`): 59 items, kinds probe rc 0.

Attempt 1 of the series 1 scan stopped in `scan1` with a `KeyError` for `Games.lean`, which was
missing from that series' touched-declarations file (`scan/games-relational-attempt1/`). The driver
added it (header records the change), and attempt 2 is the result above.

## Lint, sizes and sketches (checks 8–10)

- `style_lint.py` on the new and changed Lean files: 0 findings for series 1's three and series 2's
  one (`evidence/lint/style-*.txt`).
- `campaign_style_lint.py TCSlib/Cryptography --check8b`:
  - base: **92 FAIL / 103 WARN over 450 files**, the maintainer's baseline;
  - series 1 head: 92 / 103 over 451 files;
  - series 2 head: 92 / 103 over 450 files.
  
  The FAIL and WARN line sets equal the base's at both heads: no new line
  (`campaign-diff-*.txt` empty).
- `dev/sk15.py` (proofs of 15 or more lines without a sketch) on `Relational`, `Probability` and
  `Group`: none. Both `sorry`'d targets carry a `**Proof sketch.**`.
- Widths: every line of every new or changed file and probe file is at most 100 characters, and every
  file is at most 1,000 lines (`evidence/sizes/sizes.txt`).

## Name-clash scan (check 11)

`tools/clash/clash_scan.py` (T4's scanner) checks every new name, public or private, namespaces
resolved, against `TCSlib/` and `audits/` at the issue base: 1,386 files and 30,564 declarations.

| | New names | Clashes | Same short name |
|---|---|---|---|
| Series 1 | 4 | 0 | 1: `ETTGame.abs_expect_sub_le_expect` (private, `Forgery.lean:515`), the copy Q6 re-points in DL-40; disclosed |
| Series 2 | 4 | 0 | 0 |
| Probe readers (10), at the base and at T4's head | 10 | 0 | 0 |

## Overlap and reuse (check 12)

**Searches** (`evidence/overlap/searches.txt`, at the base, before the series commits):
- `git grep` over `TCSlib/` and `audits/` for:
  - the new names;
  - `σ → τ → Prop`, coupling and bisimulation terms, and the [BGZ09]/pRHL/CertiCrypt names;
  - the averaging form and `abs_expect_sub_le`;
  - the exponent shapes `^ (… + …).val` and `^ (-…).val`, `Function.Bijective fun … : ZMod`, and the
    `natCast` lemmas;
  - `theorem pow_val_`.
- The new names on every local and remote ref.
- The Mathlib search above.

**Design §2.4's table, confirmed** (`design-table-check.txt`). Every row's name sits at its stated
`file:line` at the base: 33 rows OK, including the brief's added rows. No new relative was found.
The rows:
- `ProbComp.expect_simulate_congr` (`Hopping.lean:384`): the `R = Eq` case.
- `simulate_eq_of_abs` and `_bounded` (`Simulate.lean:334`, `:357`).
- The ETT `expect_simulate_abs(_inv)` (`Tools.lean:65`, `:88`): budgeted, not instances (Q5).
- The until-bad lemmas (`Hopping.lean:201`, `:252`, `:306`, `:343`).
- `Games.expect_simulate_eager` (`:494`), used beside the new lemma, and the same-named
  `ChallengeSim.expect_simulate_eager` (`ChallengeSim.lean:148`).
- The specific bisimulations and couplings (`expect_lazyImpl`, `expect_ettImpl_lazy`,
  `expect_ettLazyTape`, the tape lemmas, `simulate_eImpl_congr`, `expect_simulate_sample_once`,
  `planted_coupling`, `expect_runB_good`).

No public or private lemma relates two simulations by a relation between different state types, and
no lemma states L3's bijective coupling of one sample as a relational step (L3 is new).

**Added rows:**

| New lemma | Nearest relatives | Relation |
|---|---|---|
| `ProbComp.abs_expect_sub_le_expect` | private `ETTGame.abs_expect_sub_le_expect` (`Forgery.lean:515`) | the same statement with `α` for `β` and the same proof: **disclosed duplicate by ruling (Q6)**; the private copy is re-pointed in the DW-4 / DL-40 cleanup; `Forgery.lean` is untouched |
| | `ProbComp.abs_expect_sub_le` (`Probability.lean:392`) | constant bound `ε`; the new lemma is its pointwise-bound form |
| `BilinearGroup.pow_val_add` | `pow_val_mul` (`Group.lean:192`), `pow_val_mul_GT` (`:197`); Mathlib `ZMod.val_add`; `schnorr_completeness` (`SchnorrProtocol.lean:69`) | the additive companion of `pow_val_mul`; Schnorr derives the same congruence inline, for a generator of order `q` with `ZMod q`, and states no lemma |
| `BilinearGroup.pow_val_neg` | `pow_val_add`; Mathlib `ZMod.neg_val` | no copy found; `BonehBoyen.lean:445`, `:460`, `:470` use the shape `X ^ (-z).val` in definitions and readers, not as a law |
| `BilinearGroup.pow_val_bijective_of_ne_one` | `pow_val_bijective` (`Group.lean:224`), the `G_T` form; `exists_pow_eq` (`:170`) | the `G` form Q10 names; the same proof pattern |
| `BilinearGroup.natCast_inj_of_lt` | Mathlib `ZMod.natCast_eq_natCast_iff'`, `ZMod.val_natCast_of_lt`; inline uses (`MatchingMath.lean:411`, `Primality.lean:528`) | no lemma states it; those files rewrite inline with `natCast_eq_natCast_iff'` and `Nat.mod_eq_of_lt` |

## The probe (Deliverable 3): checks


**Files** (`probe/PlProbe/*.lean.txt`, outside `TCSlib/`; the probe head `82e14ef6c…`):

| File | Lines | Max width |
|---|---|---|
| `BB1SimReaders.lean` | 174 | 100 |
| `BB1SimStepM.lean` | 586 | 100 |
| `BB1SimAxioms.lean` | 54 | 85 |
| `Sealed/BB1SimStepM_A.lean`, `_B.lean` | 605 each | 100 |

The sealed variants are byte-identical to `devseal.py` of the consumer, re-generated by the lead. None
of the files contains `sorry`, `admit`, `axiom`, `native_decide` or `@[simp]`.

**Checks.** The sub-agent ran them (`evidence/subagents/probe/`), and the lead re-ran them at the
committed probe head (`evidence/probe-lead/`) with the same results:

| Check | rc | Errors (both forms) | Warnings | Note |
|---|---|---|---|---|
| readers probe, native (into tree P) | 0 | 0 | 0 | |
| consumer `BB1SimStepM`, native | 0 | 0 | 0 | |
| axioms module, native | 0 | 0 | 0 | |
| consumer, devseal A (`-DmaxErrors=0`, no `-o`) | 0 | 0 | 0 | `DEVSEAL A sealed 868` |
| consumer, devseal B | 0 | 0 | 0 | `DEVSEAL B sealed 869` |

- **Axioms** (37 constants: 10 readers, 27 probe lemmas): 30 use `[propext, Classical.choice,
  Quot.sound]`, 6 use `[propext]`, 1 uses none; none is non-standard.
- **In-situ insertion** (`evidence/subagents/probe/insertion/`): copies of both owners at T4's head
  with the blocks compile natively, rc 0, and removing the blocks restores them byte for byte.
  - `Defs.lean`: 476 → 563 lines, SHA-256 `97ecb6e0…`.
  - `BonehBoyen.lean`: 714 → 760 lines, SHA-256 `88454d6f…`.
  
  The lead checked that the Lean text in `READERS-TO-INSERT.md` is byte-identical to those blocks,
  and that both blocks occur verbatim in the readers probe.
- **Name clashes** (`evidence/clash/probe-readers*`, `tools/clash/probe_clash.py`, the core of the
  bb1-machine clash scanner): the ten names, namespaces resolved, against `TCSlib/` and `audits/` at
  the issue base and at T4's head. 10 OK, 0 CLASH, and no same-short-name hit, at both.
- **Development seals.** They are T4's `devseal.py`, copied (header records one line split for
  widths). They are not the canonical seals. Those run on `Defs`/`BonehBoyen` once the readers land.

**P-2's algebraic hypotheses** (none mentions an IBE definition) and their providers:

| Hypothesis | Provider |
|---|---|
| `he` (the bijection `α₁ ↦ X^{−ID} g^{α₁}`) | `pow_val_bijective_of_ne_one` |
| `hinj` (distinct identities stay distinct in `Z_p`) | `natCast_inj_of_lt` with `bitsToNat_lt` and good coins |
| `hkey` (BB04's key identity) | `pow_val_add`, `pow_val_neg`, `pow_val_mul` and `ZMod` field arithmetic |
| `hF` (`F(ID*) = g^{α₁}`) | `pow_val_add`, `pow_val_neg` |
| `hT` (the BDH value) | `bilinear_pow`, `pow_val_mul_GT` |

The rows, all done:
- P-1: the nine cases.
- P-2:
  - sampling rows `Init` uncommitted (along `e ID`), `KeyGen` for `ID ≠ ID*` (along
    `Equiv.addRight (b'/(ID − ID*))`) and the first valid `Challenge` (`Equiv.refl`, the lazy `c`);
  - deterministic rows `Init` committed, `KeyGen` before `Init` or for `ID*`, `Challenge` before
    `Init`, repeated, or invalid.
- P-3: T3's challenge, along `Equiv.mulLeft (decodeT(M₁)⁻¹ · decodeT(M₀))`, with T4's readers only.

**Incidents (sub-agent, recorded in `NOTES.md`).**
- The source of throwaway `scratch/stepmdev*` debugging runs was not kept. They are superseded by
  `alternatives/encCT-congrArg/`, and their logs remain.
- An unquoted heredoc once made the shell try to run back-quoted words while writing the
  `READERS-TO-INSERT.md` draft. Everything failed or was refused, nothing changed on disk except that
  file, and the file was regenerated.
- Three scratch files exceed 100 characters per line: `Explore2`, `Owner1`, and the `*_A` variants
  made before the `devseal.py` line split. They are evidence of explorations, not probe files.


## Scope requests

None. No frozen file was changed on any branch. `Defs.lean` and `BonehBoyen.lean` are unchanged on the
probe branch: the readers are proved in the probe.

## Questions for Seyoon

1. **Q7, the reader set** (the probe's purpose; not a blocker). The development seals refute the one
   reader of Q7 and the three of Q7(B). The minimal set the probe found is the ten readers above:
   six in `Defs.lean`, four in `BonehBoyen.lean`. Each is a theorem proved by `rfl` or in one line,
   ready for byte-for-byte insertion at T4's anchors. Approve these ten, or the uniform alternative of
   nine per-case `sidImpl_*_onSpec` readers in place of #1–#6.

## Observations on the pack

- `base-sorries.txt` lists its 28 declarations in **13** modules (13 module lines), while its README
  and the brief say 14 (and 30 in 15 after series 1). The admissions here match the file exactly: 28
  in 13 at the base and series 2, and 30 in 14 at series 1.
- The base's strict seal of `Games/Probability` fails once, at `dist_apply`, through the `FinDist`
  coercion; the canonical coe seal passes (Rule 10 above). It is not this job's change. It is noted
  because the brief asks for every failing declaration of every seal.

## Evidence

`evidence/` with its manifest `evidence/SHA256SUMS`, and the top-level `SHA256SUMS` listing every
delivered file except itself. The delivered paths equal the manifests' paths, with no leading `./`
(checked by `evidence/tools/deliver.py` before the push). The main directories:
- `logs/`: preflight, cache and package checks;
- `build/`: the bootstraps, the sweeps and the commit-1 check, with `results.jsonl` and raw logs;
- `mathlib-search/`, `admissions/`, `statements/`, `axioms/`, `headers/` (with `blocks/`), `rule10/`,
  `rule10-base/`, `scan/`, `lint/`, `sizes/`, `clash/`, `overlap/`, `citations/`;
- `probe-lead/`: the lead's re-run of the probe;
- `subagents/probe/`: the sub-agent's logs, tools, insertion check and scratch sources;
- `delivery/`: the `git am` reproductions;
- `tools/`, every tool used.

Tools copied from T4's delivery say so in their headers, with any change recorded there:
- copied: `review/runner.py`, `seal/*`, `widths.py`, `sweepsum.py`, `dev/sk15.py`, `clash/*`;
- adapted: `seal/rule10_b.sh` (per-series directories), `deliver.py` (several series) and
  `seal/review/mkctl_bb1s.py` (one row);
- new: `pkgcheck.py`, `insert_blocks.py`, `drivers/bootstrap.sh`, `drivers/rule10_stmt.sh`,
  `headers/*.py`, `admissions/admissions.py`, `clash/probe_clash.py`,
  `overlap/design_table_check.sh`.
