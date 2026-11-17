# bb1-sim-statements — checkpoint 1 (the probe complete; series 2 built)

Claude statement job `bb1-sim-statements` (issued-stmt-r1). The lead, with one sub-agent (`probe`).
This checkpoint carries the probe, Deliverable 3, for Seyoon's scope ruling Q7, and series 2. Series 1
is committed locally and its 151-module sweep is still running, so it is not in this checkpoint. The
final carries series 1, the seals, the controls and the rest of the checks.

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
| Issue base (records tip at issue, fetched by name) | `bdcadd858cbe043e8c41e465a96e81feb1eecda1` |
| Records commit with this issue (`issued-stmt-r1`, equal to the pack, `dispatch.md` aside) | `6fa1e1024291284c7d539910f58c5454c536db88` |
| `cryptography/pass-shelat-ch2-4` tip when fetched (the base is an ancestor; work stays on the base) | `c32ca85754ad561711fbc334834ce98919732105` |
| Series 2 head, `stmt/pairing-group-helpers` (1 commit) | `fc9cf2f51…` (full hash in `patches/group-helpers/COMMITS.tsv`) |
| Series 1 head, `stmt/games-relational` (2 commits; in the final) | local, sweep running |
| Probe base: `fill/pairings-bb1-machine` tip | `7c0a55e0239c14786612d0cd4462e64238543ca1` |
| Probe base after `git am` of T4's three delivered patches (with `COMMITS.tsv`'s committer data) | `c90273fad3511ada7c9c1a53e1abdd8478237cee` (reproduced) |
| Probe head, `probe/bb1-sim-readers` (local, never delivered as patches) | `82e14ef6c…` (`evidence/probe-lead/HEAD.txt`) |

Every branch is local. Commits use `commit.gpgsign=false`. The pack verifies (`shasum -a 256 -c
SHA256SUMS`: 8 OK). T4's delivery verifies with its top-level `SHA256SUMS` (1,040 OK). Its
`order-final.txt` has SHA-256 `f17ade1e…`. The ten input files the brief lists match their SHA-256s at
the base.

## Who did what

- **Lead:**
  - environment, cache and both olean trees;
  - series 2 and series 1;
  - the Mathlib search;
  - the insertion, header, statement and clash tools and checks;
  - the probe's formal clash scan;
  - the lead's re-run of every probe check at the committed probe head;
  - this report, the commits and the delivery.
- **Sub-agent `probe`:** Deliverable 3. It wrote:
  - `PlProbe/BB1SimReaders.lean`, `BB1SimStepM.lean`, `BB1SimAxioms.lean` and the sealed variants;
  - the scratch alternatives;
  - `probe/READERS-TO-INSERT.md`;
  - every log under `evidence/subagents/probe/` (`NOTES.md` gives the order of its runs).
  
  It ran Lean only through the shared lock and never ran `lake`. The lead committed its files.

## Environment (addendum Part 1)

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

## Series 2: `stmt/pairing-group-helpers` (built; final checks in the final)

One commit, `stmt pairing-group-helpers: group helpers in Pairing/Group (Q10)`. `Group.lean` goes from
304 to 338 lines, with two pure insertions: four `## Main results` bullets after line 62, and the
helper block after line 232. No import changed.

| Helper | Statement |
|---|---|
| `BilinearGroup.pow_val_add` | `(x : B.G) (a b : ZMod B.order) : x ^ (a + b).val = x ^ a.val * x ^ b.val` |
| `BilinearGroup.pow_val_neg` | `(x : B.G) (a : ZMod B.order) : x ^ (-a).val = (x ^ a.val)⁻¹` |
| `BilinearGroup.pow_val_bijective_of_ne_one` | `{g : B.G} (hg : g ≠ 1) : Function.Bijective fun a : ZMod B.order => g ^ a.val` |
| `BilinearGroup.natCast_inj_of_lt` | `{m n : ℕ} (hm : m < B.order) (hn : n < B.order) : (m : ZMod B.order) = n ↔ m = n` |

- **Mathlib first** (`evidence/mathlib-search/`). `exact?` fails on each statement in a generic form:
  a group with `x ^ n = 1`, a finite group of prime order, and `ZMod p` for (4). Mathlib has only
  building blocks: `ZMod.val_add`, `ZMod.neg_val`, `pow_eq_pow_iff_modEq`, `orderOf_eq_prime`, and
  `ZMod.natCast_eq_natCast_iff'` (a `%` form). None is "directly usable", so all four are inserted.
- **Proofs.** They follow the file's own patterns. `pow_val_add` is `pow_val_mul`'s rewrite chain.
  `pow_val_bijective_of_ne_one` is `pow_val_bijective`'s proof with `orderOf g = p`. `pow_val_neg`
  goes through `pow_val_add`. `natCast_inj_of_lt` is `natCast_eq_natCast_iff'` and `Nat.mod_eq_of_lt`.
- **The probe uses all four** as intended providers of P-2's hypotheses (READERS-TO-INSERT §4). No
  further exponent law was needed.
- **Sweep** (`evidence/build/group-helpers/`): `Group` and the other 10 non-root modules of
  `DOWN-GROUP`, on tree S2. All rc 0, 0 errors. `sorry` warnings: `Assumptions` 1 (T1),
  `BonehBoyenMachine` 1 (T4 at the base), `BonehBoyenSecurity` 2 (T2, T3), the base admissions.
- **Insertion check** (`evidence/headers/group-helpers/insertion-check.out`): both blocks are at
  their anchors, and removing them restores the base byte for byte. PASS; head SHA-256 `235b0646…`.
- **Lint at the working head:** `style_lint.py Group.lean` gives 0 findings. `campaign_style_lint.py
  TCSlib/Cryptography --check8b` gives 92 FAIL / 103 WARN over 450 files, with the same line set as
  the base (base 92 / 103 / 450, `evidence/lint/campaign-base.txt`).
- **In the final:** decls2 and the `StmtDump`, the axioms, the insertion controls, the canonical
  seals and base seal of `Group`, its paired controls, the scan and the clash scan.

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

## Not yet in this checkpoint

- **Series 1**, which comes with the final:
  - commits `912a343e5` (the averaging bound) and `d742bf025` (`Relational.lean` and the facade);
  - the headers checked against design r1 (PASS);
  - the sweep of the 151 modules, running when this was pushed. Its log directory is still being
    written, so it is not in this checkpoint.
- For both series:
  - admissions;
  - decls2 and `StmtDump`;
  - axioms and the dependency trace;
  - insertion controls;
  - the Rule 10 canonical seals, base seals and paired controls;
  - the explicit-unfold scan;
  - final lint, sizes and sketches;
  - the clash scan;
  - § *Overlap and reuse*.

## Evidence

`evidence/` with its manifest `evidence/SHA256SUMS`, and the top-level `SHA256SUMS`. The delivered
paths equal the manifests' paths, checked by `evidence/tools/deliver.py`. Tools copied from T4's
delivery record their changes in their headers: `review/runner.py`, `seal/*`, `widths.py`,
`sweepsum.py`, `dev/sk15.py`, `clash/*`. `deliver.py` is adapted; `pkgcheck.py`, `insert_blocks.py`,
`headers/*.py`, `clash/probe_clash.py` and `seal/review/mkctl_bb1s.py` are new.
