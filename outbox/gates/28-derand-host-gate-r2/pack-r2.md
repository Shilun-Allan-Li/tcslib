# Gate 28 · The seed-majority enumeration host for derandomization (derand host, statement) · round 2

The auditor is Codex. Round 1 was HOLD (0/2/1/1); its findings are `findings/gate28-derand-host-findings.md` (SHA-256
`2d1b32ed…`). This round re-audits the two majors, the minor and the note. The round-1 pack (`pack.md`) still defines
the scope; its questions stand for anything round 1 left unverified.

- **PR:** draft [PR #312](https://github.com/Shilun-Allan-Li/tcslib/pull/312), now at
  `0c04d1eb1e5450372632a23f3e94f3b7bfc37606` (branch `stmt/pass-shelat-derand-host`, tree
  `2a3a58ab0e422d06f2d8d13d1d9e8a8820f09bea`).
- **Base:** `013119f006af40d03b88b0fc2d9b453cf0a9b348`, unchanged; the PR was not rebased.
- **New since round 1:** two commits on top of the round-1 head `8972fb4ef15fa3d4e3df37d6aa8674408835593d`, both by
  the maintainer (author and committer Claude):
  - `2f9333b99b83fdd6accb29926fab38fd75f66897` (tree `528e9c7d…`): the machine-level contract (G28-02), the
    consumer wording (G28-03) and the proof owner (N28-01). It touches `Randomized/SeedMajority.lean` (101
    insertions, 27 deletions) and the facade `Randomized.lean` (its `## Contents` entry only: 2 insertions, 1
    deletion).
  - `0c04d1eb` "corollary admitted until mem_DTIME_iff (Rule 10)": `SeedMajority.lean` only (21 insertions, 24
    deletions).
- **The target branch moved.** Since round 1, #311 was merged into `cryptography/pass-shelat-ch2-4` (merge
  `9c32076f`, head `542bfb1e`). Its Lean change is the new module `Cryptography/SecureComputation/
  SpecialEncryptionMulti.lean` and two lines of the facade `Cryptography/SecureComputation.lean`, disjoint from
  #312's two files. Every other commit from the base to the tip `c080a8406f5a8f8d29e5cf1787162d26a1d8a64c` is
  records only. GitHub's three-dot diff against the tip equals `pr.diff-r2.txt` byte for byte.
- **Resolutions:** `resolutions-r1.md` (the dispositions, then its § "Round-2 edits").

Lean paths below are under `TCSlib/Complexity/` unless they start with `TCSlib/`.

## What to check

### 1. G28-01: is H17 registered, and does the row match the code?

`machine-library-design.md` §14 at records `c080a840` (in `verification-r2.zip`, `records/`) has two changes against
the round-1 copy from `41e3cd2a` (`checks/machine-library-design-r1-r2.diff`, 3 insertions, 1 deletion):
- the status paragraph's sentence "H17 was registered 2026-11-15 for the derand host statement gate (Gate 28,
  G28-01).", after the H15 sentence;
- row **H17**, after H16.

The row's draft is `landing-r1/H17-row-draft.md` (= the round-2 evidence's `H17-row.md`). The entered row differs
from it in two sentences: the corollary is recorded as admitted until `mem_DTIME_iff` (the draft said "proved from the
contract through `mem_DTIME_of_decidesInTimeVia`, `DTIME.mono` and `Randomized.DTIME_const_mul_subset`"), and the
round-2 head is `0c04d1eb` (the draft had `2f9333b9`).

Check the row against `SeedMajority.lean` at `0c04d1eb`:
- **contract:** `V ∈ P` on `pairEncode x u`; the unary width hypothesis; one finite machine `M` with `c, e` and
  `B(n) = c · (2^{w(n)} · (n+1)^e)`; `M.DecidesInTime S B` with ties rejecting; the envelope
  `|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ B |x|` for every `x`, `v`, `j`; existential, no definition;
- **home** `TCSlib/Complexity/Randomized/SeedMajority.lean`, namespace `Complexity`; **reader**
  `Randomized.half_lt_randProb_iff` (proved);
- **status:** statement only, round-2 head, Gate 28 round 1 HOLD at `8972fb4e`, round 2 pending; the G28-02
  disposition (Seyoon's ruling, no time-only exception);
- **owner:** the `derand` fill, with the two pre-approved shared-file changes;
- **consumers:** `bpp_subset_dtime_subexp` through the corollary with the piecewise test and width; prospectively
  `BPP ⊆ EXP` by coin enumeration;
- **route** and **envelope clause:** the state loop, `exists_loopFindTM` over H14 with fuel `Nat.bits (2^{w(|x|)})`,
  the bound `c₀ (T(n) + 1)(2^{w(n)} + 2)`, the time-derived envelope, and no `loopHostTM_*`/`timedCondTM_*` spec.

Two wording differences between the row and the code, for rating:
- The row's route runs "through the pre-approved generic-fuel harvest `computesFunInTime_find`"; the module's route
  says "exactly as in `Complexity.IterateFind.polyTimeComputable_find`" and does not name the harvest.
- The row's status column says the `derand` fill "proves both the host contract and Theorem 180.1"; its contract
  column, the module docstring and the corollary's **Status** also name the corollary.

### 2. G28-02: is the new `exists_seedMajorityTM` the contract the ruling asks for?

The ruling (Seyoon, 2026-11-15; decision-log row "Gate findings in"): a machine-level host contract tying correctness,
time and a coarse head envelope, derived from the time bound, to the **same machine**, with `seedMajority_mem_DTIME`
kept as its corollary and no admitted `loopHostTM_*` space spec used.

```lean
open Classical in
theorem Complexity.exists_seedMajorityTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ (M : FinTM Bool) (c e : ℕ),
      M.DecidesInTime
          {x : List Bool | 2 ^ w x.length <
            2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
              pairEncode x (List.ofFn u) ∈ V).card}
          (fun n => c * (2 ^ w n * (n + 1) ^ e)) ∧
        ∀ (x : List Bool) (v : ℕ) (j : Fin M.k),
          |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤
            ((c * (2 ^ w x.length * (x.length + 1) ^ e) : ℕ) : ℤ) := by
  sorry
```

Check:
- **One machine.** Both conjuncts are about the same `M`, `c` and `e`. The run in the envelope starts at
  `M.tm.initCfg x`, the configuration that `FinTM.DecidesInTime` → `FinTM.ComputesInTime` →
  `MultiTapeTM.ComputesInTimeAndSpace` (`TuringMachine/Deterministic.lean:414`) runs from.
- **Form.** The envelope is `Turing.ModuleHost.Clean.envelope`'s (`TuringMachine/Build/ModuleHost.lean:244`): the
  absolute work-head position at every time `v` is at most the time budget at the argument's length, cast to `ℤ`.
  `Clean.envelope` runs from the seam `Cfg.ofWords … (stateWord M.k arg)`; here the run starts from the input
  configuration, and the budget is the decision budget `B |x|`. No space spec is admitted, and none is cited.
- **Truth, including the envelope.** Round 1 found the time and correctness part true (ties, `w = 0`, `m = 0`,
  small `n`). The envelope: every work head starts at the origin (`Turing.Cfg.init_workTapePos`, a field lemma used
  at `Randomized/Build/IterateFind.lean:385`), moves by at most one cell per step
  (`Turing.MultiTapeTM.workTapePos_step_le`, `Deterministic.lean:281`; over a run
  `MultiTapeTM.workTapePos_runFrom_mem_Icc`, `TuringMachine/Finite.lean:471`), and the run is constant after it halts
  (`MultiTapeTM.runFrom_of_halt`, `Deterministic.lean:262`), which `ComputesInTimeAndSpace` puts at time `B |x|`. So
  `|pos| ≤ min(v, B |x|)`. `c ≥ 1` is forced, since no machine halts in 0 steps (`FinTM.not_computesInTime_zero`).
- **Sufficiency through the corollary.** The corollary's statement is byte-identical to round 1's, which round 1
  found sufficient for Theorem 180.1 by the full paper proof. The contract implies it: with `T n = 2^{w(n)} ·
  (n+1)^e`, the contract's budget is literally `fun n => c * T n`, so `⟨e, mem_DTIME_iff.2 ⟨c, M, hM⟩⟩` once the reader
  exists (`DTIME T = {L | ∃ c M, M.DecidesInTime L fun n => c * T n}`, `ClassP/DTIME.lean:88`).
- **Rule 10.** The module introduces no definition; its one proof is `half_lt_randProb_iff`, unchanged. The
  whole-file seal now marks `Randomized.randProb`, `Complexity.DTIME`, `Complexity.P`,
  `Complexity.PolyTimeComputable`, `Turing.pairEncode`, `Turing.FinTM.DecidesInTime` and
  `Turing.FinTM.DecidesInTimeVia` local irreducible, and passes (evidence below).
- **Docstrings.** The contract's formula docstring, `**Deviation.**` (the envelope is the host clause of policy §1,
  not in the source) and five-step `**Proof sketch.**`; the module's § "The formal reading", § Design (head envelope)
  and § Route step 5.

The module also states that a sharper envelope holds (state words of length `O(n + w(n))`) and is not stated, as
H14's docstring does for its factor-two bound. Is the coarse envelope enough for policy §1 and the ruling, and is this
the right form for a host whose machine starts from the input rather than from a seam?

### 3. The corollary `seedMajority_mem_DTIME`: admitted, for Rule 10

Round 2's first commit proved the corollary from the contract through `mem_DTIME_of_decidesInTimeVia`
(`ClassP/ModelInvariance.lean:70`, with `Function.Embedding.refl Bool`), `DTIME.mono` and
`DTIME_const_mul_subset`. That proof fed `hM x` to an argument of type `M.DecidesInTimeVia (refl) L T` applied to
`x`, after rewriting with `Function.Embedding.coe_refl` and `List.map_id`. It therefore read
`Turing.FinTM.DecidesInTime` and `Turing.FinTM.DecidesInTimeVia` by their definitions; the round-2 evidence's
informational `StrictSealSeedMajority` failed exactly there (2 errors, both in the corollary). The second commit
reverts the body to `sorry`. It also drops the two imports added for that proof (`ClassP.ModelInvariance`,
`Randomized.QuasiPolyHierarchy`), so the imports are again round 1's.

The corollary's docstring gains a `**Status.**` paragraph: admitted; it follows from the contract through the reader
`Complexity.mem_DTIME_iff`, which the `derand` fill adds beside `DTIME` under its pre-approval (Seyoon, 2026-11-15,
"by `Iff.rfl`, formula docstring"); the `derand` fill proves the contract and the corollary. Its proof sketch now runs
through `mem_DTIME_iff` alone (the budget is literally `c · T n`, so no `mono` or constant absorption). The module
docstring's "The class" bullet, its `## Main results` entry and its proof-owner sentence say the same.

Check:
- that no published reader introduces `L ∈ DTIME T` from `M.DecidesInTime L (fun n => c * T n)` today (the only
  introduction lemmas at the head are `mem_DTIME_of_decidesInTimeVia`, which needs `DecidesInTimeVia`, and
  `RAMSimulation/Classes.lean`'s `mem_DTIME_of_decides` for `XProgram`s), so that admitting is the Rule-10-clean
  choice until the pre-approved reader lands;
- that the statement is unchanged and the route stated in the docstring is correct;
- that ownership is named consistently (N28-01): module docstring, contract, corollary, facade, H17, resolutions.

For rating: the `**Status.**` paragraph and the module's "The class" bullet say a proof without the reader "would read
`Turing.FinTM.DecidesInTime`, `Turing.FinTM.DecidesInTimeVia` and `DTIME` by their definitions". The removed proof read
the first two; a direct `⟨c, M, hM⟩` would read `DTIME`. The H17 row names only the first two.

### 4. G28-03 and N28-01, and is anything else new since round 1?

- **G28-03:** the module's `## Consumers` paragraph gives the piecewise test **and** width: below `n₀`, `V₁` on the
  true coins with width `m(n)`; from `n₀` on, `⟨x, u⟩ ↦ M(x; F'(u)↾m(|x|))` with width `ℓ(n)`; and why the width
  alone does not suffice.
- **N28-01:** the module's proof-owner sentence (the `derand` fill proves the contract, the corollary and Theorem
  180.1); the route heading "(the `derand` fill)"; the contract's sketch heading. The derand brief, order and roots
  are updated after the gate, as recorded (not part of this PR).
- **The diffs.** `git diff 8972fb4e 0c04d1eb` touches `SeedMajority.lean` (97 insertions, 26 deletions) and the
  facade's `## Contents` entry (2 insertions, 1 deletion). `pr.diff-r2.txt` is `git diff 013119f0 0c04d1eb`: 2
  paths, 239 insertions, 0 deletions (the new 234-line module; the facade's one import line and its 4-line `##
  Contents` entry). Every other file, every frozen file included, is byte-identical to the base.
- **Headers.** `half_lt_randProb_iff` and `seedMajority_mem_DTIME` have byte-identical headers (keyword to `:=`) at
  `8972fb4e`, `2f9333b9` and `0c04d1eb`; `half_lt_randProb_iff`'s body is unchanged. `exists_seedMajorityTM`'s header
  is byte-identical at `2f9333b9` and `0c04d1eb`.
- **`source-head-r2.json`:** `SeedMajority.lean` SHA-256 `c992181e…`, 234 lines, max width 98; facade `073bb72d…`,
  211 lines, max width 100; none over 100.
- **`sources-r2.zip`:** the source closure at `0c04d1eb` of both changed modules, 308 files, the same paths as the
  round-1 `sources.zip`; only the two changed files differ. `ClassP/ModelInvariance.lean` is not in it; it is in the
  bundle.
- **The base move** (`verification-r2.zip`, `checks/base-move.txt`): every commit from `013119f0` to `c080a840` with
  its non-record paths. Only #311's three commits (`46b780dc`, `542bfb1e`, merge `9c32076f`) touch Lean, in
  `TCSlib/Cryptography/SecureComputation.lean` and `.../SpecialEncryptionMulti.lean`. `git merge-tree --write-tree
  c080a840 0c04d1eb` has no conflict (tree `6d24a1fc…`) and differs from the tip only in #312's two files, each with
  the head blob. None of #312's three declaration names occurs in the tip. Neither PR's modules are in the other's
  import closure; root `TCSlib` and `audits/pass-shelat/Checks` import both.

Do the round-2 edits, or the merged tip, introduce anything that round 1 would have raised?

## Evidence

Both are in `landing-r1/`, each a ZIP with its manifest and `PROVENANCE`. Each ZIP's file entries are its manifest's
paths, under one top folder, plus that folder's `SHA256SUMS`, byte-identical to the manifest; every hash verifies.

| | `stmt-derand-r2-evidence.zip` | `stmt-derand-r2b-evidence.zip` |
|---|---|---|
| SHA-256 | `80123d3de4f30fda800b5b85d1ac6bd6f07c0c231e5660fd61c5ad3693071183` | `146953211c64a6219b427712154fd8effc4004c8dae024f6c625c56f8a0c09cd` |
| Manifest, `PROVENANCE` | `stmt-derand-r2-SHA256SUMS` (118), `stmt-derand-r2-PROVENANCE.txt` | `stmt-derand-r2b-SHA256SUMS` (120), `stmt-derand-r2b-PROVENANCE.txt` |
| Entries | 134 (15 directories, 119 files) | 136 (15 directories, 121 files) |
| Head | `2f9333b9`, corollary proved | `0c04d1eb`, corollary admitted |
| Build | 63/63 rc 0, one `sorry` (`191:8`) | 63/63 rc 0, two `sorry`s (`192:8`, `225:8`) |
| Seal | 5 names; strict seal (informational) fails in the corollary | 7 names, passes |

Round 2b is the evidence for the head; round 2 is kept for the record of the proved corollary and its strict-seal
failure.

**Round 2b, at the head:**
- **Source** (`src/`, `patches/`): `SeedMajority.lean` equal to the head blob (`c992181e…`);
  `patches/0001-*.patch` equals `git format-patch -1 0c04d1eb`; `patches/diff-r2-r2b.txt` equals `git diff 2f9333b9
  0c04d1eb`.
- **Headers** (`checks/headers.txt`): the three headers byte-identical to `2f9333b9`; imports identical to round 1's.
- **Build** (`build/`): from the same olean base as round 1 (source `eff2dcd0`; the 53 changed modules and their
  downstream, 63 modules through root `TCSlib` and `audits/pass-shelat/Checks`). 63/63 rc 0, 0 errors in both forms,
  24 warnings (round 2: 23; the extra is the corollary's `sorry`). The only `sorry` warnings are the two intended ones.
  `SeedMajority`, the facade and root `TCSlib` were built from the head blobs. `audits/pass-shelat/Checks`'s log
  mentions `sorryAx` only for `TCSlib.Cryptography.exists_canonizerExp`, an admission already in the base; it is
  byte-identical to round 2's.
- **Rule 10** (`probes/`): `SealSeedMajority` (the 7 names) rc 0, only the two `sorry` warnings.
  `SealSeedMajorityOwnImports` (the file's own imports, the 6 names in scope) rc 0. The sealed probes add one import,
  `ClassP.ModelInvariance` (marked `PROBE ONLY`), so that the seal can name `DecidesInTimeVia`.
  `SealSeedMajorityControl` adds 4 paired controls (`randProb` by `rfl`; `DTIME` by an anonymous constructor;
  `DecidesInTime` applied as its body; `DecidesInTimeVia` applied as its body): rc 1, exactly 4 errors, one at each
  control (lines 245, 249, 255, 263). `UnsealedSeedMajorityControl`: rc 0.
- **Axioms:** `exists_seedMajorityTM` and `seedMajority_mem_DTIME` use `[propext, sorryAx, Classical.choice,
  Quot.sound]`; `half_lt_randProb_iff` uses `[propext, Classical.choice, Quot.sound]`.
- **Consumer probe** (round 2's file, unchanged): sealed, its control (`DTIME` through its body, line 56) is the only
  error; `ConsumerProbeUnsealed` rc 0.
- **Lint** (`lint/`, `--check8b`, base `2f9333b9`): Cryptography 92 FAIL / 101 WARN and Complexity 25 / 391 at both;
  the FAIL/WARN sets are identical; the only full-diff line is `SeedMajority.lean`'s INFO size line (237 → 234).
- **Restore:** `dl-oleans` back at `457ba704…` (1230 files).

**Not built:** the head merged onto the tip. #311's two files and #312's two files are disjoint, neither PR's modules
import the other's, and the names do not collide, so the merged tree differs from the built one only in #311's
modules and their importers (root `TCSlib`, `audits/pass-shelat/Checks`). Is a trial-merge build needed before #312
can be marked ready, as for #307 at Gate 24?

## Known dispositions and slips (not findings)

- **The host proof is out of scope**, as in round 1; so is the corollary's proof, which waits for `mem_DTIME_iff`.
- **Not exercised here:** the two derand pre-approvals (the `IterateFind` harvest and `mem_DTIME_iff`) and the derand
  brief update (step 4 and checkpoint 1, order and roots), all after the gate.
- **The resolutions' "one place".** `resolutions-r1.md` says the registry row departs from the draft "in one place:
  the corollary is recorded as admitted". It also updates the head from `2f9333b9` to `0c04d1eb` (§ 1 above).
- **The round-2b manifest's paths start with `./`** (`./PROVENANCE.txt`, …); round 2's do not. The hashes verify
  with the prefix removed, and the ZIP's inner `SHA256SUMS` is byte-identical to the manifest.
- **"Nothing pushed" in both PROVENANCE files.** Each was written before the maintainer pushed; round 2b's says that
  `origin/stmt/pass-shelat-derand-host` is still `8972fb4e`. The branch is now at `0c04d1eb` (decision-log row "#312
  round 2 pushed"), the same commit. Round 2b's PROVENANCE names round 2's folder by its job-local name
  `../stmt-derand-r2/`; the records copy is `stmt-derand-r2-evidence.zip`.
- **The GitHub base pin** is still `b12a12f2` (a records commit), as in round 1.
- **The registry's status paragraph** still opens "Status as of 2026-10-12", a pre-existing line.

## Evidence files

- **`resolutions-r1.md`:** the dispositions and § "Round-2 edits".
- **`findings/`:** the round-1 findings.
- **`landing-r1/`:** the H17 draft row, and the two evidence ZIPs with their manifests and `PROVENANCE`.
- **`verification-r2.zip`** (6 entries; `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each source):
  byte-identical originals at records `c080a8406f5a8f8d29e5cf1787162d26a1d8a64c` of `machine-library-design.md` (§14,
  H17) and the decision log; and `checks/`, generated from git alone: the registry diff since round 1 and
  `base-move.txt`.
- **`pr.diff-r2.txt`:** `git diff` from the base to `0c04d1eb`, 2 paths, 239/0.
- **`source-head-r2.json`:** hashes, line counts and over-width counts of the 2 changed files at `0c04d1eb`.
- **`sources-r2.zip`:** the source closure at `0c04d1eb` of both changed modules, 308 files.
- **Round 1:** `outbox/gates/28-derand-host-gate/` on the exchange at `2776272b61fcc7a1adf3f743c735c7e45be5045c`, with
  records `1ea6503c82b12fd7e49c2e621fcae4cd29d9d08c` (its `verification.zip` holds the round-1 evidence, the derand
  issue package, the duplication ledger and the round-1 registry).

## Findings delivery

Return `gate28-derand-host-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP.
Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report the audited
head and the counts by severity. The gate closes at zero blockers and zero majors.
