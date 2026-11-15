## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/pack-r2.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/resolutions-r1.md =====

# Gate 28 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 1 minor, 1 note.
- **Findings:** `findings/gate28-derand-host-findings.md`.
- **Audited head:** `8972fb4ef15fa3d4e3df37d6aa8674408835593d`.
- Codex found the mathematics sound. The contract is true, including ties, `w = 0`, `m = 0` and small `n`. It is
  sufficient for Theorem 180.1 by the full paper proof, which Codex rechecked. The route is feasible.

| # | Severity | Disposition |
|---|---|---|
| G28-01 | major | **To fix in records.** Register host **H17** in `machine-library-design.md` §14. The entry records the contract, home, reader, Gate 28 status, proof owner (the `derand` fill), consumers, route and the G28-02 disposition. It accompanies round 2. |
| G28-02 | major | **Ruling (Seyoon, 2026-11-15): add a machine-level contract.** #312 is revised to state a shared host contract that ties correctness, time and a coarse head envelope (derived from the time bound) to the **same machine**. `seedMajority_mem_DTIME` is kept as its corollary. The admitted `loopHostTM_*` space specs must not be used. Gate 28 then has a round 2. |
| G28-03 | minor | **To fix in round 2.** The consumer paragraph will give the piecewise test **and** width from the paper proof: true coins and `m(n)` below the threshold, `F'(u)↾m` and `ℓ(n)` from it on. |
| N28-01 | note | **To fix in round 2.** The proof owner is named consistently: the `derand` fill proves the host and the theorem. The `derand` brief, order and roots are updated after the gate, together with the two pre-approved shared-file changes. |

## Round-2 edits (head `0c04d1eb1e5450372632a23f3e94f3b7bfc37606`)

- **G28-01 · done.** H17 is registered in `machine-library-design.md` §14 (records), with a line in the status
  paragraph. The row gives the contract, its home, the reader, the gate status, the proof owner (the `derand` fill),
  the consumers, the route and the head-envelope clause. The draft is kept as `landing-r1/H17-row-draft.md`.
  - The registry row departs from the draft in one place: the corollary is recorded as admitted, as below.
- **G28-02 · done** by `2f9333b9`. The new existential contract `exists_seedMajorityTM` gives one machine `M`
  with constants `c, e` and two properties:
  - `M.DecidesInTime S (n ↦ c·(2^{w n}·(n+1)^e))`;
  - the head envelope `|workTapePos j| ≤ c·(2^{w|x|}·(|x|+1)^e)` for every input, time and tape. This is H14's
    `Clean.envelope` form, derived from the time bound. No admitted space spec is used.
  - The contract stays sorried for the `derand` fill.
- **The corollary · admitted** (`0c04d1eb`). Round 2 first proved `seedMajority_mem_DTIME` from the contract. That
  proof read `FinTM.DecidesInTime` and `DecidesInTimeVia` by their definitions, which Rule 10 forbids, so the
  maintainer reverted it to `sorry`.
  - It follows from the contract through the reader `mem_DTIME_iff`. The `derand` fill adds that reader under its
    pre-approval, and proves the corollary as well.
  - The whole-file seal now also seals `DecidesInTime`, `DecidesInTimeVia` and `DTIME`, and passes.
  - The paired controls, two of them new, each fail exactly once sealed.
- **G28-03 · done.** The consumer paragraph gives the piecewise test and width.
- **N28-01 · done.** The proof owner is named consistently: the `derand` fill proves the contract, the corollary
  and Theorem 180.1.
- **Build and lint.** 63/63 modules give rc 0 through root `TCSlib`. The only `sorry`s are the contract and the
  corollary. Lint is unchanged: Cryptography 92/101, Complexity 25/391.
- **Evidence.** In `landing-r1/`:
  - `stmt-derand-r2-evidence.zip`, SHA-256 `80123d3de4f30fda800b5b85d1ac6bd6f07c0c231e5660fd61c5ad3693071183`;
  - `stmt-derand-r2b-evidence.zip`, SHA-256 `146953211c64a6219b427712154fd8effc4004c8dae024f6c625c56f8a0c09cd`.

Round 2 of Gate 28 goes to Codex next.

## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/findings/gate28-derand-host-findings.md =====

# Pass–shelat Gate 28 — derandomization host statement audit

**Verdict: HOLD.** **0 blockers, 2 majors, 1 minor, 1 note.**

The mathematical contract and probability reader pass this statement audit. The contract is
sufficient for the paper proof of Theorem 180.1. Closure is held on the host-policy issues below;
the intended `sorry` is not a finding. No dispatch, repository write, or merge was performed.

| Item | Audited revision |
|---|---|
| Draft PR | [#312](https://github.com/Shilun-Allan-Li/tcslib/pull/312) |
| Lean head | `8972fb4ef15fa3d4e3df37d6aa8674408835593d` |
| Lean merge base | `013119f006af40d03b88b0fc2d9b453cf0a9b348` |
| Campaign records | `1ea6503c82b12fd7e49c2e621fcae4cd29d9d08c` |
| Exchange | `2776272b61fcc7a1adf3f743c735c7e45be5045c` |

## Findings

Paths in this table are repository paths. Line numbers refer to the pinned files.

| ID | Severity | File / declaration | Finding and evidence | Proposed fix |
|---|---|---|---|---|
| G28-01 | **major** | `machine-library-design.md` §14; `seedMajority_mem_DTIME` | H17 is absent from the actual host registry. The only row is a draft in `briefs/pass-shelat-ch5-8/maintainer/stmt-derand-2026-11-15/pr-body.md:182`. Policy §1's review checklist requires a registered public host. The same campaign treated missing H15 registration as G08-01, a major (`PassShelatChapter5-8Plan.md:413–421`). Disclosure of this omission does not discharge it. | Enter H17 in the canonical registry before or with the statement landing, before briefing the consumer against it. Record the contract, home, reader, Gate 28 status, proof owner, consumers, route, and disposition of G28-02. A registry-only repair can accompany this statement gate; it need not await the host proof. |
| G28-02 | **major** | `TCSlib/Complexity/Randomized/SeedMajority.lean:71–72,149–154`; policy §1 | The proposed host deliberately has no space/head-envelope clause. Policy §1:113–117 expressly requires such a clause; the two recorded derand pre-approvals concern the generic-fuel harvest and `mem_DTIME_iff`, not an exception to that requirement (`PassShelatChapter5-8Plan.md:698`). Calling the contract a decision-layer membership does not itself record an exception. | Retain the useful `DTIME` corollary, and expose a shared host contract tying correctness, time, and a stated head envelope to the **same machine**; alternatively obtain and record Seyoon's explicit approval of this time-only decision-layer interface. A coarse envelope derived from the time bound suffices for the literal policy; no polynomial-space strengthening is required by this finding. Do not use the admitted `loopHostTM_*` space specifications as if proved. |
| G28-03 | **minor** | `TCSlib/Complexity/Randomized/SeedMajority.lean:54–56` | The displayed consumer test always applies `G`, while the next clause says true coins below a threshold are handled by changing the width. Changing the width alone does not remove the generator. The correct paper proof changes **both** the test and width (`pr-body.md:113–121`). PRG security imposes no correctness guarantee on finitely many exceptional seed lengths. | Give the piecewise test and width from the paper proof in this consumer paragraph: use the original seed below the threshold and the generator output from the threshold on. |
| N28-01 | note | `SeedMajority.lean:26`; PR description; issued derand brief | “The proof is a separate fill” can mean separate from the statement phase; the PR description assigns both proofs to derand. This is ambiguous ownership prose, not a mathematical contradiction. The issued brief still has its old host scope-request checkpoint; its post-gate update is already recorded. | Name the proof owner consistently and update the issued brief/order/roots before dispatch, including the two pre-approved shared-file changes. |

**G28-02 precedent considered.** H15 was accepted as a high-level polynomial-time interface without
a separate machine envelope; the registry records that choice explicitly. This is relevant
precedent for requesting the same treatment here. It is not a blanket change to policy §1 or a
recorded ruling for H17. Conversely, Gate 03l round 2 treated H14's missing envelope as a major
and repaired it. I do not silently choose a new exception between those precedents. The shared
`Complexity/Randomized/` location is appropriate for the decision corollary; its pathname is not
an additional finding.

## Integrity and evidence

- The outer `SHA256SUMS` verifies **10/10** files. In particular, `bundle.md` is
  `b07f60050d951bb5cf9e90f4dea56a1263636b891fb5c6e79473021b8e36cb60`.
- `verification.zip`: **44/44** manifest entries verify; its 45 file entries are exactly those
  entries plus `SHA256SUMS`. The nested maintainer archive verifies **106/106** entries and has
  exactly 107 files. Its manifest equals `evidence-SHA256SUMS`; all **27** evidence extracts are
  byte-identical to their originals.
- All **308** source files in `sources.zip` match their Git blob IDs in the independently
  retrieved, nontruncated tree at the Lean head. All **11** bundle sections match the specified
  Lean/records blobs after removing only the bundle's separator newline where present.
- The independently retrieved base/head comparison has one commit and exactly two changed
  paths: the new 163-line module and four facade lines, **167 additions / 0 deletions**. No
  frozen Lean file changed. Both head source SHA-256 values match `source-head.json`.
  GitHub’s target pin is `b12a12f2`; the two base-to-records-tip commits through `41e3cd2a`
  change only campaign records and the two statement-evidence folders, as disclosed.
- The archived plan is explicitly from records `41e3cd2a`, as its provenance says. Compared
  with the requested records pin, it lacks only the final Gates 27–28 staging row. I read that
  newer row too; it adds no space-clause exception. Policy, registry, duplication ledger, brief,
  and full paper-proof text were checked against the requested records pin.
- The 63 recorded module builds all report return code 0 and zero errors. I recomputed every
  archived build-log hash and both diagnostic forms. The sole reported sorry warning is the
  authorized contract at `SeedMajority.lean:154:8`. The before/after object-tree snapshots match.
  Independent width checks give 163/97 and 210/100 for lines/maximum width.

**Limit:** Lean and its compiled dependencies are absent from this audit environment. I did not
rerun Lean or independently reproduce the 63 builds, seals, or axiom prints. Their authenticated
source/log pairs were inspected and checked for internal consistency. The attached verifier
reproduces the byte, archive, width, and log checks; it does not prove the sorried host.

## Truth and boundary cases

For the reader, let `count` be the displayed filter cardinality. In the rationals,

\[
  2^m>0,\qquad
  \frac12<\operatorname{randProb}(m,A)
  \iff \frac12<\frac{\mathrm{count}}{2^m}
  \iff 2^m<2\,\mathrm{count}.
\]

This is exactly `randProb_eq` followed by positive-denominator multiplication and natural-to-
rational casts. The new proof performs those operations through the published reader. A tie
has `2 count = 2^m`, so both strict inequalities are false. For `m=0`, there is exactly one
function `Fin 0 → Bool`, whose list is `[]`; `count` is 0 or 1. Thus the reader and the host
reduce to the single empty-seed test, with no division by zero or tie convention change.

For the host, fix an input of length `n` and put `R = 2^{w(n)}`. The width hypothesis gives

\[
  w(n)\le C(n+1)^c
\]

by applying `PolyTimeComputable.output_length_le` to any word of length `n`. Enumerate ranks
`0,…,R−1`, and maintain

\[
  \mathrm{count}_i
   =\#\{j<i:\operatorname{pairEncode}(x,\mathrm{word}_{w(n)}(j))\in V\},
  \qquad 0\le\mathrm{count}_i\le i\le R.
\]

Initialize `i=count=0`; each nonterminal step tests rank `i`, adds its Boolean verdict, and
increments `i`. Induction on `i` proves the invariant. At `i=R`, fixed-width binary expansion
is a bijection from the ranks onto `Fin (w n) → Bool`, so `count_R` is precisely the theorem's
cardinality. Emit the one-bit strict comparison. This establishes the mathematical correctness
argument, including rejection on ties.

The binary rank and count each need at most `w(n)+1` bits, including the terminal value `R`.
The paired state consequently has length at most `2n+3w(n)+7`. Computing the unary width,
padding a seed, running the `P` test, updating the counters, and the final comparison all have
a common polynomial budget `T(n)`. For suitable constants `A,e`, take

\[
  T(n)+1\le A(n+1)^e,\qquad
  R+2\le3R,\qquad
  c_0(T(n)+1)(R+2)\le3c_0A\,2^{w(n)}(n+1)^e.
\]

The constant is absorbed in `DTIME`. At `n=0`, the bound is positive (`2^{w(0)}`), and the
constant covers initialization and the fixed width-computation cost. At lengths with `w(n)=0`,
there is one test and polynomial time. No lower bound on `w`, monotonicity, or time-
constructibility of an arbitrary numerical time function is needed.

This is a mathematical proof plan, not a completed Lean proof. The fill must supply the
enumeration bijection, invariant, polynomial-time components, and machine composition.

## Sufficiency for Theorem 180.1

The full `pr-body.md` route is sound. It also matches the frozen theorem's intended proof:

1. From `InBPP polyTimeModel L`, use its Boolean verifier and `polyTimeModel_eff_iff` to obtain
   the accepting paired language `V₁ ∈ P`. Set `m(n)=a(n+1)^k`. Choose fixed `d≥2` with
   `1/d<min(ε,1)` and `ℓ(n)=min{t:n≤t^d}`. Here `ℓ(0)=0`; for `n≥1`, searching `t≤n`
   computes its unary word in polynomial time. No real exponent is computed by a machine.
2. Expand to the syntactic polynomial `P(s)=a(s^d+1)^k+s+1`, using one-bit truncation and
   `prg_expand`; obtain evaluator `F'` through `PRG.easy_iff`. The inequalities
   `P(s)>s` and `m(n)≤P(ℓ(n))` hold at every length, including zero.
3. If the probability gap exceeds `1/12` at infinitely many input lengths, it does so at
   infinitely many seed lengths: `ℓ(n)=s` implies `n≤s^d`, so each fiber is finite. Choose one
   bad input `x_s` for each such `s`, with empty advice otherwise. Its length is at most `s^d`.
   The deterministic test `y ↦ M(x_s; y.take(m(|x_s|)))` is polynomial-time with this advice.
   `verifier_toNUPPT` applies to the efficient prefix-truncated verifier. Uniform prefix
   projection and `randProb_eq_uprob` identify its advantage with the bad gap. By
   `PRG.secure_iff` this advantage is negligible, contradicting infinitely many values above
   `1/12` (already the inverse-linear bound contradicts this for sufficiently large `s`).
4. Therefore a fixed threshold `n₀` exists. Define the paired test and width **together**:

   \[
   w(n)=\begin{cases}m(n)&n<n_0,\\\ell(n)&n\ge n_0,\end{cases}
   \qquad
   V''(\langle x,u\rangle)=
   \begin{cases}
     V_1(\langle x,u\rangle)&|x|<n_0,\\
     V_1(\langle x,(F'(u)).\mathrm{take}(m(|x|))\rangle)&|x|\ge n_0.
   \end{cases}
   \]

   Both are polynomial-time: hard-code the single natural `n₀`, use integer-root search,
   pairing, prefix truncation, and `P` closure. A threshold obtained by classical existence is
   harmless: the theorem asks for an existential decider, not a uniform procedure extracting
   that decider from a security proof. Extend the test on raw words using the total pairing
   projections; behavior on malformed words is irrelevant to its paired-input specification.
5. Below the threshold, true-coin acceptance is at least `2/3` on members and at most `1/3`
   on nonmembers. From the threshold on, the respective bounds are
   `2/3−1/12=7/12>1/2` and `1/3+1/12=5/12<1/2`. The reader therefore identifies `L` exactly
   with the host's strict-majority language. This handles all finite exceptions without a
   separate finite-table machine.
6. The host gives some `e`. Eventually `w(n)=ℓ(n)≤n^{1/d}+1`, and

   \[
   \log_2\!\left(2^{w(n)}(n+1)^e\right)
     \le n^{1/d}+1+e\log_2(n+1)\le n^\varepsilon.
   \]

   The last inequality is eventual because `1/d<ε`. Rounding up preserves the upper bound.
   Since `subexpBound ε n≥1` at every length, one natural constant absorbs the finitely many
   exceptions. `DTIME.mono` and `DTIME_const_mul_subset` finish exactly as in `ConsumerProbe`.

The compiled consumer probe checks only the final transport from a supplied pointwise bound.
It does not establish steps 1–5 or the asymptotic inequality; those remain the derand fill's
proof obligations. Polynomial prefix truncation is available directly as
`Complexity.polyTimeComputable_pairTakePoly`; the fill need not unfold the older
`takePrefixByLen` definition to implement this step.

## Generality, route, and Rule 10

- A `P` test on `pairEncode x u` is sufficient for both named consumers and matches
  `polyTimeModel`. Neither presently needs an arbitrary-time leaf, a variable threshold, or
  the numerical count as output. The unary computability hypothesis is useful: a merely
  polynomially bounded width could be uncomputable. It also permits the required piecewise
  integer-root schedule. These design restrictions are not mathematical defects.
- A `DTIME` membership is enough for the theorem's decision-class conclusion. A consumer
  needing a clean submodule or a head bound would require a machine-level interface; that is
  the policy issue in G28-02, not a failure of Theorem 180.1's reduction.
- `exists_loopFindTM` quantifies over arbitrary `R,T : ℕ→ℕ`; it does not require polynomial
  fuel. Its fuel machine outputs **binary** `Nat.bits (2^{w(n)})`, of length `w(n)+1`, not an
  exponential-length unary word. The conclusion searches `List.range (R(n)+1)`, so it includes
  the terminal index `R(n)` and allows `R(n)` seed tests followed by the payload round.
- The invariant must be closed under the total step function, as required by `hInvStep`.
  Make terminal states fixed, or use the existing size guard; never assume an unbounded
  increment preserves a fixed state bound after termination. The approved generic-fuel
  harvest can retain `Inv` and the word adapters in their original shared file. The existing
  polynomial-fuel `final_bound` cannot be applied to exponential `R`; use the direct bound
  displayed above instead. These are feasible fill obligations, not a need to change the
  statement. The 900–1,600-line estimate is plausible but is not a verified size guarantee.
- The 26 route-lemma axiom records contain only the standard axioms. In particular, the
  proved `exists_loopFindTM` uses private `loopHost_contracts`, rather than the admitted
  `loopHostTM_*`/`timedCondTM_*` specification theorems. The approved `mem_DTIME_iff` addition
  supplies the missing introduction reader for the later proof.
- The new reader uses `randProb_eq` and arithmetic lemmas; no forbidden definition read was
  found. The host introduces no definition. The whole-file seal succeeds; its body-reading
  control fails once and passes unsealed. The consumer's `DTIME` constructor control likewise
  fails once sealed and passes unsealed. Classical decidability causes no mismatch: the
  decisions for a fixed proposition are subsingleton, and both counts describe the same event.
- The existential projection decider computes an any-verdict at fixed polynomial width;
  block-majority counts polynomially many supplied blocks; H16 performs one round per
  **counter letter**. None supplies this exponential seed-majority contract at polynomial
  state size. The approved shared harvest avoids copying the private `IterateFind` machinery.
  No duplicate public result or new copied proof was found in this statement change.
- The theorem docstrings state their formulas and source locations; the host has a deviation
  note and proof sketch. The proof reader is short enough not to require an additional sketch.
  The facade imports the new module, and the pinned root imports the Randomized facade.

## Sources and reproducibility

Primary source checked: Pass–shelat, *A Course in Cryptography*, third edition, §8.2,
[Theorem 180.1, printed p. 180](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf).
The source's exhaustive-seed argument supports the contract; the integer-root schedule,
nonuniform-advice argument, and all-length repair are explicit elaborations checked above.
The repository's [AB09] enumeration attribution is consistent with that standard argument.

The evidence ZIP contains this report, `verification-results.json`, the offline verifier,
Git-blob maps, repository comparison metadata, and focused source/policy excerpts. To rerun
the byte checks, place the verifier and both Git-blob maps together and run:

```sh
python3 verify_gate28.py /path/to/outbox/gates/28-derand-host-gate
```

**Glossary.** `count` is an accepting-seed cardinality; `count_i` is the tally before rank `i`;
`word_w(i)` is the width-`w` binary expansion of `i`; `R=2^{w(n)}` is the seed count; `T` is a
common per-round polynomial budget; `C,c,A,c₀,e` are fixed natural bounds/constants. In the
consumer argument, `M` is the BPP verifier, `V₁` its accepting paired language, `m(n)=a(n+1)^k`
its coin width, `d` the fixed root degree, `ℓ(n)` its ceiling-root schedule, `s` a seed length,
`P(s)` the polynomial PRG stretch envelope, `F'` its evaluator, `x_s` an advised bad input,
`n₀` the finite-exception threshold, and `V''` the piecewise paired test. `ε>0` is the requested
subexponential exponent; `x,n,u,i,A` otherwise have the input/length/seed/rank/event meanings
in the audited statements (`A` in the probability reader is an event, not the budget constant).

## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/landing-r1/H17-row-draft.md =====

# H17 registry row (draft for `machine-library-design.md` §14; Gate 28, G28-01)

Not entered in the records by this job. The maintainer adds it. Pipes inside cells are escaped
(`\|`), as in row H14.

**Registry table row** (append after H16):

| H17 | **Seed-majority enumeration host:** `Complexity.exists_seedMajorityTM`, in `TCSlib/Complexity/Randomized/SeedMajority.lean`. Take a test `V ∈ P` read on `Turing.pairEncode x u`, and a width `w : ℕ → ℕ` whose unary word `x ↦ 1^{w(\|x\|)}` is polynomial-time computable. Then one finite machine `M`, with constants `c, e` and the budget `B(n) = c · (2^{w(n)} · (n+1)^e)`, satisfies both clauses. Correctness and time: `M` decides the strict-majority language `S = {x \| 2^{w(\|x\|)} < 2 · #{u : Fin (w \|x\|) → Bool \| pairEncode x (List.ofFn u) ∈ V}}` within `B` (`M.DecidesInTime S B`); ties reject. Head envelope: `\|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j\| ≤ B \|x\|` for every input `x`, time `v` and work tape `j`. This is the coarse envelope derived from the time bound, in the form of H14's `Clean.envelope`. The contract is existential and introduces no definition. Corollary: `Complexity.seedMajority_mem_DTIME`, `∃ e, {x \| …} ∈ DTIME (n ↦ 2^{w(n)} · (n+1)^e)`. It is proved from the contract through `mem_DTIME_of_decidesInTimeVia`, `DTIME.mono` and `Randomized.DTIME_const_mul_subset`. Reader: `Randomized.half_lt_randProb_iff`, `1/2 < randProb m A ↔ 2^m < 2 · #{r \| A r}` (proved). Route: a state loop `⟨x, ⟨i, a⟩⟩` keeps the binary seed rank and the acceptance count. It runs through `Turing.FinTM.exists_loopFindTM` over the clean-module host (H14) with exponential fuel `Nat.bits (2^{w(\|x\|)})`, through the pre-approved generic-fuel harvest `computesFunInTime_find`. Its bound `c₀ (T(n) + 1)(2^{w(n)} + 2)` has `T` polynomial. The envelope follows from that time bound: the heads start at the origin, move by at most one cell per step (`MultiTapeTM.workTapePos_runFrom_mem_Icc`), and stay put after the halt. The admitted `loopHostTM_*`/`timedCondTM_*` space specifications are not used. | **Statement only**, in draft PR #312 (`stmt/pass-shelat-derand-host`, round-2 head `2f9333b99b83fdd6accb29926fab38fd75f66897`). **Gate 28** round 1: HOLD (0 blockers, 2 majors, 1 minor, 1 note), audited head `8972fb4ef15fa3d4e3df37d6aa8674408835593d`. Round 2 is pending on this head. G28-02 disposition: Seyoon's ruling, 2026-11-15. The host states a machine-level contract tying correctness, time and a coarse head envelope, derived from the time bound, to the same machine. No time-only exception is recorded. `seedMajority_mem_DTIME` is kept as its corollary. The host proof is `sorry`, assigned to the **`derand` fill**, which proves both the host contract and Theorem 180.1. The fill has two pre-approved shared-file changes: the generic-fuel `computesFunInTime_find` in `Randomized/Build/IterateFind.lean`, and `mem_DTIME_iff` beside `DTIME`. Registered 2026-11-15 (Gate 28, G28-01). | `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` (derand, [PS10, Thm 180.1]) uses the corollary with the piecewise test and width. Below `n₀` these are the true coins and `m(n)`; from `n₀` on, `F'(u)↾m(\|x\|)` and `ℓ(n)`. Prospectively, `BPP ⊆ EXP` by coin enumeration [AB09, §7.1, p. 126] (`w = polyLen a k`), which today goes through Sipser–Gács. |

**Companion sentence** for the registry's status paragraph (after "H15 was registered 2026-11-06
PST …"):

> H17 was registered 2026-11-15 for the derand host statement gate (Gate 28, G28-01).

## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/landing-r1/stmt-derand-r2b-PROVENANCE.txt =====

Seed-majority host statement, round 2b (Rule 10: corollary admitted until mem_DTIME_iff), #312.
Nothing pushed. Prepared 2026-11-15 UTC by Claude (session_01PqpVTiuDcjSqhyfbqnsVxA).
Method and tools: ../stmt-derand-r2/ (PROVENANCE.txt), copied into tools/ unchanged, plus
tools/rawheaders.py, tools/mkprobes.py, tools/edit.py (new; each has its own docstring).

why      seedMajority_mem_DTIME was proved from exists_seedMajorityTM through
         mem_DTIME_of_decidesInTimeVia, DTIME.mono and DTIME_const_mul_subset, but its proof
         read Turing.FinTM.DecidesInTime (ClassP/DTIME.lean) and Turing.FinTM.DecidesInTimeVia
         (ClassP/ModelInvariance.lean) by their definitions (round 2's StrictSealSeedMajority
         failed exactly there). Rule 10 forbids that.

source
  branch   stmt/pass-shelat-derand-host (local), worktree $SP/wt-stmt-derand: sparse checkout
           (no-cone, '/*' '!/briefs/'; per-worktree config.worktree), so briefs/ was never
           checked out; .lake/packages symlinked to the main checkout. Worktree removed at the
           end (symlink unlinked, then `git worktree remove`); branch kept.
  parent   2f9333b99b83fdd6accb29926fab38fd75f66897 (round-2 head; git rev-parse)
  head     0c04d1eb1e5450372632a23f3e94f3b7bfc37606
  tree     2a3a58ab0e422d06f2d8d13d1d9e8a8820f09bea
           1 commit, author = committer = Claude <noreply@anthropic.com>, 2026-11-15T03:59:49Z
           (patches/COMMITS.tsv, patches/0001-*.patch, patches/commit-message.txt)
           origin/stmt/pass-shelat-derand-host still 8972fb4e (round 1): nothing pushed.
  changed  M TCSlib/Complexity/Randomized/SeedMajority.lean only (234 lines, max width 98,
           sha256 c992181ea4cf9e85af6cb1982aa100a5ecd2aabf46e0a8955ba0398e7e0d5356; src/ holds it).
           patches/diff-r2-r2b.txt (vs 2f9333b9), patches/diff-r1-r2b-SeedMajority.txt (vs 8972fb4).

edit
  proof    seedMajority_mem_DTIME: body is now `sorry` (10 proof lines removed).
  docs     its docstring gains a **Status** paragraph: admitted; it follows from
           exists_seedMajorityTM via the reader Complexity.mem_DTIME_iff, which the derand fill
           adds beside DTIME (ClassP/DTIME.lean) under its pre-approval (Seyoon, 2026-11-15);
           the derand fill proves both the contract and this corollary; without the reader a
           proof would read DecidesInTime, DecidesInTimeVia and DTIME by their definitions
           (Rule 10). Its proof sketch now runs through mem_DTIME_iff only: the contract's
           budget is literally c * T n with T n = 2^{w n} (n+1)^e, so <c, M, hM> is the
           witness, with no mono / constant absorption.
           Module docstring, for consistency with that: "The class" bullet (was "proved from
           the contract through DTIME's published lemmas only") and the Main results entry
           (was "proved from the contract") now say admitted until mem_DTIME_iff; the
           Proof owner sentence names the corollary as well. Facade entry neutral, unchanged.
  imports  dropped TCSlib.Complexity.ClassP.ModelInvariance and
           TCSlib.Complexity.Randomized.QuasiPolyHierarchy: round 2 added both for the removed
           proof only (mem_DTIME_of_decidesInTimeVia / DTIME_const_mul_subset); every name the
           statements use (FinTM, DecidesInTime, runFrom, workTapePos, DTIME, P) comes through
           ClassP.P -> ClassP.DTIME -> TuringMachine.Finite. The module builds without them.
           Imports are now identical to round 1 (8972fb4).

checks
  headers  checks/headers.txt: codecmp.py (comment-blanked, whitespace-normalised): 3 headers,
           identical to 2f9333b9. rawheaders.py (raw bytes, keyword to first :=): 3/3
           byte-identical (half_lt_randProb_iff, exists_seedMajorityTM, seedMajority_mem_DTIME,
           SHA-256 of each listed). Only file changed: SeedMajority.lean.
  widths   checks/widths.txt: 234 lines, max width 98. RESULT OK.
  lint     campaign_style_lint.py --check8b, base = 2f9333b9 (git archive of scripts/ and
           TCSlib/ to $SP/r2bwork/base-2f9333b9, removed afterwards), head = worktree:
           Cryptography 92 FAIL / 101 WARN both; Complexity 25 FAIL / 391 WARN both.
           FAIL/WARN sets identical (lint/failwarn-*.diff empty); full diffs: Cryptography
           empty, Complexity the one INFO size line (237 -> 234 lines). Raw FAIL/WARN lines
           also identical to round 2's head logs. No new FAIL. (fw-*.txt here collapse runs
           of spaces, unlike round 2's; the raw comparison above is the like-for-like one.)

olean tree $SP/dl-oleans only (dl-oleans-2 untouched; a concurrent job's Lean process used
         dl-oleans-2 exclusively, checked from its command line and environment)
  pre      tree/snapshot-pre.txt: 1230 files, 0 empty dirs, SHA-256
           457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f, byte-identical to
           ../stmt-derand-r2/tree/snapshot-pre.txt; tree/snapshot-prebuild.txt same.
  order    order/changed.txt (git diff eff2dcd0..head, 53 modules) -> downorder.py ->
           order/build-head.txt, 63 modules imports-first; changed, order, backup and new lists
           identical to round 2. order/backup.txt: 20 base oleans copied aside to
           $SP/r2bwork/backup (order/backup-sha256.txt); order/new.txt: 43 head-only.
  build    runner.py via scripts/lean_check_tree.sh (byte-identical to /home/user/tcslib's),
           TCSLIB_OLEANS=$SP/dl-oleans, one Lean process at a time: build/results.jsonl,
           build/mods/*.log, build/runner.out (runner rc=0).
           63/63 rc 0; errors 0 (both forms); substring "error" 0 times; 24 warnings (round 2:
           23; the one extra is the new intended sorry). The only sorry warnings:
             SeedMajority.lean:192:8  exists_seedMajorityTM   (intended, as before)
             SeedMajority.lean:225:8  seedMajority_mem_DTIME  (intended, new)
           SeedMajority, facade TCSlib/Complexity/Randomized and root TCSlib rc 0, source
           SHA-256 = head blobs. Full downstream incl. audits/pass-shelat/Checks rc 0.
  probes   tools/probe.sh (lean without -o, cwd = worktree), run while the build's oleans were
           in the tree; probe files generated by tools/mkprobes.py from the head source; logs
           name them by their scratch path $SP/r2bwork/probes/.
           Whole-file seal now: randProb, DTIME, P, PolyTimeComputable, pairEncode,
           Turing.FinTM.DecidesInTime, Turing.FinTM.DecidesInTimeVia. SeedMajority no longer
           imports ModelInvariance, so the sealed probes add that one import line (marked
           PROBE ONLY) solely so the seal can name DecidesInTimeVia.
           SealSeedMajority: rc 0, only the two intended sorry warnings (198, 231 = 192, 225 + 6).
           SealSeedMajorityOwnImports (file's own imports, the six names in scope): rc 0, the
             two sorry warnings only.
           SealSeedMajorityControl: + 4 paired controls (1 randProb by rfl; 2 DTIME by
             anonymous constructor; 3 DecidesInTime applied as its body; 4 DecidesInTimeVia
             applied as its body): rc 1, exactly 4 errors, one at each control (245, 249, 255,
             263). UnsealedSeedMajorityControl: rc 0 (all four controls elaborate).
             Axioms: exists_seedMajorityTM, seedMajority_mem_DTIME [propext, sorryAx,
             Classical.choice, Quot.sound]; half_lt_randProb_iff [propext, Classical.choice,
             Quot.sound].
           ConsumerProbe (round 2's file, unchanged; sealed DTIME, randProb, P,
             PolyTimeComputable, pairEncode, subexpBound): rc 1, its control (DTIME through its
             body, line 56) the only error; transport_general and the subexpBound instance
             elaborate. ConsumerProbeUnsealed: rc 0.
  restore  restore/restore-log.txt: 20 backups copied back, 43 new oleans removed (incl.
           SeedMajority), 5 emptied directories removed. restore/snapshot-post.txt
           byte-identical to tree/snapshot-pre.txt (and to round 2's), SHA-256
           457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f, 1230 files,
           0 empty dirs. RESULT OK.

toolchain  Lean 4.25.0 (PATH=$HOME/.elan/bin:$PATH). No lake build, no lake exe cache get.
           Python: python3 -I. /home/user/tcslib working tree not edited (git status clean).
SHA256SUMS: every file here except itself; ../stmt-derand-r2b-evidence.zip holds this folder.

## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/landing-r1/stmt-derand-r2-PROVENANCE.txt =====

Seed-majority host statement, round 2 (Gate 28 round-1 resolutions), #312. Nothing pushed.
Prepared 2026-11-15 UTC by Claude (session_01PqpVTiuDcjSqhyfbqnsVxA).

read first   briefs/pass-shelat-ch5-8/gates/28-derand-host/findings/gate28-derand-host-findings.md (in full),
             .../28-derand-host/resolutions-r1.md, policy.md §1 (Hosts come first: time and head-envelope clauses),
             machine-library-design.md §14 rows H14-H16, TuringMachine/Build/ModuleHost.lean (Clean,
             Clean.envelope, host_clean_envelope), ClassP/BinaryArith/Loops.lean (H16 has no envelope of its own;
             its registry row composes with H14's clean_install and Clean.envelope).

source
  branch   stmt/pass-shelat-derand-host (local), worktree $SP/wt-stmt-derand (.lake/packages symlinked to the main
           checkout; the 1.6 GB briefs/ folder deleted from the worktree's working copy only, never staged)
  parent   8972fb4ef15fa3d4e3df37d6aa8674408835593d (round-1 head = origin head, checked with git rev-parse)
  head     2f9333b99b83fdd6accb29926fab38fd75f66897
  tree     528e9c7d0e6b16a68ea1745bb6bd3008e4adf272
           1 commit, author = committer = Claude <noreply@anthropic.com> (patches/COMMITS.tsv, patches/0001-*.patch)
  changed  M TCSlib/Complexity/Randomized/SeedMajority.lean (237 lines, sha256 e6e50aee2ee62d1f181aa988db298d55907baa597ffaf91c80ff61e3146f3ead)
           M TCSlib/Complexity/Randomized.lean (facade, Contents entry only; 211 lines, sha256 073bb72d696d715a908fea7aa1ed7600886811a7698b24d672c1b2dd863f8c18)
           src/ holds both at head; patches/diff-r1-r2.txt, patches/diff-base-r2.txt (vs PR base 013119f0).

resolutions
  G28-02   new sorried contract Complexity.exists_seedMajorityTM (checks/contract.txt, full text): one FinTM M and
           constants c e with B(n) = c * (2^(w n) * (n+1)^e): M.DecidesInTime <majority language> B, and
           |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| <= B |x| for all x, v, j (coarse time-derived head
           envelope, the form of H14's Clean.envelope). Existential; no definition introduced.
           seedMajority_mem_DTIME: statement unchanged; now PROVED from the contract through
           mem_DTIME_of_decidesInTimeVia (Function.Embedding.refl Bool), DTIME.mono and
           Randomized.DTIME_const_mul_subset (published; axioms propext, Classical.choice, Quot.sound). It reads
           the machine predicates FinTM.DecidesInTime / FinTM.DecidesInTimeVia by their formulas (application,
           Function.Embedding.coe_refl, List.map_id): probes/StrictSealSeedMajority (informational) seals those two
           as well and fails exactly there (2 errors, both inside seedMajority_mem_DTIME). DTIME itself is sealed
           in every probe. No loopHostTM_* / timedCondTM_* lemma is cited. New imports (intended):
           TCSlib.Complexity.ClassP.ModelInvariance, TCSlib.Complexity.Randomized.QuasiPolyHierarchy.
  G28-03   module docstring "## Consumers": piecewise test and width (below n0: V1 on the true coins, width m(n);
           from n0 on: M(x; F'(u)|m(|x|)), width l(n)), and why the width alone does not suffice.
  N28-01   module docstring: "Proof owner: the derand fill proves both the host contract
           Complexity.exists_seedMajorityTM and Theorem 180.1"; the route heading and the contract's sketch name
           the derand fill too. (The derand brief/order/roots update is records work after the gate.)
  G28-01   records only: H17-row.md (draft row + companion sentence). /home/user/tcslib not edited.

checks
  headers  checks/headers.txt (tools/codecmp.py): SeedMajority's two round-1 headers (half_lt_randProb_iff,
           seedMajority_mem_DTIME) identical; one header added (exists_seedMajorityTM); imports: two added. Facade:
           code identical up to whitespace (comment-only change), imports identical; vs 013119f0 only the round-1
           import line.
  widths   checks/widths.txt: SeedMajority 237 lines, max 98; facade 211 lines, max 100. RESULT OK.
  lint     campaign_style_lint.py --check8b, base = round-1 head 8972fb4 (git archive export, removed afterwards),
           head = worktree: Cryptography 92 FAIL / 101 WARN both, Complexity 25 FAIL / 391 WARN both; FAIL/WARN line
           sets identical (lint/failwarn-*.diff empty); full diffs: only the two INFO size lines. Both also
           identical to the round-1 head logs of stmt-derand-evidence.zip. The new file has no FAIL or WARN.

olean tree $SP/dl-oleans only (dl-oleans-2 untouched)
  pre      tree/snapshot-pre.txt: 1230 files, 0 empty dirs, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f
           (base snapshot; also the post-restore state of job 1, stmt-b1-gate27). tree/snapshot-prebuild.txt same.
  order    order/changed.txt (git diff eff2dcd0..head, 53 modules) -> tools/downorder.py -> order/build-head.txt,
           63 modules imports-first (same set as round 1); order/backup.txt 20 base oleans copied aside,
           order/new.txt 43 head-only oleans.
  build    tools/runner.py via scripts/lean_check_tree.sh (byte-identical to /home/user/tcslib's),
           TCSLIB_OLEANS=$SP/dl-oleans, one Lean process at a time: build/results.jsonl, build/mods/*.log.
           63/63 rc 0; errors 0 (both forms); substring "error" 0 times. The only sorry warning:
           TCSlib/Complexity/Randomized/SeedMajority.lean:191:8 (exists_seedMajorityTM, intended).
           SeedMajority, facade TCSlib/Complexity/Randomized and root TCSlib rc 0, source SHA-256 = head blobs.
  probes   (tools/probe.sh, lean without -o, cwd = worktree, run while the build's oleans were in the tree;
           logs name the probe files by their scratch path $SP/r2work/dr/probes/)
           SealSeedMajority: whole-file seal (randProb, DTIME, P, PolyTimeComputable, pairEncode): rc 0, only the
             intended sorry warning (line 195 = 191 + 4 seal lines).
           SealSeedMajorityControl: + 2 controls (randProb by rfl; DTIME by anonymous constructor): rc 1, exactly
             2 errors, at the 2 controls (lines 246, 250). UnsealedSeedMajorityControl: rc 0.
             Axioms: exists_seedMajorityTM and seedMajority_mem_DTIME [propext, sorryAx, Classical.choice,
             Quot.sound]; half_lt_randProb_iff, mem_DTIME_of_decidesInTimeVia, DTIME.mono,
             DTIME_const_mul_subset [propext, Classical.choice, Quot.sound]. So the corollary's sorryAx comes
             from the contract only.
           StrictSealSeedMajority (informational): also seals FinTM.DecidesInTime and FinTM.DecidesInTimeVia:
             rc 1, 2 errors, both in seedMajority_mem_DTIME (lines 234-235); see G28-02 above.
           ConsumerProbe (sealed: DTIME, randProb, P, PolyTimeComputable, pairEncode, subexpBound): Thm 180.1's
             final transport from seedMajority_mem_DTIME, half_lt_randProb_iff, DTIME.mono and
             DTIME_const_mul_subset, for a general T and at T = subexpBound ε with L identified with the
             majority language: elaborates; its control (DTIME through its body) is the only error (line 56).
             ConsumerProbeUnsealed: rc 0.
  restore  restore/restore-log.txt: 20 backups copied back, 43 new oleans removed (incl. SeedMajority), 5 emptied
           directories removed. restore/snapshot-post.txt byte-identical to tree/snapshot-pre.txt, SHA-256
           457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f, 1230 files, 0 empty dirs. RESULT OK.

toolchain  Lean 4.25.0 (PATH=$HOME/.elan/bin:$PATH). No lake build, no lake exe cache get. Python: python3 -I.
SHA256SUMS: every file here except itself; ../stmt-derand-r2-evidence.zip holds this folder.

## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/pack.md =====

# Gate 28 · The seed-majority enumeration host for derandomization (derand host, statement)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #312](https://github.com/Shilun-Allan-Li/tcslib/pull/312) at
  `8972fb4ef15fa3d4e3df37d6aa8674408835593d` (branch `stmt/pass-shelat-derand-host`, tree
  `ba544f9ca0d80ff12644128a2cc32a94d6b5f709`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `013119f006af40d03b88b0fc2d9b453cf0a9b348` (the merge base; GitHub shows the branch tip at opening, `b12a12f2`, a
  records commit). The two commits from the base to the records tip `41e3cd2a6b637ed10c6782b5f3c68212f9f77b65`
  (`b12a12f2`, `41e3cd2a`) touch records only: `PassShelatChapter5-8Plan.md` and the two evidence folders
  `maintainer/stmt-b1-2026-11-15/` and `maintainer/stmt-derand-2026-11-15/`. The diff
  `origin/cryptography/pass-shelat-ch2-4...8972fb4e` equals `013119f0..8972fb4e` byte for byte (`pr.diff.txt`).
- **Commits:** 1, by the maintainer (author Claude): `8972fb4e` "Statement: the seed-majority enumeration host
  (derand, PS10 Thm 180.1)".
- **Scope:** a **statement audit** of a *host contract*. Seyoon ruled on 2026-11-14 that `derand`
  (`Randomness.bpp_subset_dtime_subexp`, [PS10, §8.2, Theorem 180.1]) is **held**: the deterministic counting/majority
  enumeration host it needs is first stated, sorried, by the maintainer in a statement PR with its own gate, and only
  then is `derand` dispatched. This PR is that statement. It adds no `def`.
- **Sources:** [PS10] §8.2, Theorem 180.1 (book p. 180), step 4 of its proof; [AB09] S. Arora and B. Barak,
  *Computational Complexity*, 2009, §7.1, p. 126 (`BPP ⊆ EXP` by enumerating the random strings) and Claim 2.4.

## What changed

The PR touches 2 Lean files (167 insertions, 0 deletions). Paths are under `TCSlib/Complexity/`.

| File | Status | Lines | SHA-256 at head |
|---|---|---:|---|
| `Randomized/SeedMajority.lean` | new | 163 | `3f6758b1…` |
| `Randomized.lean` (facade) | modified: one import and one `## Contents` entry (3 lines) | 206 → 210 | `bfefe641…` |

The new module imports `ClassP/P`, `ClassNP/PolyTime`, `TuringMachine/Encoding` and `Randomized/Classes`. It has two
public theorems and nothing else:

```lean
open Classical in
theorem Complexity.seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry   -- the contract; the only sorry

theorem Randomized.half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card   -- proved
```

`DTIME T = {L | ∃ c M, M.DecidesInTime L (fun n => c * T n)}` (`ClassP/DTIME.lean`), so the one membership carries
correctness (some machine decides exactly the strict-majority language; ties reject) and the time bound
`c · 2^{w(n)} · (n+1)^e`.

The maintainer's design choices, disclosed for this gate (PR description; `pr-body.md` § Design and § Decisions):
1. **Existential machine.** The contract is a class membership. No `def`, so no sorried definition and no reader owed;
   consumers read it through `DTIME.mono`, `Randomized.DTIME_const_mul_subset` and `half_lt_randProb_iff`.
2. **Generality.** The test is any `V ∈ P` read on `pairEncode x u` (the convention of `Randomized.polyTimeModel`), not
   a decider of arbitrary time on `x ++ u`; the width is any `w` whose unary word is polynomial-time; majority is
   strict, with no general threshold; only the `DTIME` form, with no machine-level `DecidesInTime` contract.
3. **No head-envelope (space) clause:** a decision-layer host, as `exists_proj_decider` is.
4. **Placement:** the shared `Complexity/Randomized` layer, not `derand`'s helper directory (policy §1, a second
   prospective consumer `BPP ⊆ EXP` [AB09, p. 126], and Complexity does not import Cryptography).
5. **Relatives not reused:** `Complexity.exists_proj_decider` (any-verdict, fixed width `C(n+1)^c`, test on `x ++ u`,
   private engine) and the polynomial block-majority tests.
6. **Registry row H17** for `machine-library-design.md` §14 is drafted in `pr-body.md` and not yet entered.

## Rulings and records in force

- **derand held; host contract first (Seyoon, 2026-11-14,** decision-log row "Rulings (Seyoon) on the staged
  fills"**):** the deterministic counting/majority enumeration host's contract is first stated (sorried) by the
  maintainer in a statement PR with its own gate; then `derand` is dispatched.
- **Derand fill pre-approvals (Seyoon, 2026-11-15,** row "derand host statement PR"**), for the later fill, not for
  this PR:**
  1. harvest one public generic-fuel `computesFunInTime_find` (with its contract) into the frozen
     `Complexity/Randomized/Build/IterateFind.lean`, reusing its private helpers in place;
  2. add `mem_DTIME_iff` (by `Iff.rfl`, with a formula docstring) beside `DTIME` in the frozen shared
     `ClassP/DTIME.lean`, its downstream rebuilt at review.

  The same row says the derand brief is updated after this gate: step 4 and checkpoint 1 consume the contract, and the
  order and roots are regenerated.
- **The derand brief** `fills/derand/issued-r1/brief.md` (in `verification.zip`, `records/`) is the consumer's issued
  brief. Its checkpoint 1 asked for a scope request for "a deterministic machine that runs a decider on `x ++ u` for
  every seed `u` of width `w` and accepts iff more than half accept, within `b · 2^w · (T(n + w) + poly)`". The stated
  contract specializes this to a `P` test on `pairEncode x u`; see question 3.
- **Policy §1, *Hosts come first*:** a host is never built `private` inside the proof that first needs it; its public
  contract is designed, statement-gated and placed in the shared construction layer first, generic in the parts its
  consumers vary, with time and space (head-envelope) clauses. The host registry is `machine-library-design.md` §14
  (rows H14 clean-module host, H16 counted word loop at the FP layer, in `verification.zip`).
- **Standing rules:** Rule 10; formula docstrings with `[PS10 …]`/`[AB09 …]` tags and a `**Proof sketch.**` (policy
  §§2–3); the #305 facade rule; lint baseline **92 FAIL / 101 WARN** on `TCSlib/Cryptography` with no new line (the
  PR also reports `TCSlib/Complexity`, 25 / 391); lines of at most 100 characters.

## What is frozen

Every file other than the new module and the facade's import and `## Contents` lines, in particular
`Cryptography/Randomness/Derandomization.lean` (`bpp_subset_dtime_subexp`, `subexpBound`), `ClassP/DTIME.lean`,
`Randomized/Classes.lean` (`randProb`, `randProb_eq`), `Randomized/QuasiPolyHierarchy.lean`
(`DTIME_const_mul_subset`), `Randomized/Build/IterateFind.lean` and `ClassNP/EXP.lean`: byte-identical to the base
(check with `pr.diff.txt`). The two derand pre-approvals above are not exercised here.

## Questions for the audit

1. **Is the contract true?** Including:
   - **ties:** `2^w = 2 · count` rejects; is that the intended strict majority, and is it what Theorem 180.1 needs (its
     `1/12` margin keeps acceptance probabilities away from `1/2`)?
   - **`w = 0`** (and `w x.length = 0` at some lengths): one seed, the empty word; the language is
     `{x | pairEncode x [] ∈ V}` at those lengths and the bound is `(n+1)^e`;
   - **small `n`:** `n = 0`, where the bound is `2^{w 0}`; and `DTIME_eq_empty_of_exists_zero` (the bound is never 0
     here);
   - **the time:** `2^{w(n)}` rounds, each a polynomial-time step on a state of length `O(n + w(n))`, with
     `w(n) ≤ C(n+1)^c` from `hw` (`PolyTimeComputable.output_length_le`); is `c · 2^{w(n)} · (n+1)^e` attainable on
     every input, including the cost of computing `1^{w(|x|)}` and of the final comparison?
   - the decision layer: `DecidesInTime` requires output exactly `[decide (x ∈ L)]` within `c · T(|x|)` steps on every
     `x : List Bool`.
2. **Is it sufficient for Theorem 180.1?** The PR description (`pr-body.md` § "Theorem 180.1 from the contract and the
   PRG hypothesis") gives a six-step paper proof; the module docstring's § Consumers gives the instantiation. Check:
   - the test `V'' = {⟨x, u⟩ | if |x| < n₀ then ⟨x, u⟩ ∈ V₁ else ⟨x, F'(u)↾m(|x|)⟩ ∈ V₁}` is in `P`
     (`preimage_mem_P`, Boolean closure, `PolyTimeComputable.pairEncode`, prefix truncation), with `V₁` the
     `some true`-set of the `polyTimeModel` verifier;
   - the width `w(n) = if n < n₀ then m(n) else ℓ(n)` (`ℓ(n)` the least `t` with `n ≤ t^d`) has a polynomial-time unary
     word; `n₀` is obtained non-constructively from PRG security, which is harmless for a fixed function `w` — is it?
   - `L` equals the majority language: below `n₀` with the true coins (acceptance `≥ 2/3` or `≤ 1/3`), from `n₀` on with
     gap at most `1/12` (`≥ 7/12` or `≤ 5/12`); `half_lt_randProb_iff` converts;
   - the bound `2^{w n}(n+1)^e ≤ c · subexpBound ε n` for all `n`, the finite exceptions absorbed into `c`
     (`subexpBound_pos`), then `DTIME.mono` and `DTIME_const_mul_subset`;
   - whether step 2 (bad input lengths to bad seed lengths, advice `|x| ≤ s^d`, `verifier_toNUPPT`,
     `NUPPT.exists_withAdvice(On)`, `randProb_eq_uprob`, `PRG.secure_iff`) is consistent with the frozen sketch of
     `bpp_subset_dtime_subexp`.

   `probes/ConsumerProbe.lean` checks only the last step (from a pointwise bound to `DTIME T`), sealed.
3. **Is the generality appropriate?**
   - A `P` test on `pairEncode x u`, versus the brief's decider of arbitrary time on `x ++ u`: is `P` enough for both
     consumers (derand's `V''` and `BPP ⊆ EXP` by coin enumeration with `w = polyLen a k`), and is `pairEncode` the
     right convention (it is `polyTimeModel`'s)?
   - Strict majority only, with no general threshold: does any foreseeable consumer need `t · 2^w < count`, or the
     count itself?
   - The `DTIME` form only, with no machine-level contract: does any consumer need to compose the host's machine (e.g.
     as a clean module inside a larger machine), which a `DTIME` membership cannot provide?
   - Is the width hypothesis `hw` the right one (input-length dependence only; the unary word rather than a binary
     one)?
4. **Is it placed in the shared layer, and is it Rule-10 clean?**
   - Policy §1 asks for the shared *construction* layer and for time and space (head-envelope) clauses. Is
     `Complexity/Randomized/` the right home (rather than `TuringMachine/Build/` or beside `ClassNP/EXP.lean`), and is
     the missing space clause acceptable for a decision-layer contract (precedent `exists_proj_decider`)?
   - Must the registry row H17 be entered in `machine-library-design.md` §14 before this PR merges, or with it?
   - Rule 10: `half_lt_randProb_iff` reads `randProb` only through `randProb_eq`; the statement uses `DTIME`, `P`,
     `PolyTimeComputable`, `pairEncode` and the `Finset` count as atoms. The evidence has a whole-file seal of the new
     module and a consumer probe, each with a paired control.
   - Nearest relatives: `exists_proj_decider` (`ClassNP/EXP.lean`), the block-majority tests
     (`ClassNP/PolyTimeBlockMajority.lean`), H16 `BinArith.forLoop` (`ClassP/BinaryArith/Loops.lean`, a counted loop
     with one round per counter letter) and `IterateFind.polyTimeComputable_find`. Is any of them, or a published
     generalization of one, the contract that should be stated instead?
5. **Is it provable on the stated route?** The module docstring's § Route: a state loop `⟨x, ⟨i, a⟩⟩`; the
   result-bearing combinator `Turing.FinTM.exists_loopFindTM` over the clean-module host with fuel
   `Nat.bits (2^{w(|x|)})`, bound `c (T(n) + 1)(R(n) + 2)`; the count through `i ↦ word_w(i)`; the normal form.
   - `evidence/probes/RouteAxioms.log`: 26 route lemmas, standard axioms only; the route avoids the admitted
     `loopHostTM_*` and `timedCondTM_*` specs.
   - Is the exponential fuel compatible with `exists_loopFindTM`'s contract (its fuel and time parameters, and the
     polynomial `T` of each round), and with the private `IterateFind` helpers (`Inv`, `verdictWord`, `stepWord`,
     `outWord`, `final_bound`), given the pre-approved harvest of a generic-fuel `computesFunInTime_find`?
   - Is introducing a `DTIME` membership possible without reading `DTIME`'s body, given the pre-approved
     `mem_DTIME_iff`?
   - The size estimate is 0.9–1.6k lines for the host; is it plausible?
6. **Docstrings and attribution.** Module docstring (formal reading, `## Main results`, consumers, design, route,
   `## References`) and the two theorem docstrings: formulas, `[PS10 …]`/`[AB09 …]` tags, the `**Deviation.**` and the
   contract's `**Proof sketch.**`.

## Known dispositions (not findings)

- **The facade edit** (one import, one `## Contents` entry) is the #305 facade rule, not a frozen-file change.
- **The host's proof is out of scope.** The gate asks whether the contract is true, sufficient, appropriately general,
  well placed and provable on the stated route.
- **Not exercised here:** the two derand pre-approvals (the `IterateFind` harvest and `mem_DTIME_iff`); the H17
  registry row (drafted only); the derand brief update.
- **Two PR texts.** The GitHub description of #312 is a shortened rewrite of the evidence's `pr-body.md` (in
  `verification.zip`, `records/…/stmt-derand-2026-11-15/pr-body.md`, byte-identical to the ZIP entry). The paper proof,
  the eight decisions for Seyoon and the draft H17 row are in full only in `pr-body.md`.
- **The evidence build** checked 63 modules in an olean tree whose base is source `eff2dcd0`: the new module, its
  facade, the 51 Cryptography modules changed between `eff2dcd0` and the PR base and their downstream, root `TCSlib`
  and `audits/pass-shelat/Checks`. `build/results.jsonl` has 64 lines: 63 module rows and a final `done` marker.

### Wording noted by the staging (please rate)

- The module docstring says "the proof is a separate fill"; the PR description says "The `derand` fill will then
  prove both the host and the theorem", and the 2026-11-15 pre-approvals are given to the derand fill. Which unit
  proves the contract is not stated the same way in the three places.

## Also check

- The `sorry` is the only one in the PR, at `SeedMajority.lean:154` (`seedMajority_mem_DTIME`); `half_lt_randProb_iff`
  uses the three standard axioms (`evidence/probes/ConsumerProbe.log`).
- Every line of the two files is at most 100 characters (`source-head.json`; `evidence/lint/widths.txt`).
- `open Classical in` on the contract: is the decidability instance of the `Finset.filter` the one a consumer obtains
  (the consumer probe rewrites with `half_lt_randProb_iff`, whose `[DecidablePred A]` is explicit)?
- Namespaces: the contract is in `Complexity`, the reader in `Randomized`, matching `DTIME` and `randProb`.

## Evidence

`verification.zip` (45 entries; its `SHA256SUMS` lists every other entry, `PROVENANCE.txt` maps each to its source)
holds byte-identical originals from records `41e3cd2a`:
- `stmt-derand-evidence.zip` (SHA-256 `aace4d2a…`, 107 file entries = the 106 manifest paths under `stmt-derand/` plus
  that folder's `SHA256SUMS`, byte-identical to the manifest) and its manifest `evidence-SHA256SUMS`;
- `records/`: the evidence's `PROVENANCE.txt` and `pr-body.md` (as beside the ZIP), the decision log, the duplication
  ledger, `machine-library-design.md` (§14, host registry) and the derand issue package `fills/derand/issued-r1/`;
- `evidence/`: byte copies of the ZIP entries cited here:
  - `build/order.txt`, `build/results.jsonl`, `build/mods/*.log` (4 of the 63): 63/63 rc 0, 0 errors (both
    `error:` and `error(` forms counted, G26-N1); the only `sorry` warning is `SeedMajority.lean:154:8`;
  - `probes/RouteAxioms.lean`/`.log` (route lemmas' axioms); `probes/SealSeedMajority.lean`/`.log` (whole-file seal:
    `randProb`, `DTIME`, `P`, `PolyTimeComputable`, `pairEncode` local irreducible; rc 0);
    `SealSeedMajorityControl` / `UnsealedSeedMajorityControl` (a control reading `randProb` through its body fails
    sealed exactly once, line 172, and passes unsealed); `ConsumerProbe` / `ConsumerProbeUnsealed` (the last step of
    derand through readers only, sealed; its control builds `DTIME` membership through the body and fails exactly
    once sealed; all pass unsealed);
  - `lint/linediff.txt` (Cryptography 92/101 and Complexity 25/391 at base and head, 0 new and 0 gone lines),
    `lint/widths.txt` (max widths 100 and 97);
  - `patches/COMMITS.tsv`, `patches/am-check.txt` (the tree reproduced from the patch; the commit is SSH-signed),
    `restore/restore-log.txt`, `tree/snapshot-pre.txt`, `restore/snapshot-post.txt` (the olean tree restored,
    SHA-256 `457ba704…` before and after), `PROVENANCE.txt`, `pr-body.md`.

Also: `pr.diff.txt` (2 paths, 167/0), `source-head.json` (hashes, line counts and over-width counts of the 2 files) and
`sources.zip` (the import closure at the head of both changed modules, 308 files). The consumer
`Cryptography/Randomness/Derandomization.lean` is not in that closure; it is in the bundle.

## Findings delivery

Return `gate28-derand-host-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable contract, or a scope violation (a frozen file changed).
- **major:** a missing or wrong hypothesis, a contract too weak for Theorem 180.1 or not provable on any reasonable
  route, a misplaced host under policy §1, a forbidden read, a duplicate public result, or necessary evidence that
  cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, route or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== TCSlib/Complexity/Randomized/SeedMajority.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.Randomized.Classes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic majority over all seeds (statement phase)

The counting enumeration host: a deterministic machine that, on input `x`, runs a
polynomial-time test on `⟨x, u⟩` for **every** seed `u ∈ {0,1}^{w(|x|)}`, counts the accepting
seeds, and accepts iff more than half of them accept, in time `2^{w(n)} · poly(n)`. It is the
enumeration behind `BPP ⊆ EXP` [AB09, §7.1, p. 126] (run the machine on every random string
and count the accepting ones) and step 4 of the proof of [PS10, §8.2, Theorem 180.1] (run the
derandomized verifier on every seed of the generator and take the majority). It is a *host* in
the sense of `policy.md` §1 (*Hosts come first*): an odometer over all seeds, generic in the
leaf test `V` and in the width `w`. Its contract is stated here, ahead of its consumers, by
Seyoon's rulings of 2026-11-14 (the host) and 2026-11-15 (the machine-level contract with a
head envelope, Gate 28, G28-02). **Proof owner:** the `derand` fill proves the host contract
`Complexity.exists_seedMajorityTM`, its corollary `Complexity.seedMajority_mem_DTIME`, and
Theorem 180.1 (`TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp`).

**The formal reading.**
- **The test** is a language `V ∈ P` read on `Turing.pairEncode x u`, the library's two-argument
  convention (`Randomized.polyTimeModel`'s verifiers are read the same way), so that the test may
  depend on the input `x` as well as on the seed `u`.
- **The width** `w : ℕ → ℕ` depends on the input length only, and its unary word
  `x ↦ 1^{w(|x|)}` is polynomial-time computable. This makes `w` computable by the machine and
  bounds it polynomially (`Complexity.PolyTimeComputable.output_length_le`); it is otherwise
  arbitrary, so a consumer may use a non-polynomial schedule such as an integer root, or a
  piecewise one.
- **The count** is `#{u : Fin (w |x|) → Bool | ⟨x, u⟩ ∈ V}`, the numerator of
  `Randomized.randProb` (`Randomized.half_lt_randProb_iff` converts), and **majority** is the
  strict `2^{w(|x|)} < 2 · count`, so ties reject.
- **The machine contract** (`Complexity.exists_seedMajorityTM`) ties correctness, time and a
  head envelope to the **same machine**: some finite machine `M` and constants `c, e`, with the
  budget `B(n) = c · (2^{w(n)} · (n+1)^e)`, satisfy
  - *correctness and time:* `M` decides the majority language within `B`
    (`Turing.FinTM.DecidesInTime`, the library's machine-level decision contract);
  - *head envelope:* at every time `v` of the run of `M` from its initial configuration on `x`,
    every work head is within `B |x|` cells of the origin. This is the coarse envelope derived
    from the time bound, in the form of the clean-module host's `Turing.ModuleHost.Clean.envelope`
    (`machine-library-design.md` §14, rows H14 and H16).
- **The class** `DTIME (n ↦ 2^{w(n)} · (n+1)^e)` is a corollary (`seedMajority_mem_DTIME`),
  which follows from the contract through the reader `Complexity.mem_DTIME_iff`. The `derand`
  fill adds that reader beside `DTIME` (`ClassP/DTIME.lean`) under its pre-approval (Seyoon,
  2026-11-15). Until then the corollary is admitted: without the reader its proof would read
  `Turing.FinTM.DecidesInTime`, `Turing.FinTM.DecidesInTimeVia` and `DTIME` by their
  definitions (Rule 10).

## Main results

* `Complexity.exists_seedMajorityTM` — the host's machine-level contract: correctness, time and
  head envelope of one machine (stated; a `sorry` under the route below, for the `derand` fill).
  [AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4 of the proof]
* `Complexity.seedMajority_mem_DTIME` — the decision-class corollary
  `∃ e, {x | 2^{w(|x|)} < 2 · count} ∈ DTIME (n ↦ 2^{w(n)} · (n+1)^e)` (stated; a `sorry`
  until the `derand` fill adds `mem_DTIME_iff`, then read off the contract).
* `Randomized.half_lt_randProb_iff` — majority as a probability:
  `1/2 < randProb m A ↔ 2^m < 2 · #{r | A r}` (proved).

## Consumers

* `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` ([PS10, Theorem 180.1]), through
  `seedMajority_mem_DTIME`, with the test **and** the width of the paper proof, both piecewise in
  a threshold length `n₀`. Let `V₁` be the accepting paired language of the `BPP` verifier `M`,
  `m(n)` its coin width, `F'` the evaluator of the expanded generator, and `ℓ(n)` the least `t`
  with `n ≤ t^d`. Below `n₀`, the test is `V₁` itself on the true coins,
  `⟨x, u⟩ ↦ M(x; u)`, with the width `w(n) = m(n)`. From `n₀` on, the test is
  `⟨x, u⟩ ↦ M(x; F'(u)↾m(|x|))` with the width `w(n) = ℓ(n)`. Changing the width alone would not
  remove the generator: `PRG` security says nothing about finitely many seed lengths, so the test
  changes with it.
* Prospectively, `BPP ⊆ EXP` by coin enumeration [AB09, p. 126] (`w = polyLen a k`), which
  `Randomized.mem_EXP_of_inBPP_polyTimeModel` currently obtains through Sipser–Gács.

## Design

* The nearest relative is the existential projection decider `Complexity.exists_proj_decider`
  (`ClassNP/EXP.lean`): the same odometer with an *any* verdict, a fixed width `C(n+1)^c` and
  the test on `x ++ u`. Its engine `enumMachine_contracts` and the `enumCont_*` body are
  private, it does not count, and its width is not a parameter, so it is not reused.
* The polynomial block-majority tests (`Complexity.polyTimeComputable_blockMajorityTest`) count
  over polynomially many blocks; this host counts over exponentially many seeds.
* The test is polynomial-time (`V ∈ P`), not a decider of arbitrary time `Tv` as in
  `exists_proj_decider`: both consumers have polynomial tests, and the clean-module host below
  installs polynomial-time word functions only (`Turing.ModuleHost.clean_install`).
* **Head envelope** (`policy.md` §1, *Hosts come first*; Seyoon's ruling of 2026-11-15, Gate 28,
  G28-02). The contract is machine-level, and its envelope is the coarse one from its own time
  bound `B`, on the same machine, as H14 states `Clean.envelope` and H16 composes with it. A
  sharper envelope does hold (every state word has length `O(n + w(n))`), but no consumer needs
  it and it is not stated. The admitted `loopHostTM_*` and `timedCondTM_*` space specifications
  are not used for it.

## Route for the proof (the `derand` fill)

1. *State loop.* The state word is `⟨x, ⟨i, a⟩⟩`: the binary rank `i` of the current seed and
   the binary acceptance count `a`, from `⟨x, ⟨0, 0⟩⟩`. A step tests `⟨x, word_w(i)⟩ ∈ V`,
   where `word_w(i)` is the width-`w(|x|)` binary word of `i`, adds the verdict to `a` and
   increments `i`. The loop stops when `i = 2^{w(|x|)}` and outputs `[decide (2^w < 2a)]`.
   Every piece is a polynomial-time word function of the state (`Complexity.BinArith`'s
   `add`, `lt` and `beq`, zero padding, the unary width, and `V`'s decider through
   `Complexity.mem_P_iff_polyTimeComputable`).
2. *Machine.* The result-bearing loop combinator `Turing.FinTM.exists_loopFindTM` over the
   clean-module host (`Turing.ModuleHost`, with `Complexity.IterateFind.hostTM`, `hostCtrl`,
   `hostRet`, `copyTM` and their run lemmas), exactly as in
   `Complexity.IterateFind.polyTimeComputable_find`, but with the exponential fuel
   `R(n) = 2^{w(n)}`, written as `Nat.bits (2^{w(|x|)})`
   (`w(|x|)` zeros, then a one) from the unary width. The combinator's bound is
   `c (T(n) + 1)(R(n) + 2)`, with `T` polynomial because every state word has length
   `O(n + w(n))` and `w(n) ≤ C(n+1)^c`. The admitted `loopHostTM_*` and `timedCondTM_*` specs
   are not used: `exists_loopFindTM` is proved from the private `loopHost_contracts`.
3. *Count.* The first stopping round is `2^{w(|x|)}`; there `a` counts the ranks `i < 2^w`
   whose word is accepted, which is the `Finset` count above through the bijection
   `i ↦ word_w(i)` between `[0, 2^w)` and `{0,1}^w`.
4. *Normal form.* `c (T(n) + 1)(2^{w(n)} + 2) ≤ b · (2^{w(n)} · (n+1)^e)`: the budget `B`.
5. *Envelope.* Every work head starts at the origin (`Turing.Cfg.init_workTapePos`) and moves by
   at most one cell per step (`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`); the run halts
   by time `B |x|` and is constant afterwards (`Turing.MultiTapeTM.runFrom_of_halt`). This is the
   argument of `Turing.ModuleHost.Clean.envelope`, applied to the machine of steps 2–4.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, §7.1, p. 126 (`BPP ⊆ EXP` by enumerating the random strings) and Claim 2.4 (the
  enumeration argument of `NP ⊆ EXP`).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
-/

namespace Randomized

open Finset

/-- **Majority as a probability.** For an event `A` on `m`-bit strings, the uniform probability
of `A` exceeds `1/2` exactly when more than half of the `2^m` strings satisfy it:
`1/2 < randProb m A ↔ 2^m < 2 · #{r : Fin m → Bool | A (List.ofFn r)}`. This converts the
counting form of `Complexity.seedMajority_mem_DTIME` into the probabilistic form of
[AB09, Def 7.3] and [PS10, Theorem 180.1]. -/
theorem half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card := by
  rw [randProb_eq, lt_div_iff₀ (by positivity), ← Nat.cast_lt (α := ℚ)]
  push_cast
  constructor <;> intro h <;> linarith

end Randomized

namespace Complexity

open Turing

open Classical in
/-- **Deterministic majority over all seeds: the machine contract** [AB09, §7.1, p. 126];
[PS10, §8.2, Theorem 180.1, step 4 of the proof]. For a test `V ∈ P` on paired words and a width
`w : ℕ → ℕ` whose unary word `x ↦ 1^{w(|x|)}` is polynomial-time computable, one finite machine
`M`, with constants `c, e` and the budget `B(n) = c · (2^{w(n)} · (n+1)^e)`,
- decides the strict-majority language
  `S = {x | 2^{w(|x|)} < 2 · #{u : Fin (w |x|) → Bool | pairEncode x (List.ofFn u) ∈ V}}`
  within `B` (`M.DecidesInTime S B`): on every input `x` it halts within `B |x|` steps with
  output `[true]` if `x ∈ S` and `[false]` otherwise; ties (`2 · count = 2^w`) reject; and
- keeps every work head within `B |x|` cells of the origin at every time `v` of its run on `x`:
  `|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ B |x|` (the head envelope, the coarse one
  from the time bound, as `Turing.ModuleHost.Clean.envelope`).

**Deviation.** The source's machine runs the test on every seed and counts; here the test is a
`P`-language on `Turing.pairEncode x u` and the count is a `Finset` count over
`Fin (w |x|) → Bool`, the numerator of `Randomized.randProb` (`Randomized.half_lt_randProb_iff`).
The head envelope is not in the source; it is the host clause of `policy.md` §1.

**Proof sketch** (the route of the module docstring; the `derand` fill).
1. Run the state loop `⟨x, ⟨i, a⟩⟩ ↦ ⟨x, ⟨i + 1, a + [⟨x, word_w(i)⟩ ∈ V]⟩⟩` from
   `⟨x, ⟨0, 0⟩⟩`, stopping at `i = 2^{w(|x|)}` with the payload `[2^w < 2a]`; each piece is a
   polynomial-time word function of the state.
2. Build the machine with the loop combinator `Turing.FinTM.exists_loopFindTM` over the
   clean-module host, as in `Complexity.IterateFind.polyTimeComputable_find`, with the fuel
   `Nat.bits (2^{w(|x|)})`; it halts within `c₀ (T(n) + 1)(2^{w(n)} + 2)` with `T` polynomial,
   since `w(n) ≤ C (n+1)^c` (`PolyTimeComputable.output_length_le`).
3. At the stopping round, `a` is the number of accepted ranks `i < 2^w`, which equals the
   `Finset` count through the bijection `i ↦ word_w(i)` onto `{0,1}^w`.
4. Bound `c₀ (T(n) + 1)(2^{w(n)} + 2)` by `c · (2^{w(n)} · (n+1)^e)`.
5. The envelope: the heads start at the origin (`Cfg.init_workTapePos`), move by at most one
   cell per step (`MultiTapeTM.workTapePos_runFrom_mem_Icc`), and the run is constant after its
   halt at a time `≤ B |x|` (`MultiTapeTM.runFrom_of_halt`). -/
theorem exists_seedMajorityTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
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

open Classical in
/-- **Deterministic majority over all seeds: the decision class** [AB09, §7.1, p. 126];
[PS10, §8.2, Theorem 180.1, step 4 of the proof]: for a test `V ∈ P` on paired words and a width
`w : ℕ → ℕ` whose unary word `x ↦ 1^{w(|x|)}` is polynomial-time computable, some degree `e`
puts the strict-majority language in `DTIME (n ↦ 2^{w(n)} · (n+1)^e)`:
`∃ e, {x | 2^{w(|x|)} < 2 · #{u : Fin (w |x|) → Bool | pairEncode x (List.ofFn u) ∈ V}}
∈ DTIME (fun n => 2^{w(n)} · (n+1)^e)`. Ties (`2 · count = 2^w`) reject. It is the corollary
of the machine contract `exists_seedMajorityTM` that the consumers of the class read.

**Status.** Admitted (a `sorry`). It follows from `exists_seedMajorityTM` through the reader
`Complexity.mem_DTIME_iff`, which the `derand` fill adds beside `DTIME` (`ClassP/DTIME.lean`)
under its pre-approval (Seyoon, 2026-11-15). The `derand` fill proves both the contract and
this corollary. Until the reader exists, a proof would read `Turing.FinTM.DecidesInTime`,
`Turing.FinTM.DecidesInTimeVia` and `DTIME` by their definitions, which Rule 10 forbids.

**Proof sketch.** Take the machine `M` and constants `c, e` of `exists_seedMajorityTM` (the
envelope is not needed here). `M` decides the language within
`n ↦ c · (2^{w(n)} · (n+1)^e)`, which is `c · T n` for `T n = 2^{w(n)} · (n+1)^e`. By
`mem_DTIME_iff` (membership in `DTIME T` is a constant `c` together with a machine deciding
within `c · T`), the language is in `DTIME T`, with the witness `e`. -/
theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry

end Complexity

## ===== TCSlib/Complexity/Randomized.lean =====

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SchwartzZippel
import TCSlib.Complexity.Randomized.ErrorReduction
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.Randomized.Adleman
import TCSlib.Complexity.Randomized.SipserGacs
import TCSlib.Complexity.Randomized.PolyTimeModel
import TCSlib.Complexity.Randomized.PTM
import TCSlib.Complexity.Randomized.Inclusions
import TCSlib.Complexity.Randomized.PTMEquiv
import TCSlib.Complexity.Randomized.Median
import TCSlib.Complexity.Randomized.PrimalityMath
import TCSlib.Complexity.Randomized.Primality
import TCSlib.Complexity.Randomized.AlgCircuit
import TCSlib.Complexity.Randomized.RandomBits
import TCSlib.Complexity.Randomized.Fingerprint
import TCSlib.Complexity.Randomized.ZeroPEval
import TCSlib.Complexity.Randomized.ZeroPRun
import TCSlib.Complexity.Randomized.ZeroP
import TCSlib.Complexity.Randomized.ZeroPPIT
import TCSlib.Complexity.Randomized.MatchingMath
import TCSlib.Complexity.Randomized.Matching
import TCSlib.Complexity.Randomized.ExpectedTime
import TCSlib.Complexity.Randomized.Coins
import TCSlib.Complexity.Randomized.ZPPEquiv
import TCSlib.Complexity.Randomized.ZPPHosts
import TCSlib.Complexity.Randomized.ZPPHostsClasses
import TCSlib.Complexity.Randomized.Reductions
import TCSlib.Complexity.Randomized.NPPoly
import TCSlib.Complexity.Randomized.Yap
import TCSlib.Complexity.Randomized.DirectedWalk
import TCSlib.Complexity.Randomized.BPPHard
import TCSlib.Complexity.Randomized.BPLInPCount
import TCSlib.Complexity.Randomized.BPLInPWords
import TCSlib.Complexity.Randomized.BPLInP
import TCSlib.Complexity.Randomized.RandomWalkCover
import TCSlib.Complexity.Randomized.RandomWalkMixing
import TCSlib.Complexity.Randomized.RandomWalkMixingPad
import TCSlib.Complexity.Randomized.UniformSample
import TCSlib.Complexity.Randomized.BiasedCoin
import TCSlib.Complexity.Randomized.BiasedCoinHalting
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyCode
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyMachine
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyRun
import TCSlib.Complexity.Randomized.SpaceAmplifyPoly
import TCSlib.Complexity.Randomized.ZeroPReduce
import TCSlib.Complexity.Randomized.BPPAmplify
import TCSlib.Complexity.Randomized.RPExpected
import TCSlib.Complexity.Randomized.BPOperator
import TCSlib.Complexity.Randomized.AlgCircuitExample
import TCSlib.Complexity.Randomized.QuasiPolyHierarchy
import TCSlib.Complexity.Randomized.BPPEqP
import TCSlib.Complexity.Randomized.BPTIMEThreshold
import TCSlib.Complexity.Randomized.Space
import TCSlib.Complexity.Randomized.SpaceAmplify
import TCSlib.Complexity.Randomized.SpaceAmplifyRun
import TCSlib.Complexity.Randomized.RandomWalk
import TCSlib.Complexity.Randomized.RandomWalkHitting
import TCSlib.Complexity.Randomized.RandomWalkPad
import TCSlib.Complexity.Randomized.UPath
import TCSlib.Complexity.Randomized.UPathMachine
import TCSlib.Complexity.Randomized.UPathLoops
import TCSlib.Complexity.Randomized.UPathParse
import TCSlib.Complexity.Randomized.UPathSearch
import TCSlib.Complexity.Randomized.UPathWalk
import TCSlib.Complexity.Randomized.UPathRL
import TCSlib.Complexity.Randomized.PolyExpr
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Complexity.Randomized.Primitives
import TCSlib.Complexity.Randomized.UnaryPolynomial
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Complexity.Randomized.SeedMajority

/-!
# Randomized Computation

Arora–Barak Chapter 7 (Randomized Computation): the model-free
probabilistic tools, and the chapter's complexity classes and theorems in
the certificate view of [AB09, Def 7.3], relative to an abstract efficiency
notion (`Randomized.VerifierModel`) standing in for polynomial-time Turing
machines.

## Contents

- `Randomized.SchwartzZippel`: the Schwartz–Zippel lemma in Arora–Barak's
  form ([AB09, Lem 7.5]), restated from Mathlib's
  `MvPolynomial.schwartz_zippel_totalDegree`.
- `Randomized.ErrorReduction`: concentration for i.i.d. Boolean trials (Hoeffding form of the
  Chernoff bound [AB09, Cor A.15]) and the majority-vote error bound that is the calculation
  inside the error-reduction theorem ([AB09, Thm 7.10]).
- `Randomized.Classes`: verifier-style `BPP`/`RP`/`coRP`/`ZPP`
  ([AB09, Defs 7.2/7.3/7.6/7.7]), `ZPP = RP ∩ coRP` ([AB09, Thm 7.8]), and
  error reduction at the class level ([AB09, Lem 7.9, Thm 7.10]).
- `Randomized.Adleman`: `BPP ⊆ P/poly` ([AB09, Thm 7.14]), concluding in
  `Language.InPPoly` from `CircuitComplexity.PPoly`.
- `Randomized.SipserGacs`: certificate-style `Σ₂ᵖ`/`Π₂ᵖ` and
  `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` ([AB09, Thm 7.15]).
- `Randomized.PolyTimeModel`: the instantiation of the abstract verifier
  model by genuine polynomial-time machines (`Complexity.P`), discharging
  the closure hypotheses and connecting `Σ₂` to `Complexity.SigmaP 2`.
- `Randomized.PTM`: probabilistic Turing machines as binary-choice machines read
  probabilistically; `BPTIME`, `BPP_PTM`, `RTIME`, `RP_PTM`, `coRP_PTM`
  ([AB09, Def 7.1, Def 7.2, Def 7.6]).
- `Randomized.Inclusions`: `P ⊆ BPP`, `RP ⊆ NP`, `RP, coRP ⊆ BPP`, `BPP ⊆ EXP`,
  `NP = P ⇒ BPP = P`, `3SAT ∈ BPP ⇒ PH = Σ₂ᵖ` ([AB09, §7.1, §7.3, §7.5.1]) and RP error
  reduction ([AB09, Exercise 7.4]).
- `Randomized.PTMEquiv`: the PTM classes equal the certificate classes over polynomial-time
  verifiers ([AB09, Def 7.2 ≡ Def 7.3]).
- `Randomized.Median`: `FindKthElement` and its expected number of comparisons
  ([AB09, §7.2.1, Claim 7.4]).
- `Randomized.PrimalityMath`, `Randomized.Primality`: Solovay–Strassen; `PRIMES ∈ coRP`
  ([AB09, §7.2.2]).
- `Randomized.AlgCircuit`: algebraic circuits, their polynomials and degree, `ZEROP`
  ([AB09, §7.2.3]).
- `Randomized.RandomBits`: shared counting lemmas over random strings (conditioning on a
  prefix, the union bound) and numbers read off blocks of fair coins.
- `Randomized.Fingerprint`: the fingerprinting test for `ZEROP` and its error analysis
  ([AB09, §7.2.3]).
- `Randomized.ZeroPEval`, `Randomized.ZeroPRun`: the polynomial-time evaluator of encoded
  algebraic circuits modulo `k`.
- `Randomized.ZeroP`, `Randomized.ZeroPPIT`: `ZEROP ∈ coRP` and polynomial identity testing
  in `coRP` ([AB09, §7.2.3]).
- `Randomized.MatchingMath`, `Randomized.Matching`: Edmonds matrix, Lovász's test, bipartite
  perfect matching in `RP` ([AB09, §7.2.4]).
- `Randomized.ExpectedTime`: expected running time, `ZTIME`, `ZPP_PTM`
  ([AB09, §7.3, Def 7.7]) and Markov truncation ([AB09, §7.4.2]).
- `Randomized.Coins`: biased coins from fair coins and von Neumann's extractor
  ([AB09, Lemma 7.12, Lemma 7.13]).
- `Randomized.ZPPEquiv`, `Randomized.ZPPHosts`, `Randomized.ZPPHostsClasses`: `ZPP` in its
  expected-time, abort and certificate forms, and `ZPP = RP ∩ coRP` for Def 7.7
  ([AB09, Theorem 7.8, Exercise 7.6]).
- `Randomized.Reductions`: randomized reductions and `BP·NP` ([AB09, Def 7.16, Def 7.17]).
- `Randomized.NPPoly`: `NP/poly` and `BP·NP ⊆ NP/poly` ([AB09, Exercise 7.7]).
- `Randomized.Yap`: Yap's theorem (`coNP ⊆ NP/poly ⇒ PH = Σ₃ᵖ`) and [AB09, Exercise 7.8].
- `Randomized.DirectedWalk`: the random walk on a directed graph can need Ω(2ⁿ) steps
  [AB09, Exercise 7.10].
- `Randomized.BPPHard`: `⟨M, x, 1ᵗ⟩` with acceptance probability ≥ 2/3 is BPP-hard
  [AB09, §7.5.3, p. 138].
- `Randomized.BPLInPCount`, `Randomized.BPLInPWords`, `Randomized.BPLInP`: `BPL ⊆ P` by an exact
  dynamic program over configurations [AB09, Exercise 7.9].
- `Randomized.RandomWalkCover`: connectivity, bipartiteness and the bipartite double cover for
  regular multigraphs; even-length walks of length `2n` between any two vertices.
- `Randomized.RandomWalkMixing`, `Randomized.RandomWalkMixingPad`: contraction to uniform,
  uniqueness of the stationary distribution, visit frequency, and the self-loop regularization
  transfer [AB09, Exercise 7.11(b), (e)].
- `Randomized.UniformSample`: uniform sampling from `[N]` with coin tosses [AB09, Exercise 7.1].
- `Randomized.BiasedCoin`, `Randomized.BiasedCoinHalting`: ρ-coin PTMs; an uncomputable ρ decides an
  undecidable language in polynomial time [AB09, Exercise 7.5].
- `Randomized.SpaceAmplifyPolyCode`, `…Machine`, `…Run`, `Randomized.SpaceAmplifyPoly`: BPL and RL
  error reduction to `2^{-n^d}` in logarithmic space [AB09, §7.7, p. 139].
- `Randomized.ZeroPReduce`: the polynomial-time reduction PIT ≤ₚ ZEROP and closure of RP/coRP under
  ≤ₚ [AB09, §7.2.3].
- `Randomized.BPPAmplify`: Lemma 7.9 and Theorem 7.10 for polynomial-time PTMs and the
  polynomial-time verifier model; any constant above `1/2` gives BPP [AB09, §7.4.1].
- `Randomized.RPExpected`: expected polynomial time gives the same RP and coRP [AB09, §7.4.2].
- `Randomized.BPOperator`: the `BP·` operator; `BP·P = BPP` and `BP·NP` agrees with Def 7.17
  [AB09, Chapter notes].
- `Randomized.AlgCircuitExample`: `∏(1 + xᵢ)` has a circuit with `2n` operations but `2ⁿ` monomials
  [AB09, §7.2.3, p. 129].
- `Randomized.QuasiPolyHierarchy`: `P ⊊ DTIME(n^{log n})` via a time-constructible quasi-polynomial
  budget.
- `Randomized.BPPEqP`: if `BPP = P` then `BPP ⊊ DTIME(n^{log n})` and BPP has a complete problem
  [AB09, §7.5, §7.5.3].
- `Randomized.BPTIMEThreshold`: any constant threshold in `(1/2, 1)` gives the same
  `BPTIME(T(n))` [AB09, §7.1, p. 125].
- `Randomized.Space`, `Randomized.SpaceAmplify`, `Randomized.SpaceAmplifyRun`: randomized
  space, `BPL`, `RL`, `RL ⊆ NL ⊆ P`, error reduction in log space ([AB09, §7.7, Def 7.18]).
- `Randomized.RandomWalk`, `Randomized.RandomWalkHitting`, `Randomized.RandomWalkPad`:
  random walks on regular multigraphs and their hitting times ([AB09, Exercise 7.11]).
- `Randomized.UPath`, `Randomized.UPathMachine`, `Randomized.UPathLoops`,
  `Randomized.UPathParse`, `Randomized.UPathSearch`, `Randomized.UPathWalk`,
  `Randomized.UPathRL`: `UPATH ∈ RL` ([AB09, Theorem 7.19]).

The Pass–shelat ch. 2–4 layer (`PassShelatChapter2-4Plan.md`; namespace `Complexity`):
probabilistic polynomial-time machines with explicit coin and advice polynomials, their
closure calculus, and the repetition lemma.

- `Randomized.PolyExpr`: syntactic polynomials `Complexity.PolyExpr` for every length and
  budget (evaluation, substitution, monotonicity, the normal-form majorant).
- `Randomized.PPT`: the structure `Complexity.NUPPT` (PPT [PS10, Definition 23.4] with
  worst-case time [PS10, Definition 23.5], computing with probability one [PS10, Definition
  24.6], non-uniform PPT in the advice form [PS10, Definition 26.8]) and the subtype
  `Complexity.PPT`.
- `Randomized.NonUniform`: the two formulations of Definition 26.8, uniformity lemmas, and
  the bridge from `Turing.FinTM.DecidesWithAdviceInTime`.
- `Randomized.Primitives`: coin splitting, unary multiplication, the unary evaluator and the
  typed coin cuts.
- `Randomized.UnaryPolynomial` — unary polynomial evaluation in time proportional
  to the input and output lengths.
- `Randomized.Closure`: the closure calculus of non-uniform PPTs.
- `Randomized.Repetition`: the repetition lemma `polyTimeComputable_iterateFind` and its
  iteration variants.
- `Randomized.SeedMajority`: the counting enumeration host, deterministic majority over all
  seeds of a polynomial-time test: one machine with its correctness, its time `2^{w(n)} · poly`
  and a head envelope, and the `DTIME` corollary ([AB09, §7.1, p. 126];
  [PS10, Theorem 180.1]; statement phase).

All entries, and the files they describe, cite the printed book's (2009) numbering.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity

## ===== TCSlib/Complexity/ClassP/ModelInvariance.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# "And why it doesn't matter": model invariance of DTIME and P

The payoff of the robustness theorems ([AB09, §1.3.1], formalized in
`TCSlib.Complexity.TuringMachine.Robustness`), stated at the strength the theorems
actually deliver (phase-2 audit, finding 4): **alphabet size** never matters —
`DTIME` is alphabet-invariant, the alphabet-dependent constant being absorbed by
`DTIME`'s own existential — while **the number of work tapes** does not matter *for
`P`*, where the quadratic overhead of tape reduction is harmless. No invariance of a
fixed class `DTIME T` under tape reduction is claimed, and [AB09, §1.6.1] likewise
draws only the polynomial-time conclusion. This is the formal content of the
chapter's title at class level.

## Main definitions

* `Turing.FinTM.DecidesInTimeVia` — a machine over a larger alphabet decides a binary
  language via a symbol embedding.

## Main results

* `Complexity.mem_DTIME_of_decidesInTimeVia` — deciding over any finite alphabet lands
  in binary `DTIME` (constant absorbed). [AB09, Claim 1.5 for languages]
* `Complexity.mem_P_of_decidesInTimeVia_poly` — `P` is alphabet-invariant.
* `Complexity.mem_P_iff_one_work_tape` — `P` is exactly what one-work-tape binary
  machines decide in polynomial time. [AB09, Claims 1.5-1.6 for `P`]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3.1; §1.6.1 "Why the model may not matter".)
-/

namespace Turing.FinTM

/-- The machine `M`, over alphabet `Γ`, decides the binary language `L` via the symbol
embedding `e : Bool ↪ Γ` within time `T`: on every input `x.map e` it halts within
`T |x|` steps with output `[e b]` where `b` is the membership bit of `x` in `L`. -/
def DecidesInTimeVia {Γ : Type} (M : FinTM Γ) (e : Bool ↪ Γ) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime (x.map e)
      [e (MultiTapeTM.indicator (L : Set (List Bool)) x)] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- Deciding a language over *any* finite alphabet puts it in the binary-machine class
`DTIME` (with the alphabet-dependent constant absorbed by `DTIME`'s existential).

**Proof sketch.** `DecidesInTimeVia` is `ComputesFunInTimeVia` for the function
`x ↦ [indicator L x]` (note `[b].map e = [e b]`); apply
`Turing.FinTM.alphabet_reduction` and absorb its constant `c` into `DTIME`'s. -/
theorem mem_DTIME_of_decidesInTimeVia {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} {T : ℕ → ℕ}
    (h : M.DecidesInTimeVia e L T) :
    L ∈ DTIME fun n => T n + 1 := by
  obtain ⟨c, M', -, hM'⟩ := FinTM.alphabet_reduction e M
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) T
    (fun x => by simpa using h x)
  exact ⟨c, M', fun x => hM' x⟩

/-- **`P` is alphabet-invariant**: a language decided in polynomial time by a machine
over any finite alphabet is in `P`.

**Proof sketch.** `Complexity.mem_DTIME_of_decidesInTimeVia` gives
`L ∈ DTIME (C · (n + 1) ^ d + 1)`; conclude with `Complexity.mem_P_of_dtime_le`
(pointwise bound `C · (n + 1) ^ d + 1 ≤ (C + 1) · 2 ^ d · (n ^ d + 1)`, using
`(n + 1) ^ d ≤ 2 ^ d (n ^ d + 1)` from the `mem_P_iff` arithmetic). -/
theorem mem_P_of_decidesInTimeVia_poly {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} (C d : ℕ)
    (h : M.DecidesInTimeVia e L fun n => C * (n + 1) ^ d) :
    L ∈ P := by
  have h1 := mem_DTIME_of_decidesInTimeVia e h
  refine mem_P_of_dtime_le h1 ((C + 1) * 2 ^ d) d fun n => ?_
  have h2 : 0 < (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos _)
  calc C * (n + 1) ^ d + 1
      ≤ C * (n + 1) ^ d + (n + 1) ^ d := Nat.add_le_add_left h2 _
    _ = (C + 1) * (n + 1) ^ d := by ring
    _ ≤ (C + 1) * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul (le_refl _) (succ_pow_le n d)
    _ = (C + 1) * 2 ^ d * (n ^ d + 1) := by ring

/-- **`P` is tape-count-invariant**: `P` is exactly the class of languages decided by
binary machines with a *single* work tape in polynomial time. [AB09, Claim 1.6 at the
level of `P`; quadratic slowdown preserves polynomiality]

**Proof sketch.** Backward: a one-work-tape polynomial decider is in particular a
polynomial decider (`Complexity.mem_P_iff`). Forward: from `mem_P_iff` take a decider
within `C · (n + 1) ^ d`; `DecidesInTime` is `ComputesFunInTime` for
`x ↦ [indicator L x]`, so `Turing.FinTM.one_work_tape_binary` yields a one-work-tape
binary machine within `c · (C · (n + 1) ^ d + 1)² ≤ C' · (n + 1) ^ (2d)`, again of the
`mem_P_iff` shape. -/
theorem mem_P_iff_one_work_tape {L : Language Bool} :
    L ∈ P ↔ ∃ (M : FinTM Bool) (C d : ℕ),
      M.k = 1 ∧ M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp hL
    obtain ⟨M', c, hk, hM'⟩ := FinTM.one_work_tape_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
      (fun n => C * (n + 1) ^ d) hM
    refine ⟨M', c * (C + 1) ^ 2, d * 2, hk, fun x => (hM' x).mono ?_⟩
    have h2 : 0 < (x.length + 1) ^ d := Nat.pow_pos (Nat.succ_pos _)
    calc c * (C * (x.length + 1) ^ d + 1) ^ 2
        ≤ c * ((C + 1) * (x.length + 1) ^ d) ^ 2 := by
          refine Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left ?_ 2)
          calc C * (x.length + 1) ^ d + 1
              ≤ C * (x.length + 1) ^ d + (x.length + 1) ^ d :=
                Nat.add_le_add_left h2 _
            _ = (C + 1) * (x.length + 1) ^ d := by ring
      _ = c * (C + 1) ^ 2 * ((x.length + 1) ^ d) ^ 2 := by ring
      _ = c * (C + 1) ^ 2 * (x.length + 1) ^ (d * 2) := by rw [pow_mul]
  · rintro ⟨M, C, d, -, hM⟩
    exact mem_P_iff.mpr ⟨C, d, M, hM⟩

end Complexity

## ===== TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan, TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan, TCSlib contributors
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clean-module host

A host (`machine-library-design.md` §14, row H14) that runs a finite family of *clean modules*
inside one finite machine.

* **Clean modules.** A clean module (`Turing.ModuleHost.Clean`) is a finite machine with at least
  one work tape that, started at the canonical seam with an argument word as its only
  tape-resident word, halts for the first time at a positive time within a budget of the argument
  length, at the seam holding a result word, having emitted exactly a declared chunk. Every
  polynomial-time word function has a clean **install** module (the value installed as the
  tape-resident word, nothing emitted) and a clean **emit** module (the argument kept, the value
  emitted), each with a polynomial budget (`clean_install`, `clean_emit`). They come from the
  clean-call bridges `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM`, whose modules exit
  at their first positive visit of an exit state: a release flag halts such a module one silent
  step after that visit, and cutting the run at its first halt (`first_halt`) gives the uniform
  contract.
* **The host.** `Turing.ModuleHost.hostTM` pads `n` modules to a shared bank of `K` work tapes
  (all modules share tape 0) and embeds them, through the forwarding transformer
  `Turing.emitAction`, into one finite machine whose states are the host's own control states `C`
  and the modules' states (`Turing.ModuleHost.State C M = C ⊕ Σ i, (M i).State`). When module `i`
  halts, control passes to its return state `ret i`; the control states run a table `ctrl`
  supplied by the consumer (`hostTM_step_inl`). `host_call` and `host_clean` run one module inside
  the host: from the host seam at the module's entry state, with any output prefix, the host
  reaches the seam at the module's return state with the module's result word, forwarding exactly
  the module's output, and visits no control state meanwhile; `guard_add` chains such segments.
* **Head envelopes.** A clean module's heads stay within its budget `B |arg|` of the origin at
  every time (`Clean.envelope`), and the host's heads stay within `t` cells of the origin up to
  time `t` of a call (`host_call_envelope`), hence within `B |arg|` during a clean call
  (`host_clean_envelope`). These are the coarse envelopes from the time bounds and the unit head
  moves of `Turing.MultiTapeTM.workTapePos_step_le` (gate 03l round 2, finding 1).

## Origin

Harvested on 2026-11-05 (gate 03l, ruling R-03l-1) from two copies of one private layer: the
module-gluing layer of `TCSlib.Complexity.ClassNP.SAT` on `main` (the streaming emitter behind
`Complexity.SAT_reducible_SAT3` [AB09, Lemma 2.14]: six modules, one control state), and its copy
in pack 03l's `TCSlib.Complexity.Randomized.Build.IterateFindHost` (the repetition machine behind
`Complexity.polyTimeComputable_iterateFind`: five modules, three control states). Both now
instantiate this file; what they vary is a parameter here: the number of modules and their
machines, the control states and their table, the return map and the start state.

## Main definitions

* `Turing.ModuleHost.Clean` — the first-halting clean-module contract (read through `clean_iff`).
* `Turing.ModuleHost.State`, `Turing.ModuleHost.entry` — the host's state type and the entry
  state of a module (`state_eq`, `entry_eq`).
* `Turing.ModuleHost.hostTM` — the host (`hostTM_k`, `hostTM_tm_q₀`, `hostTM_step_inl`).

## Main results

* `Turing.ModuleHost.clean_install`, `clean_emit` — every polynomial-time word function has a
  clean install and a clean emit module with a polynomial budget on the argument length.
* `Turing.ModuleHost.host_call`, `host_clean` — one module call inside the host, with the guard
  that no control state is visited; `guard_add` — chaining guarded segments.
* `Turing.ModuleHost.Clean.envelope`, `host_call_envelope`, `host_clean_envelope` — the head
  envelopes of a clean module and of a host call.
* `Turing.ModuleHost.first_halt`, `live_prefix` — cutting a halting run at its first halt, and
  liveness of the prefix of a live run.
* `Turing.ModuleHost.request_budget` — a polynomial budget on a bounded request fits a common
  power.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded multi-tape machines; §2.2, the class
  FP; Lemma 2.14, the reduction of the first consumer.)
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1: the repeated-adversary machine of the second consumer.)
-/

namespace Turing.ModuleHost

open Complexity

/-! ### Runs: the first halt and the live prefix -/

/-- **The first halt.** If the run of `tm` from a live configuration `cfg` has halted by time
`t`, then it halts for the first time at some time `u` with `0 < u ≤ t`: the configurations
before `u` are live, and the configuration at `u` is the one at `t`.

**Proof sketch.** Take the least halting time `u` (`Nat.find`). It is positive because `cfg` is
live, and since halting is absorbing (`runFrom_of_halt`), the configuration at `t = u + (t - u)`
is the one at `u`. -/
theorem first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, fun v hv => Nat.find_min h hv, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hu]

/-- **The live prefix.** If the run of `tm` from `c` is live at time `t`, it is live at every
time `u ≤ t` (halting is absorbing, `runFrom_of_halt`). -/
theorem live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-! ### Clean modules -/

/-- Convert a first-positive-exit module into a halting source: a release flag, raised after
the first step, makes the module halt silently when it is at `exit` — so an entry equal to the
exit still executes once. -/
private def stopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with
              state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- The release-flag embedding of a module configuration: the flag `b` joins the state, and
every physical field is kept. -/
private def stopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same physical step as the
module and raises the release flag. -/
private lemma stop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (stopTM C entry exit).tm.step (stopCfg b c) = stopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    have hs' : (stopCfg b c).state = some (b, q) := by simp [stopCfg, hs]
    rw [MultiTapeTM.step_of_some hs', MultiTapeTM.step_of_some hs]
    simp only [stopTM, hq, ↓reduceIte]
    rfl

/-- Stop a clean call one silent step after its certified first positive exit.

**Proof sketch.** Induct on prefixes, keeping the release flag false only at time zero; the
guard prevents an early stop; the final silent halt keeps every seam field and every emitted
bit. -/
private lemma stop_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (stopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
      {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hl := live_prefix C.tm c t
    (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords_def])
  have hp : ∀ v, v ≤ t → (stopTM C entry exit).tm.runFrom (stopCfg false c) v =
      stopCfg (decide (v ≠ 0)) (C.tm.runFrom c v) := by
    intro v
    induction v with
    | zero => intro _; rfl
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        stop_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      rfl
  have hi : Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg) = stopCfg false c := rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _)]
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hflag, show C.tm.runFrom c t = _ from he]
  rw [MultiTapeTM.step_of_some (q := (true, exit)) (by simp [stopCfg, Cfg.ofWords_def])]
  simp [stopTM, stopCfg, Cfg.ofWords_def, FinTM.controlAction_def, Action.apply_state,
    Action.apply_output, Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos]

/-- **The clean-module contract.** `Clean M result emit B` says: the module `M` has at least one
work tape (`0 < M.k`), and for every native input `x` and argument `arg`, the run of `M` from the
seam at its start state with `arg` as the only tape-resident word halts for the first time at
some time `t` with `0 < t ≤ B |arg|` (every configuration before `t` is live), and the
configuration at `t` is the seam holding the result word `result arg`, with output exactly
`emit arg`. -/
def Clean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- `Clean M result emit B` holds iff `0 < M.k` and, for every native input `x` and argument
`arg`, some time `t` with `0 < t ≤ B |arg|` is the first halt of `M` from the seam
`Cfg.ofWords M.tm.q₀ (stateWord M.k arg)`, at the seam holding `result arg` with output
`emit arg`. -/
theorem clean_iff (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) :
    Clean M result emit B ↔ 0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t,
        ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
        {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with
          state := none, output := emit arg} :=
  Iff.rfl

/-- **The head envelope of a clean module** (H14's space clause): if `Clean M result emit B`,
then for every native input `x` and argument `arg`, at every time `v` of the run of `M` from the
seam at its start state holding `arg` (before, at and after its first halt), every work head is
within `B |arg|` cells of the origin, where all heads start (`Cfg.ofWords_workTapePos`).

This is the coarse envelope from the time bound: one step moves each head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`), the first halt comes at a time `t ≤ B |arg|`,
and the run is constant from `t` on. The theorem intentionally publishes this coarse
time-derived bound. A sharper one does hold: every head starts at the origin and the terminal
seam (`Cfg.ofWords`) puts it back there, so a head that reaches distance `d` spends at least
`2d ≤ t` steps going out and back, and `|position| ≤ B |arg| / 2`; that factor-two bound is not
stated here (gate 03l round 2, finding 1).

**Proof sketch.** Take the first halt `t ≤ B |arg|` of `Clean`. At a time `v ≤ t` each head is
within `v` cells of its start (`MultiTapeTM.workTapePos_runFrom_mem_Icc`); at `v > t` the run
is halted, so its configuration is the one at `t` (`MultiTapeTM.runFrom_add`,
`MultiTapeTM.runFrom_of_halt`). -/
theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ}
    (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
    |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
      (B arg.length : ℤ) := by
  obtain ⟨t, -, htB, -, hend⟩ := ((clean_iff M result emit B).1 h).2 x arg
  have hhalt : (M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t).state =
      none := by
    rw [hend]
  obtain ⟨u, hut, hu⟩ : ∃ u ≤ t,
      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v =
        M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u := by
    rcases le_total v t with hvt | htv
    · exact ⟨v, hvt, rfl⟩
    · refine ⟨t, le_rfl, ?_⟩
      rw [← Nat.add_sub_of_le htv, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (M.tm.workTapePos_runFrom_mem_Icc
    (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u j)
  rw [Cfg.ofWords_workTapePos] at h1 h2
  have hB : (u : ℤ) ≤ B arg.length := by exact_mod_cast hut.trans htB
  rw [hu, abs_le]
  constructor <;> omega

/-- Turn a clean-call bridge contract into the uniform first-halting form.

**Proof sketch.** The release wrapper stops one step after the positive exit (`stop_clean`);
cutting the run at its first halt (`first_halt`) keeps the whole clean configuration. -/
private lemma clean_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    Clean (stopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := stop_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := first_halt (stopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords_def]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [stopTM, Cfg.ofWords_def] using hend.trans hs

/-- The bridge overhead `c (A (n+1)^d + n + len + 1) + 1`, with the output length
`len ≤ A (n+1)^d`, fits the single monomial `(c (2A + 1) + 1)(n+1)^{d+1}`.

**Proof sketch.** `n + 1` and both source-time terms are at most multiples of `(n+1)^{d+1}`; the
last unit, which pays for the stop, is at most `(n+1)^{d+1}`. -/
private lemma bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- **Clean install modules.** Every polynomial-time word function `f` has a clean module that
installs `f arg` as the tape-resident word and emits nothing, with a budget `A (|arg| + 1)^d`.

**Proof sketch.** `Turing.FinTM.exists_installCallTM` gives a module that exits at its first
positive visit of an exit state, within `c (T + |arg| + |f arg| + 1)` steps for the source time
`T = A (|arg|+1)^d`; the output length is at most the source time
(`Turing.MultiTapeTM.output_length_le`). The release wrapper and the first-halt cut
(`clean_stop`) give the uniform contract one step later, and `bridge_bound` puts the budget in
the form `A' (|arg| + 1)^{d+1}`. -/
theorem clean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  -- The bridge's result length depends on the word, so enlarge it pointwise to the source
  -- time before putting it in the uniform argument-length budget.
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit f (fun _ => [])
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      refine ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, ?_⟩
      exact he)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- **Clean emit modules.** Every polynomial-time word function `f` has a clean module that
keeps its argument as the tape-resident word and emits exactly `f arg`, with a budget
`A (|arg| + 1)^d`.

**Proof sketch.** As `clean_install`, from `Turing.FinTM.exists_emitCallTM`. -/
theorem clean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit id f
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- **A common budget.** A polynomial budget `A (m + 1)^d` on a request of length `m` with
`m + 1 ≤ N` is at most `A N^D` for every `D ≥ d` (monotonicity of powers, `0 < N`). -/
theorem request_budget (A d D N m : ℕ) (hd : d ≤ D) (hm : m + 1 ≤ N) :
    A * (m + 1) ^ d ≤ A * N ^ D := by
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hm d).trans (Nat.pow_le_pow_right (by omega) hd)

/-! ### Padding a module into the shared tape bank -/

/-- Pad an action to a larger tape count, keeping the extra tapes stationary. -/
private def padAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
  ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
    a.output, a.state⟩

/-- A module padded into a shared bank of `K` tapes; all modules share tape zero. -/
private def padTM (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K) : FinTM Bool where
  k := K
  State := M.State
  tm := { q₀ := M.tm.q₀
          tr := fun q inp work => padAction (M.tm.tr q inp
            (fun i => work ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)) }

/-- The configuration embedding for the shared bank: the padding tapes are blank, with their
heads at the origin. -/
private def padCfg {k K : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos,
    fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- Padding commutes with applying an action (the inactive tapes neither write nor move). -/
private lemma pad_apply {k K : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (padAction (K := K) a).apply (padCfg c) = padCfg (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply_state, Action.apply_output,
        Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos, h]
  · funext i
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply_state, Action.apply_output,
        Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos, h]

/-- The padded module runs in lockstep with the module. -/
private lemma pad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (padTM M K hk).tm.runFrom (padCfg c) t = padCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none =>
    have hs' : (padCfg (K := K) c).state = none := hs
    rw [MultiTapeTM.step_of_halt hs', MultiTapeTM.step_of_halt hs]
  | some q =>
    have hw : (fun i : Fin M.k => (padCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [padCfg, Cfg.workTapeSymbols_eq, i.isLt]
    have hstate : (padCfg (K := K) c).state = some q := hs
    rw [MultiTapeTM.step_of_some hstate, MultiTapeTM.step_of_some hs]
    change (padAction (M.tm.tr q c.inputSymbol _)).apply _ = _
    rw [hw]
    exact pad_apply _ _

/-- With a positive tape count, padding a seam gives the seam with the same state word. -/
private lemma pad_seam {k K : ℕ} {S : Type} {x : List Bool}
    (hk : 0 < k) (q : S) (w out : List Bool) :
    padCfg (K := K) ({Cfg.ofWords (input := x) q (stateWord k w) with output := out}) =
      {Cfg.ofWords (input := x) q (stateWord K w) with output := out} := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : i.val < k
    · simp [padCfg, Cfg.ofWords_def, stateWord_eq, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [padCfg, Cfg.ofWords_def, stateWord_eq, hi, hn, FinTM.bufferTape_eq]
  · funext i
    simp [padCfg, Cfg.ofWords_def]

/-! ### The host -/

/-- The states of the host over the modules `M : Fin n → FinTM Bool` with control states `C`:
`C ⊕ Σ i, (M i).State`, a control state or module `i` in one of its states. -/
abbrev State (C : Type) {n : ℕ} (M : Fin n → FinTM Bool) : Type :=
  C ⊕ Σ i, (M i).State

/-- The host's state type is `C ⊕ Σ i, (M i).State`. -/
theorem state_eq (C : Type) {n : ℕ} (M : Fin n → FinTM Bool) :
    State C M = (C ⊕ Σ i, (M i).State) :=
  rfl

/-- The entry state of module `i` inside the host: module `i` at its start state. -/
def entry {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (i : Fin n) : State C M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- The entry state of module `i` is `inr ⟨i, (M i).tm.q₀⟩`. -/
theorem entry_eq {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (i : Fin n) :
    entry (C := C) M i = .inr ⟨i, (M i).tm.q₀⟩ :=
  rfl

/-- **The clean-module host** over the modules `M : Fin n → FinTM Bool`: a finite machine with
`K` work tapes (`hk`: every module fits, all modules sharing tape 0), states `State C M`, start
state `q₀`. At a control state `inl c` it applies the consumer's table `ctrl c`; at a module
state `inr ⟨i, s⟩` it applies module `i`'s transition, padded to the `K` tapes and forwarded by
`Turing.emitAction`: the module's emission is the host's, a live successor stays in module `i`,
and a halt passes control to the return state `ret i`. -/
@[simps (config := { isSimp := false }) k tm_q₀]
def hostTM {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ)
    (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) : FinTM Bool where
  k := K
  State := State C M
  tm := {
    q₀ := q₀
    tr := fun q inp work => match q with
      | .inl c => ctrl c inp work
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (ret i)
          ((padTM (M i) K (hk i)).tm.tr s inp work) }

/-- **A control step.** At a configuration in the control state `inl c`, one step of the host
applies the consumer's action `ctrl c` for the scanned input and work symbols. -/
theorem hostTM_step_inl {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) {x : List Bool}
    (cfg : Cfg K Bool (State C M) x) (c : C) (hc : cfg.state = some (.inl c)) :
    (hostTM M K hk ctrl ret q₀).tm.step cfg =
      (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
  MultiTapeTM.step_of_some hc

/-- Forwarding a padded clean seam produces the host's seam with the supplied output prefix (a
positive tape count identifies the tape-zero word). -/
private lemma host_seam {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ)
    (ret : Fin n → State C M) (i : Fin n)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : State C M)) (ret i) pre
      (padCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : State C M))).getD (ret i)))
        (stateWord K w) with output := pre ++ out} := by
  have h := pad_seam (K := K) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h

/-- **A module call inside the host.** Suppose module `i` (with `0 < (M i).k`), run from the seam
at its start state with argument `arg`, is live before time `t` and at time `t` is halted at the
seam holding `result`, with output `out`. Then the host, run from its seam at the entry state of
module `i` holding `arg` with output prefix `pre`, visits no control state before time `t`, and
at time `t` is at the seam in the return state `ret i` holding `result`, with output
`pre ++ out`.

**Proof sketch.** The host seam is the forwarded image (`Turing.emitCfg`) of the padded module
seam (`host_seam`). The module's live run is transferred to the padded machine (`pad_run`) and
then to the host by `Turing.emit_run`, whose agreement hypothesis holds by the definition of
`hostTM`. Every live configuration of the module has a state in module `i`'s summand, hence is
not a control state; the halting endpoint is the forwarded image of the module's terminal seam,
i.e. the host seam at `ret i` (`host_seam` again). -/
theorem host_call {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
        ≠ some (.inl c)) ∧
    (hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
      {Cfg.ofWords (ret i) (stateWord K result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → State C M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (ret i) pre (padCfg (K := K) c) =
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} := by
    simpa [emb, c, entry] using
      host_seam M K ret i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v =
        emitCfg emb (ret i) pre (padCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (padTM (M i) K (hk i)).tm (hostTM M K hk ctrl ret q₀).tm emb (ret i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [pad_run]
        exact hg u (by omega))]
    rw [pad_run]
  constructor
  · intro v hv a
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg_state, padCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact host_seam M K ret i hp x result pre out q none

/-- **The head envelope of a host call** (H14's space clause for one call, inclusive of its
endpoint): run from its seam at the entry state of module `i` holding `arg` with output prefix
`pre`, the host has, at every time `v ≤ t`, every work head within `t` cells of the origin,
where all heads start (`Cfg.ofWords_workTapePos`). Under the hypotheses of `host_call`, `t` is
the duration of the call, so this bounds the heads throughout the call.

This is the coarse envelope from the time bound: one step moves each head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`). A sharper envelope follows from the proof of
`host_call` and is not stated here: before the return, the host's tape `j` is module `i`'s
tape `j` for `j < (M i).k` (the padded module runs in lockstep and the forwarding keeps every
physical field, `Turing.emit_run`), and every other tape stays blank with its head at the
origin, so the host's heads obey any head envelope of the module.

**Proof sketch.** `MultiTapeTM.workTapePos_runFrom_mem_Icc` from the host seam, whose heads are
at the origin, and `v ≤ t`. -/
theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) :
    ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos
        j| ≤ (t : ℤ) := by
  intro v hv j
  have key : ∀ c : Cfg K Bool (State C M) x, c.workTapePos j = 0 →
      |((hostTM M K hk ctrl ret q₀).tm.runFrom c v).workTapePos j| ≤ (t : ℤ) := by
    intro c hc
    obtain ⟨h1, h2⟩ :=
      Finset.mem_Icc.1 ((hostTM M K hk ctrl ret q₀).tm.workTapePos_runFrom_mem_Icc c v j)
    rw [hc] at h1 h2
    have hvt : (v : ℤ) ≤ t := by exact_mod_cast hv
    rw [abs_le]
    constructor <;> omega
  exact key {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
    (Cfg.ofWords_workTapePos (input := x) (entry (C := C) M i) (stateWord K arg) j)

/-- **Chaining guarded segments.** If the run from `c` avoids the state `anchor` before time `a`
and is at `d` at time `a`, and the run from `d` avoids `anchor` before time `b`, then the run
from `c` avoids `anchor` before time `a + b`. -/
theorem guard_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  intro v hv
  by_cases h : v < a
  · exact ha v h
  · have hva : a ≤ v := by omega
    rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
    exact hb (v - a) (by omega)

/-- **A clean module call inside the host.** If module `i` is `Clean` with result map `f`,
emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
`ret i` holding `f arg`, with output `pre ++ g arg`, and visits no control state before `t`.

**Proof sketch.** Unfold `Clean` for `x` and `arg` and apply `host_call` with the result word
`f arg` and the output `g arg`. -/
theorem host_clean {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ :=
    host_call M K hk ctrl ret q₀ i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- **A clean module call inside the host, with its head envelope** (the bounded call of
`host_clean` together with H14's space clause): if module `i` is `Clean` with result map `f`,
emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
`ret i` holding `f arg`, with output `pre ++ g arg`, visits no control state before `t`, and at
every time `v ≤ t` has every work head within `B |arg|` cells of the origin.

The envelope is the coarse one from the time bound (`host_call_envelope`, which also describes
the sharper envelope inherited from the module).

**Proof sketch.** `host_clean` gives `t` and the call; `host_call_envelope` at `t`, with
`t ≤ B |arg|`, gives the envelope. -/
theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧
      ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
          v).workTapePos j| ≤ (B arg.length : ℤ) := by
  obtain ⟨t, hp, ht, hguard, hend⟩ := host_clean M K hk ctrl ret q₀ i f g B h x arg pre
  refine ⟨t, hp, ht, hguard, hend, fun v hv j => ?_⟩
  have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
  exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB

end Turing.ModuleHost

## ===== TCSlib/Cryptography/Randomness/Derandomization.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Derandomization from pseudorandom generators (statement phase)

[PS10, Theorem 180.1]: if pseudorandom generators exist, then `BPP ⊆ DTIME(2^{n^ε})` for every
constant `ε > 0`.

**The formal reading.**
- **`BPP`** is `main`'s `Randomized.InBPP Randomized.polyTimeModel` ([AB09, Def 7.3]): an
  efficient verifier with randomness `polyLen a k |x|` and two-sided error `1/3` (decision D-6).
  It is inhabited: `P ⊆ BPP` is `Randomized.inBPP_polyTimeModel_of_mem_P`.
- **`DTIME(t)`** is `main`'s `Complexity.DTIME`, deterministic multi-tape time `O(t(n))`, the
  source's reading ("bounded by `O(t(n))`").
- **The bound** `2^{n^ε}` is taken with a real exponent and rounded up (`subexpBound`), so that
  every real `ε > 0` is covered, as in the source. It is at least `1` at every length
  (`subexpBound_pos`), so `DTIME (subexpBound ε)` is not empty for a trivial reason (`DTIME` of a
  bound that vanishes somewhere is).
- **"PRGs exist"** is `∃ G : PRG, G.Secure`, the ch. 2–4 layer's [PS10, Definition 77.1], secure
  against non-uniform distinguishers. A PRG of any stretch `ℓ(n) > n` gives one with any polynomial
  stretch by the ch. 2–4 expansion theorems (`PRG.Secure.truncate`, `prg_expand`), which the proof
  needs with a computable integer-root seed schedule and a syntactic polynomial output
  envelope, as specified in the proof sketch below.

## Main definitions

* `Randomness.subexpBound`: `n ↦ ⌈2^{n^ε}⌉`.

## Main results

* `Randomness.subexpBound_pos`: the bound is positive.
* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1, stated; a `sorry` under the source's sketch).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, Definitions 1.12 and 7.3 (`main`'s `DTIME` and `BPP`).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity TCSlib.Cryptography

/-- The subexponential time bound `n ↦ ⌈2^{n^ε}⌉` (real exponent, rounded up). -/
noncomputable def subexpBound (ε : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊

/-- The subexponential bound is the natural ceiling of `2^{n^ε}` with real exponents:
`subexpBound ε n = ⌈2^{n^ε}⌉₊`. -/
theorem subexpBound_eq (ε : ℝ) (n : ℕ) :
    subexpBound ε n = ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ := rfl

/-- The subexponential bound is positive at every length. -/
theorem subexpBound_pos (ε : ℝ) (n : ℕ) : 0 < subexpBound ε n :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)

/-- **Theorem 180.1: pseudorandom generators derandomize `BPP` in subexponential time**
[PS10, Theorem 180.1]: if a secure PRG exists, then every language of `main`'s `BPP` is in
`DTIME(2^{n^ε})` for every `ε > 0`.

**Proof sketch** (the source's, with the steps it leaves implicit; route note S3c).
1. Let `L ∈ BPP` have verifier `M` and randomness `m(n) = a(n+1)^k`. Fix an integer `d ≥ 2`
   with `1/d < min(ε,1)`. Compute `ℓ(n)` as the least natural `t` with `n ≤ t^d`, using integer
   comparisons and powers. Then `n ≤ ℓ(n)^d` and `ℓ(n) ≤ n^{1/d}+1`. No computation of an
   arbitrary real exponent is required. Expand the PRG to the syntactic polynomial envelope
   `P(s) = a(s^d+1)^k+s+1`, which exceeds `s` and covers `m(n)` whenever `s = ℓ(n)`.
2. Let `M'(x; u) = M(x; G(u)↾m(|x|))`, with seed length `ℓ(|x|)`. If infinitely many lengths
   have an input with acceptance-probability gap `> 1/12`, choose one corresponding bad input
   at each bad seed length. Its advice length is at most `s^d`. The verifier bridge, composed
   with prefix truncation, is therefore a distinguisher polynomial in `s`; the probabilities
   agree through `randProb_eq_uprob`. Each seed length has only finitely many corresponding
   input lengths, so infinitely many bad input lengths give infinitely many bad seed lengths,
   contradicting PRG security. The fixed `1/12` threshold leaves an explicit majority margin.
3. Eventually every input has probability gap at most `1/12`. Since `M` is correct with
   probability at least `2/3`, `M'` is correct with probability at least `7/12 > 1/2`.
   The majority over all seeds is correct. A finite table handles the remaining input lengths.
4. Construct a deterministic multi-tape machine enumerating the seeds, running `G` and `M`,
   and counting, using the shared TM construction layer. For some constants `C,C'`, its time
   is at most `2^{ℓ(n)} · poly(n) ≤ 2^{n^{1/d}+1+C log₂(n+1)+C'}`. Since `1/d < ε`, this is
   eventually at most `2^{n^ε}`; a constant factor absorbs the finite exceptions. This machine
   construction is the substantive remaining fill obligation, not supplied by the sketch. -/
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry

end TCSlib.Cryptography.Randomness
