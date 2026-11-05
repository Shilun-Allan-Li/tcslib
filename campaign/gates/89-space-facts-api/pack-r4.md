# External audit pack, round 4: four space facts out of `Machines/ARMWidth`, and the logarithmic bounds' duplicates (PR #181, an API gate)

**Rounds 1–3** (`pack.md`, `pack-r2.md`, `pack-r3.md`; findings `findings.md`, `findings-r2.md`,
`findings-r3.md`; resolutions `resolutions.md`). Round 3: **OPEN, 0 blockers, 1 major, 0 minors.**
Its major: LS-1 (`logSpace n ≤ n + 1`) was still not retired. `ARMProof`'s `arm_decides` proved it
inline under the alias `Ls := logSpace n` with `Nat.log_lt_self`, and round 3's search, by
`Nat.log_le_self`, had missed it.

**The PR now:** #181 on `lean/logspace-move`, head `227d92ee4a91fa86860d1d1ddf3a98130fa674b9`.
Round 4's Lean commits (`evidence/round4/patches/0004`–`0007`):
- `a7c2a655`, `arm_decides` cites `logSpace_le_succ`;
- `fe4bdb67`, `logSpace_le_size_succ` moves to `Basic`, and `BPLInP` and `SpaceAmplifyPoly` cite it;
- `252bbcb8`, `ExpBFS/Run`;
- `227d92ee`, `ISCountGenCorrect`.

The two merges in between (`248e3796`, `3c091078`) bring in campaign records and change no Lean.
Against the campaign, #181 now changes fourteen Lean files: round 3's eight and six more.

## What changed since round 3 (verify)

The user ruled on each family the round-4 searches found (2026-11-04):

| File · declaration | Change | Ruling |
|---|---|---|
| `Machines/ARMProof` · `Complexity.LogProg.arm_decides` | `hLn`'s five-line proof (`simp only [hLs, logSpace]`, cases, `Nat.log_lt_self`) becomes `by rw [hLs]; exact logSpace_le_succ n` | round 3's finding 1 |
| `SpaceComplexity/Basic` · `Complexity.logSpace_le_size_succ` (new) | `logSpace n ≤ Nat.size n + 1`, moved from `Logspace/ISCountMath` (`Complexity.LogProg.ISCount.logSpace_le_size_succ`, removed). Statement and proof are byte-identical (`freeze/moved-lemma.txt`); the docstring gains a proof sketch. Listed under the file's main results | LS-2: "Fix in #181 now" |
| `Randomized/BPLInP` · `Randomized.BPLInP.two_pow_codes_le`, `Randomized.BPL_subset_P` | each inline re-derivation of `logSpace n ≤ |bits n| + 1` (`Nat.lt_size`, `Nat.pow_log_le_self`) becomes `logSpace_le_size_succ` through `Nat.size_eq_bits_len`; `two_pow_codes_le`'s sketch cites it | LS-2 |
| `Randomized/SpaceAmplifyPoly` · `Randomized.PolyAmp.logSpace_le_ell` | its proof (`ell n = |bits n| + 1`, `Nat.log_lt_of_lt_pow`) becomes `rw [ell, Nat.size_eq_bits_len]; exact logSpace_le_size_succ n` | LS-2 |
| `Logspace/ISCountGenCorrect` · private `size_le_logSpace` | `Nat.size n ≤ logSpace n`, re-derived through `Nat.size_le` and `Nat.lt_pow_succ_log_self`, now cites `LogProg.length_bits_le_log` (`Machines/Bin`) through `Nat.size_eq_bits_len` and `logSpace_eq` | LS-2's converse |
| `ExpBFS/Run` · `Complexity.LogProg.ExpBFS.setup_run` | `hhv : hv |x| ≤ |x|`, re-derived by cases and `Nat.log_lt_self`, now reads it from the same file's `lgv_le_succ` | with LS-2 |

`Logspace/ISCountMath`, `BPLInP`, `SpaceAmplifyPoly`, `ISCountGenCorrect` and `ARMProof` are
Hydroxyi's; `ExpBFS/Run` is shared. The edits are copy deletions and re-points under the user's
standing dedup exception and the ruling above (FYI to the author). Freeze (`evidence/round4/freeze/`,
each file at round 3's head `b8add1ac` against `227d92ee`):
- `Basic` +1 public (`logSpace_le_size_succ`); `ISCountMath` −1 public (the same);
- changed bodies only: `arm_decides`, `two_pow_codes_le`, `BPL_subset_P`, `logSpace_le_ell`,
  `setup_run`, and the private `size_le_logSpace`;
- nothing else.

The removed name has no other declaration or use on any of the 122 origin refs; its one use,
`ISCountGenCorrect:66`, now resolves to `Basic`'s lemma (`evidence/round4/api-search/`).

**Ledgered (user, 2026-11-04), not changed by #181:**
- **LS-3**, `|bits n| = Nat.log 2 n + 1` for `n ≠ 0`, three private copies; one is in E-D's
  in-flight `NTimeDiagonalizer`;
- **BL-1**, elementary bounds on the binary length carried over from Mathlib's `Nat.size` lemmas
  where a lemma already states them, five kinds across the library.

Both are accepted debt for the dedup window, scheduled in their ledger entries.

## Brief for the auditor

1. **Is LS-1 retired now, and LS-2 with it?** Read `evidence/round4/ls1-search/classification.md`,
   over `candidates.tsv` and `context.txt` (`ls1search.py`: every code line that touches `logSpace`'s
   definition, and every Mathlib upper bound of `Nat.log`; 91 lines in 60 declarations) and over
   `bitsweep.tsv` (`bitsweep.sh`: the binary-length sweep, 189 lines in 132 declarations; in
   context in `bitsweep-context.txt`). Its
   claims:
   - LS-1 is proved once, in `Basic`, and cited at nine sites;
   - LS-2 is proved once, in `Basic`, and cited at four sites;
   - LS-2's converse (`LogProg.length_bits_le_log`) is proved once and cited at fourteen sites;
   - every other candidate proves a different fact.

   Is any site a copy in another guise? Is the search's coverage argument (cite, unfold, or reduce
   through a (B) lemma) sound?
2. **The re-points:** are the six changed proofs correct and equivalent? Is the move of
   `logSpace_le_size_succ` faithful (statement, proof, home, and the namespace change from
   `Complexity.LogProg.ISCount` to `Complexity`)?
3. **The ledger** (`campaign/duplication-ledger.md`): LS-1's third correction, and the new LS-2
   (retired), LS-3 and BL-1 entries. Are they accurate? Does each one's named scope cover the
   sites the sweep shows?
4. **The screen, round 4** (`evidence/round4/screen/`): 24 files. They are round 3's 17, `ARMProof`, the
   five other new round-4 files (`ISCountMath`, `ISCountGenCorrect`, `BPLInP`, `SpaceAmplifyPoly`,
   `ExpBFS/Run`) and `PathHard` (its own `logSpace_le_ell`). Base is `711f5444` (a
   `git archive` export), head is `227d92ee`:
   - 232 → 232 declarations, 63 → 63 pairs, 16,287 → 16,255 characters, none new or gone;
   - the move counts once on each side;
   - `logSpace_le_ell`'s body falls under the screen's 60-character floor (142 → 55);
   - `size_le_logSpace`'s body rises over it (57 → 61).

   Is that right?
5. **Unchanged since round 3:** the seven other files of rounds 1–3. Confirm that round 4 touches
   none of them.

## Repository-side attestations (verify or challenge)

- **Elaboration** (`evidence/round4/elab/`, method in `evidence/round4/README.txt`): the seven round-4
  files, 0 diagnostics each. `ARMProof` ran against `oleans-lsm3`. The others ran in a clone of it
  with `Basic` and `ISCountMath` recompiled.
- **Lint** (`evidence/round4/lint/`): `campaign_style_lint` over `SpaceComplexity` and `Randomized`,
  0 FAIL and 83 + 51 WARN at both the export and the head; only line counts change. `style_lint`
  over the seven files gives 0 findings, except `SpaceAmplifyPoly:177` (`runVal_two_ge` has no
  proof sketch). That finding predates #181 and is in a proof #181 does not touch.
- **Replay:** `replay-lsm4.sh` (`evidence/round4/merged-tree/`), the fourteen files' downstream
  closure, 137 modules (the same closure as rounds 2–3). It builds fresh `.olean`s from
  `oleans-leqc3`, pinning the fourteen blobs. The precheck passed; **not yet run.**
  `replay-lsm3` (round 3's head) passed but no longer certifies the PR.
- **Overlap with #182** (gate 90): #181 merges first; #182 then takes one merged-tree replay of its
  closure from `oleans-lsm4`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/89-space-facts-api/findings-r4.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `space-facts-api-r4-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
