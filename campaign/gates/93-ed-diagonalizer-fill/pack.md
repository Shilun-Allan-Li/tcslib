# External audit pack: E-D, the lazy diagonalizer (PR #188, a fill gate)

## What this gate covers

The fill brief E-D is `campaign/fills/eq/briefs/eq-fill-diagonalizer.md`, issued at
`c8b0711408c02a2c7e254663511ecdb65516ae88`. It sits in the Arora–Barak chapters 3–4 plan, C1-E:
the diagonalizer of the nondeterministic time hierarchy, [AB09, proof of Theorem 3.2]. It has one
target, `Turing.NTimeDiag.exists_diagonalizer` in
`TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean`.

**Delivered complete** by the worker (Claude, one fill):
- the report is `campaign/fills/eq/reports/eq-fill-diagonalizer-REPORT.md`;
- the evidence is `campaign/fills/eq/evidence/eq-fill-diagonalizer/`, including the delivered
  patches and the delivery's checksums.

**The maintainer's review** is `campaign/fills/eq/reviews/ed-fill/REVIEW.md`, with `out/`,
`probe/`, `scripts/` and `land/`. Verdict: **land with edits; 0 blockers, 3 majors, 4 minors,
11 notes.**

**Ruled by the user, 2026-11-04:**
- **F1 acknowledged.** `dz_word_lt` re-derives BL-1 kind (vi), the word-value bound. The file
  cannot import `Machines/Bin`, so the copy waits for the dedup window (12.2c).
- **The other recommendations, all:**
  - the landing edits E1–E7;
  - F2 and F3 removed by E3 and E4;
  - the frozen proof sketch left to the deferred docstring cleanup (F9);
  - the commit subjects reworded, with the `Claude-Session:` trailers dropped;
  - the ledger entries (`campaign/duplication-ledger.md`, "E-D's delivery").

**The head** is `lean/ed-diagonalizer` at `dae7929c8fc99b2210faedea2cb0ac1d4cc41752`
(`evidence/patches/`, 12 commits):
- **the worker's 11 commits,** cherry-picked from the verified bundle in order. Authorship and
  bodies are kept. The subjects are reworded per the review's F17 table, and the `Claude-Session:`
  trailers are dropped. At the eleventh, the owned file equals the delivered head's (blob
  `4b72d525`);
- **`f77abee9`, the maintainer's commit.** Its file equals the review's tested landed file (blob
  `fc65a848`; the diff is `evidence/landing-edits.diff`). It makes edits E1–E7:
  - E1, `qy_call_bound`'s `hb := Turing.length_bits_le_self (f a)`, the brief's landing item;
  - E2, `ne_eq` instead of `rw [Ne, …]`;
  - E3, a citation of `Nat.ofDigits_append_replicate_zero`;
  - E4, a citation of `MultiTapeTM.exists_first_halt`;
  - E5–E7, docstrings, among them the target's `**Implementation.**` paragraph;
- **a merge of the campaign** after #181 and #182. It leaves the owned file unchanged.

## What changed (verify)

| Class | Change |
|---|---|
| **Target's body** | `exists_diagonalizer`: `sorry` → a 22-line body from the kit, `D`, `K` and the middle and top lemmas |
| **Privates** | 214 → 320: the setup `P = dzSet` (12 phases), the run `Q = dzQ` (23 phases), `D = dzD` (`guessRunTM` bundled as a `FinNDTM`), the private leaf `dzTakeTM` (RC-2), the clocked hosted run, and the halting and acceptance lemmas |
| **Frozen** | every public statement (22 → 22) and every pre-existing declaration, down to the kernel terms, except the target's proof (review §(b), `out/11d-hash-compare.txt`) and, at landing, `qy_call_bound`'s proof (E1; its type unchanged, `out/33b-land-vs-head.txt`) |
| **Imports** | the overlay's three (region (a)) |
| **Text** | the new docstrings; the module header's status line; three label-bearing lines of the target's docstring rewritten as public text; E6's Implementation paragraph |

## Brief for the auditor

1. **Correctness.** Is `exists_diagonalizer` proved as stated? In particular:
   - the uniform `K`: it is built from the kit's constants only, and the step clock cuts the core
     at `g n`;
   - the `g n = n` boundary, which the statement gate required;
   - the middle in both directions, and the top;
   - `D` as `guessRunTM` over the phase-host setup and run (review §(h)).
2. **Route conformance** (review §(g)): the brief's binding rows, and the ruled own leaf
   `dzTakeTM` (RC-2).
3. **Duplication.**
   - The review's F1–F3 and F11–F13, and the ledger entries.
   - **The worker's screens:** 44 new pairs, one at 98%, `dz_split_stream` against `NDHost`'s
     private `guessRun_split`. That is a promotion request; the review's own head screen reproduces
     the screens byte for byte (`out/17-*`).
   - **The landing head:** `evidence/screen/`, a run of the v3 screen restricted to pairs with an
     `NTimeDiagonalizer` declaration on one side, over the brief's 38-file population at the
     landing head. It is compared with the review's head screen restricted the same way.
   - F2 and F3 had re-proved sub-steps (Mathlib's `Nat.ofDigits_append_replicate_zero`, FH-1's
     `exists_first_halt`). Is any other inline step a re-derivation of a lemma in the closure?
4. **Rule 10**, under the 2026-10-23 scope:
   - the review's maximal seal: 350 definitions, 4 `simp` erasures, and a control per definition
     that passes unsealed and fails sealed (`out/14*`, `out/34-land-seal-*`);
   - the tactic-argument inspection (`out/14b-inspection-table.txt`);
   - F4, `Ne` passed to `rw`, fixed by E2.

   Is any other-file definition unfolded or closed by reduction?
5. **Rule 11:** the public constants (F10).
6. **The public-facing text** after E5–E7 and E6's paragraph; F9's frozen sketch, deferred.
7. **The landing.** Are the 11 cherry-picks the delivered commits (patch-ids; the delivered patches
   are in the evidence), and is the maintainer's commit exactly E1–E7?

## Repository-side attestations (verify or challenge)

- **Elaboration** (the review's `out/32-*`, `out/40-tip-*`): the landed file, `NTimeHierarchy` and
  the facade exit 0 with no output, on the base snapshot and on a clone of the tip after #181.
  Every one of the module's 1,846 constants is within `[propext, Classical.choice, Quot.sound]`
  (`out/33-land-audit.out`).
- **Replay:** `replay-led` (`evidence/merged-tree/`) covers `NTimeDiagonalizer`, `NTimeHierarchy`
  and `Diagonalization`, chained from `oleans-larm2` (the tip after #182). **Passed:** 3 of 3 at
  `dae7929c`, 0 failed, static-equal with no sorry warning. `NTimeHierarchy`'s three theorems still
  reach `sorryAx` through the normal form `exists_codeNDTM_accepts_linear`, which lands separately.
- **Lint** (review §(j)): `campaign_style_lint` 0 FAIL; the policy linter reports the file's size
  only.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/93-ed-diagonalizer-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `ed-diagonalizer-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
