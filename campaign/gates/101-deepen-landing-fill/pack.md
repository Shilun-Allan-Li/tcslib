# External audit pack: the deepening fill's landing, `Complexity.savitch` (PR #208, a fill gate)

## Why this PR

`Complexity.savitch` ([AB09, Theorem 4.14]; [Sav70]) was the campaign's last `sorry` in
`SpaceComplexity/Savitch`. The deepening fill (brief `campaign/fills/ch34/briefs/ch34-fill-deepen.md`,
agent Claude) proves it for every `S ≥ logSpace` without computing the space bound: a register
machine `D` runs Savitch's midpoint search at radius `s = 1, 2, …` and stops once no configuration
reaches the window's edge ([Sip13, §8.1, proof of Theorem 8.5]). Its API is gate 96's (#196).

**The PR:** #208 on `lean/ch34-deepen-landing`, head `a074d9b7ef0eb5c82bb248254f5f599081e0521b`:
- the delivery, `fill/ch34-deepen` at `c7b179da` (base `fd97df61`; seven commits, kept as
  delivered; `campaign/fills/ch34/reports/deepen-REPORT.md`);
- the maintainer's landing edits `a46e04a9` and `eeceae9f` (`evidence/landing/`), from a review
  of the delivery (`evidence/review/REVIEW.md`) and a have-level library sweep (`evidence/sweep/`);
- merges of the campaign, which change none of the PR's files.

It changes three files: `SpaceComplexity/SavitchARM/Deepen.lean` (new, 845 lines),
`SpaceComplexity/Savitch.lean` and the facade `SpaceComplexity.lean`.

## What changed (verify)

| Declaration | What |
|---|---|
| `Complexity.LogProg.SavitchARM.DeepenContract` (new, pinned) | the hypothesis of `arm_decides_SPACE` for `L` and `sp`: a register machine with logspace deciders halts with `x ∈ L`, registers of at most `C · (sp |x| + logSpace |x| + 1)²` digits |
| `Complexity.LogProg.SavitchARM.deepen_contract` (new, pinned) | `N.DecidesInSpace L sp → DeepenContract L sp`, through the private machine `dpD` and 43 `dp`/`Dp` privates |
| `Complexity.savitch_of_logSpace_le` (new, pinned) | `(∀ n, logSpace n ≤ S n) → NSPACE S ⊆ SPACE fun n => S n * S n`, from `deepen_contract` and `arm_decides_SPACE` |
| `Complexity.savitch` (frozen statement) | its body is `savitch_of_logSpace_le S hS.1` |
| `Savitch.lean`'s and the facade's text | the module docstring's intro, Status, Design, results and references; the facade's import and list line |

**The landing edits** (`evidence/landing/landing-edits.diff`; no statement changes):
- **The review's majors:** `2 ^ w ≤ 2 ^ (w · w)` was re-proved three times inline, now
  `(size_facts _).2` (`SavitchARM/Recursion`); the binary length against `logSpace` re-derived
  `Machines/Bin`'s `length_bits_le_log`, now cited.
- **The sweep's hits:** `dp_mem`'s iff is `decide_eq_true_iff`; `dp_run`'s `hn` is
  `Nat.size_le.mp`; three `le_trans`/`Nat.le_mul_of_pos_left` chains are
  `le_mul_of_one_le_of_le`. Also `Nat.mul_self_le_mul_self` at two squares, and an unused conjunct
  of the private `dp_bits_logSpace` dropped.
- **The review's minors:** `dpρ` is `Fin.castLE` and `dpρ_inj` `Fin.castLE_injective`;
  `deepen_contract`'s and `DeepenContract`'s docstrings state their content, without the campaign
  label "the fill's main theorem"; `dp_fit`'s sketch no longer cites a probe; in `Savitch.lean`,
  the intro (Savitch's midpoint search, not the configuration graph of `ConfigGraph`), the Status
  sentence (`savitch_of_logSpace_le` for every `S ≥ logSpace`, `savitch` from it), the Design
  bullet's radius in terms of `c · S`, the deviation's `[Sip13]` tag, and the results list's tags.

## Known deviations and dispositions (for the audit)

- **`DeepenContract` has no `_iff`** (campaign lint check 8, 80 → 81 WARN). The brief pins it and
  forbids a fourth public declaration; it is read by `obtain` in `savitch_of_logSpace_le` only.
- **`dpD` is a private host** (policy §1, *Hosts come first*): the brief designs the deepening
  machine as a private of `Deepen`; a candidate for a later harvest.
- **`dpSt` and its lemmas** split the register file between the two blocks' registers (through
  `dpρ`) and `D`'s own. It is close to `RegExt`/`RegExt.update` (`Machines/ARMProof`) and to
  Mathlib's `Fin.append`, but they are definitions with different shapes, not a re-derived lemma;
  the review ranked it minor and asked for this disposition.
- **Not citable here** (outside `Deepen`'s three imports, which the brief fixes): the private
  `bits_succ_le` (`Logspace/ISCountGenCorrect`), `ExpBFS.two_le_codeK`, `lt_two_pow_bits`,
  `indicator_eq_true_iff`. Promotion candidates, not members of any family.
- **The REPORT's errata** (the review's finding 10): `Deepen.lean` was 848 lines at the delivery,
  not 844; `ExpBFS.two_le_codeK` exists (but is outside the imports); the checkpoint zips were not
  delivered; the inspection table's `rw (no list)` rows misread the register name `rw`.
- **Edits outside region (d)'s literal list** (`Savitch.lean`'s results list and references):
  accepted by the maintainer, as policy §1–§2 require them.
- `Savitch.lean`'s `ConfigGraph` import may now be unused; left for a later edit.

## Brief for the auditor

1. **Soundness and pins:** are the three pins exactly as in the brief, `savitch`'s statement frozen,
   and the proofs correct, including the edge cases the brief lists (`x = []`, `N.k = 0`,
   `sp |x| = 0`, the halving loop at `n = 0`)?
2. **Rule 10:** do the proofs read other files' definitions only through published equations? The
   seal and its controls are below.
3. **Duplication:** does any proof still re-derive a published lemma (typed or untyped `have`,
   `simp` set, rewrite chain, conjunct)? The review and the sweep list every candidate with a
   disposition. Challenge any.
4. **Public text:** are the docstrings accurate, free of campaign labels, and attributed?

## Repository-side attestations (verify or challenge)

- **The delivery** (`evidence/delivery/`): its `SHA256SUMS` (54 entries, all verified), the bundle
  and patch series checked against the source copies by the maintainer; its logs (preflight,
  cache, the 196-module bootstrap, the final sweep, axioms, lint).
- **Rule 10** (`evidence/seal/`): the delivery's generator `mkseal_deepen.py` re-run on the landing
  head's `Deepen.lean`: 35 definitions sealed (the block fit's 22, `NoEdge`, the loop section's
  four and eight of the fill's own reach). The sealed copy elaborates with **0 diagnostics**
  against `oleans-lcamp1`; the delivery's controls, on `oleans-ldp2`, fail at all 35 sealed goals,
  at the same lines as the delivery's own run.
- **Axioms** (`evidence/axioms/`, on `oleans-ldp2`): `savitch`, `savitch_of_logSpace_le`,
  `deepen_contract` and `NPSPACE_subset_PSPACE` on `[propext, Classical.choice, Quot.sound]`.
- **Freeze** (`evidence/freeze/`): `Savitch` 2 → 3 public (`savitch_of_logSpace_le` added),
  `savitch`'s body the one authorized change; `Deepen` new, 2 public and 43 private.
- **Screen** (`evidence/screen/`): the brief's 20-file population at the landing head: 299
  declarations, 96 pairs, 27,259 characters, the base's 96 pairs exactly (0 new); no pair has a
  `Deepen` declaration on either side.
- **Lint** (`evidence/lint/`): the campaign lint 0 FAIL, 81 WARN over 112 files (the one new WARN is
  `DeepenContract`'s check 8, above); the policy linter 0 findings on `Deepen` and `Savitch`.
- **Replay** (`evidence/merged-tree/`): `replay-ldp2` at `a074d9b7`, `Deepen`, `Savitch` and the
  `SpaceComplexity` facade, chained from the campaign's snapshot `oleans-lcamp1`: **3 modules, 0
  failed, 0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/101-deepen-landing-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as `deepen-landing-fill-findings.md`** (the findings table and the verdict
line, no other wrapping): push it to `arora-barak-ch3-4/inbox/` on the branch
`exchange/pass-shelat-ch5-8` (`git pull --rebase` first, add only that file, never force-push, no
PR), and also paste its content in your reply. If you cannot push, say so and paste it only.
