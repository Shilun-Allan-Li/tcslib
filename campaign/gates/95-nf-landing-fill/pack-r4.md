# External audit pack, round 4: NF's landing, the linear normal form (PR #191, a fill gate)

**Rounds 1–3** (`pack.md`, `pack-r2.md`, `pack-r3.md`; findings `findings.md`, `findings-r2.md`,
`findings-r3.md`; dispositions in `resolutions.md`) each found one major of one kind: an inline
re-derivation of a published lemma, ruled **repair** (the user, 2026-11-05). No round found a
soundness defect in `exists_codeNDTM_accepts_linear`.

**Round 3** was **does not close, 0 blockers, 1 major, 1 minor, 5 notes**. The major was
`nf_display_firstStop`'s `he`: an untyped `have` of `Nat.mod_add_div`, rewritten by the zero
remainder, re-proving `Nat.mul_div_cancel'`. The minor was the pack's line count, recorded as an
erratum.

**The PR now:** #191 on `lean/c1-nf-landing`, head `b2bac06f2bba0b9318ef24e2d210fe34ea38b540`:
- `698dcdf5b9d66d05a27b684c4b17ca7f80d97001` (`evidence/round4/patches/`), finding 1;
- then a merge of the campaign, which changes no `.lean` file (records only since round 3).

The PR changes one file, `TCSlib/Complexity/ClassNP/NDNormalForm.lean` (blob `0908d0d6`, 3,231
lines).

## What changed since round 3 (verify)

| Finding | Change |
|---|---|
| 1, `nf_display_firstStop`'s `he` | `have he := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)`, in place of the `Nat.mod_add_div` line and its rewrite, as proposed |
| 1, the sweep's gap | The round-3 sweep took typed `have`s and proof blocks; this `have` was untyped, its content stated only by the rewrite after it. **The extended sweep** (`evidence/round4/sweep/`) covers that pattern: every untyped `have` or `obtain` whose term heads with a core or Mathlib name, with any rewrite `at` it or `▸` transport within eight lines (`untyped-haves.txt`, 11 sites), and every anonymous `have :=` (`anonymous-haves.txt`, 9 sites) |
| | Of the eleven, one other is rewritten afterwards: `nf_display_flag`'s `hm` (line 231), the round-3 sweep's C02, `(W * (r + 1) - 1) % W = W - 1` by `Nat.mod_add_div` and the computed quotient. No library lemma states it: `exact?` fails on two generalisations (`NFLibD.out`), and `Nat.mod_eq_sub_iff` leaves a divisibility side goal. It stays an idiom. The other ten are direct citations. The nine anonymous `have`s are `min`/`max` bounds handed to `omega` and local hypotheses |
| 2, the line count | Erratum in `resolutions.md`: round 3 was 3,272 → 3,232 (40 lines, 39 from the sweep), by `wc -l` of the blobs |

**Freeze** (`evidence/round4/freeze/`, `dfd8c408` → `0908d0d6`): public 1 → 1, private 104 →
104, nothing added or removed, no statement change; the one changed body is
`nf_display_firstStop`'s.

## Brief for the auditor

1. **Finding 1:** is the replacement right and statement-preserving?
2. **The extended sweep:** does any library-only fact remain proved by hand, in a typed `have`, an
   untyped one, an `obtain`, a `show`/`calc` step or a rewrite chain? Challenge C02's idiom
   disposition if a lemma states it.
3. **Rule 10:** does the changed proof read other files' definitions only through published lemmas?

## Repository-side attestations (verify or challenge)

- **Elaboration** (`evidence/round4/elab/`): `0908d0d6` against `oleans-ldwa3`, **no output**,
  exit 0.
- **Rule 10** (`evidence/round4/seal/`): round 2's generator on `0908d0d6`, candidates by the Lean
  audit at its seven imports: the same 278 definitions as round 3 (`seal-set.txt` unchanged). Both
  sealed copies 0 diagnostics; generic controls 278 unsealed (`rfl` 268, equation 277) and 5
  sealed, the same five instances; source controls 43 close unsealed and 43 fail sealed;
  `summary.txt` 273 of 278 discriminated by the generic controls, the five by source controls.
- **Axioms** (`evidence/round4/axioms/`): `NFAx` on `0908d0d6`, the target on
  `[propext, Classical.choice, Quot.sound]`; `NTHAx` on `oleans-lnf5`, all seven theorems on the
  same three.
- **Screen** (`evidence/round4/screen/`): round 2's script and 23-file population at `b2bac06f`:
  1,446 declarations, 13 pairs, 5,191 characters; the pair lines are byte-identical to round 3's
  (`pairdiff-r3.txt`: 0 new, 0 gone).
- **Replay** (`evidence/round4/merged-tree/`): `replay-lnf5` at `b2bac06f`, `NDNormalForm`,
  `ClassNP`, `NTimeHierarchy` and `Diagonalization`, chained from `oleans-ldwa3`: **4 modules, 0
  failed, 0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/95-nf-landing-fill/findings-r4.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `nf-landing-fill-r4-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
