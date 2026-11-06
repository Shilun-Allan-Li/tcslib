# External audit pack, round 5: NF's landing, the linear normal form (PR #191, a fill gate)

**Rounds 1–4** (`pack.md` … `pack-r4.md`; findings `findings.md` … `findings-r4.md`; dispositions
in `resolutions.md`) each found one major of one kind: an inline re-derivation of a published
lemma, ruled **repair** (the user, 2026-11-05). No round found a soundness defect in
`exists_codeNDTM_accepts_linear`.

**Round 4** was **does not close, 0 blockers, 1 major, 1 minor, 5 notes**:
- the major was `nf_ctl_position`'s `simp only` set, which reduced the fold over `s ++ [b]` by
  `foldl_append`, `foldl_cons` and `foldl_nil`, re-deriving `List.foldl_concat`; the round-3
  sweep had exempted chains in `simp` sets;
- the minor was the anonymous-`have` inventory, which listed 9 of 18 occurrences.

**The PR now:** #191 on `lean/c1-nf-landing`, head `c8cedd9d1a6905ef23f138f05a544ad92c0dd2e1`:
- `b4af93b744e240244d5705e2a3e1508e6cce8ddc` (`evidence/round5/patches/`), finding 1;
- then a merge of the campaign, which changes no `.lean` file (records only).

The PR changes one file, `TCSlib/Complexity/ClassNP/NDNormalForm.lean` (blob `e6a3f517`, 3,230
lines).

## What changed since round 4 (verify)

| Finding | Change |
|---|---|
| 1 | `simp only [List.foldl_concat, List.length_append, List.length_singleton]`, as proposed |
| 1, the sweep | **Every member of both chain classes anywhere in the file** (`evidence/round5/sweep/chain-classes.txt`): the fold over `l ++ [x]` and the length of a take, in `rw`, `simp only` and `simpa only` alike. The remaining uses are single citations: `foldl_nil` at five nil base cases; line 574's `foldl_append` over a general append (`flatMap_cons`) with `foldl_cons` on the outer fold; line 3077's `List.take_take` with `Nat.min_eq_left` (`exact?` finds no one-lemma form of `i ≤ j → (l.take j).take i = l.take i`, `NFLibE`). The pair `length_append`, `length_singleton` on `l ++ [a]` (lines 115, 142, 150) likewise has no one-lemma form found (`NFLibF`, whose control finds `foldl_concat`). Search results, not proofs of nonexistence |
| 2 | `anonymous-haves.txt` now lists every occurrence, mid-line and repeated: 18 on 17 lines, each dispositioned in `resolutions.md` (bounds, specialisations of local hypotheses, `min`/`max` bounds for `omega`); none is a re-derivation |

**Freeze** (`evidence/round5/freeze/`, `0908d0d6` → `e6a3f517`): public 1 → 1, private 104 →
104, nothing added or removed, no statement change; the one changed body is `nf_ctl_position`'s.

## Brief for the auditor

1. **Finding 1:** is the replacement right, and does any other chain of library rewrites anywhere
   in the file, a `simp` set included, compose to one published lemma?
2. **Finding 2:** is the anonymous-`have` inventory now complete and correctly dispositioned?
3. **Rule 10:** does the changed proof read other files' definitions only through published lemmas?

## Repository-side attestations (verify or challenge)

- **Elaboration** (`evidence/round5/elab/`): `e6a3f517` against `oleans-ldwa3`, **no output**,
  exit 0.
- **Rule 10** (`evidence/round5/seal/`): round 2's generator on `e6a3f517`, candidates by the Lean
  audit at its seven imports: the same 278 definitions as rounds 3 and 4 (`seal-set.txt`
  unchanged). Both sealed copies 0 diagnostics; generic controls 278 unsealed (`rfl` 268,
  equation 277) and 5 sealed, the same five instances; source controls 43 close unsealed and 43
  fail sealed; `summary.txt` 273 of 278 discriminated by the generic controls, the five by source
  controls.
- **Axioms** (`evidence/round5/axioms/`): `NFAx` on `e6a3f517`, the target on
  `[propext, Classical.choice, Quot.sound]`; `NTHAx` on `oleans-lnf6`, all seven theorems on the
  same three.
- **Screen** (`evidence/round5/screen/`): round 2's script and 23-file population at `c8cedd9d`:
  1,446 declarations, 13 pairs, 5,191 characters; the pair lines are byte-identical to round 4's
  (`pairdiff-r4.txt`: 0 new, 0 gone).
- **Replay** (`evidence/round5/merged-tree/`): `replay-lnf6` at `c8cedd9d`, `NDNormalForm`,
  `ClassNP`, `NTimeHierarchy` and `Diagonalization`, chained from `oleans-ldwa3`: **4 modules, 0
  failed, 0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/95-nf-landing-fill/findings-r5.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `nf-landing-fill-r5-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
