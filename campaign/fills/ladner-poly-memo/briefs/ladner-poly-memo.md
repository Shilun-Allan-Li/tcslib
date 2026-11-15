# Ladner fill 4 (Codex): target 1 part B — selection, memo driver, `ladnerH_polyTime`

## Repository and base — read this before anything else

- Repository: `https://github.com/Shilun-Allan-Li/tcslib` (the same repository as your exchange
  checkout).
- **Base commit:** `1320a5c8ce93f4644c2c92ed32e2768ed07ea9bb`, the campaign
  `complexity/arora-barak-ch3-4` after Ladner fill 3 (#320: part A of target 1, through the
  private `ladner_candidate_FP`). Work on a local branch off it (suggested
  `fill/ladner-poly-memo`). Record the base in `REPORT.md`. Never rebase.
- **Delivery** is by zip pushed to the exchange and attached in chat; see "Delivery".

## What this is

Target 1 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.ladnerH_polyTime : PolyTimeComputable (fun x => Nat.bits (ladnerH x.length))`.
Part A is merged. **This fill proves target 1.** It builds the route's part B (bundled
`ladner-fill-routes.md` §6, "selection" and "memo"): a scan over candidate indices selecting the
least successful one (or the cap), and a bottom-up memo table of `ladnerH` values, both run on the
existing public iterator, then the readout.

## Step 1 — the approved file reorder (Seyoon, 2026-11-15)

`ladnerH_polyTime` currently sits at line 197, before all the leaves it needs. **First**, as its
own commit, apply the bundled `preship/Ladner-move.patch.txt` (`git apply`). It moves the five
admitted declarations (`ladnerH_polyTime`, `SAT_H_mem_NP`, `SAT_mem_P_of_padSAT_NPHard`,
`SAT_H_intermediate`, `ladner`), with their docstrings, byte-identical and in order, to the end of
the file under the section header `/-! ### The theorem and its remaining targets -/`. Check the
result's SHA-256 is `4c9a04c3b28ae8a43cfded8ebdca4bf57b638214e82dabdccce7cd966ff0d914`. Make no
other change in that commit.

## Step 2 — scope: the private declarations to add, in `Diagonalization/Ladner.lean`

Add part B as **private** declarations in namespace `Complexity` (prefix `ladner_`), between
part A's section and the moved targets' section, then replace the body of `ladnerH_polyTime`.
The bundled pre-ship probe (`preship/Fill4PartB.lean.txt`) gives the statements:

- selection: `selectCtx`, `selectInit`, `selectStep`, `selectOut`, `selectInit_FP`,
  `selectStep_FP`, `select_size`, `select_readout`, `stage_FP` (the route's `SelectInv`,
  `selectMeasure` and `select_progress` are suggested helpers);
- memo: `memoInit`, `memoStep`, `stage_correct`, `memoStep_FP`, `memoInit_FP`, `memo_orbit`,
  `memo_size`, `memo_readout`;
- **the target:** `ladnerH_polyTime`, statement frozen, proved without `sorry`. The probe's
  assembly (iterator plus `BinArith.polyTimeComputable_getW`, using `ladner_candidate_FP` with the
  public `SAT_exists_linear_verifier`) is a valid finish.

The probe's helper statements are binding **in meaning** for `ladner_stage_FP`,
`ladner_stage_correct` and `ladner_memo_readout`; the others are guidance. Adjust them if a proof
needs it, and say so. Use part A as merged: `ladner_values`, `ladner_stage`, `ladner_candidate`
and `ladner_candidate_FP` are frozen.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/Diagonalization/Ladner.lean`. After step 1, every existing declaration
(including all part A and earlier leaves, fill 1's targets, and the four other admitted targets)
stays **byte-identical**. Only `ladnerH_polyTime`'s body changes. No import changes.

## Ground rules (binding)

1. **Statement freeze** for every existing declaration.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2, bundled): read other files' TCSlib
   definitions only through their published equations; core and Mathlib definitions may reduce by
   `rfl`, `decide` or `show` but are never passed to `simp`, `rw` or `unfold`. Use the route's §2
   API (`BinArith.polyTimeComputable_iterate`, `iterate_invariant`, `iterate_measure_eq_zero`;
   `encWords_append_singleton`, `decWords_encWords`, `length_encWords_le`; `getW_pairEncode_bits`,
   `polyTimeComputable_getW`; `countW_eq`), and `ladnerH`'s own `ladnerH_eq` and `ladnerH_le`.
   `BinArith.decWords` is already irreducible (well-founded recursion); read it by its equations.
   Escalate (E-READER) rather than unfold.
3. **No new hosts.** Both scans apply the existing public iterator; no private memo host or
   transition table. No new public declarations, files, `@[simp]` attributes, `sorry`, `admit`
   or axioms.
4. **Cite, do not re-prove.** Before proving a helper fact, search the import closure and the
   file's existing private leaves (fills 1–3) for a lemma that already states it, possibly in
   another presentation. A re-derivation of an existing fact is a duplication finding even when
   the copy screens miss it; so is copying an existing proof's text for a variant (factor a
   private helper instead). If the fact exists but cannot be reached by published equations,
   escalate (E-READER).
5. **Standards** (`policy.md`): docstrings cite [AB09, Theorem 3.3 and its proof] or library
   declarations; a `**Proof sketch.**` on every proof over 20 lines; no campaign labels in Lean
   text. Update `ladnerH_polyTime`'s docstring only if its proof sketch no longer describes the
   proof; keep the statement and citation.
6. **Route risks to keep** (route §6): count table entries with `countW`, not serialized length;
   the size bound must hold on **every** state of both scans, including after termination;
   `stage_correct` needs `padSAT_congr` on each queried prefix (shorter than its word, which is at
   most `log₂ j`); a never-successful selection returns the exact cap; never assume `ladnerH` is
   monotone.
7. **Escalate** anything unprovable as stated (E-STATEMENT) or a missing host (E-HOST). A clean
   frontier is a valid delivery; prefer finishing the selection scan and `stage_correct` first.

## Environment and verification

Follow the bundled fill-environment addendum (v2.6); **never run `lake build`**. Bootstrap the
import closure at the base into your own scratch olean tree. **At most 3 Lean processes may run at
once across the machine** (other fills share it): start at most one of your own at a time, and
check the machine-wide count first; record waits. Final checks, with exit codes:

- `Diagonalization/Ladner.lean` with zero errors; its only `sorry` warnings are the three
  remaining admitted targets (`SAT_H_mem_NP`, `SAT_mem_P_of_padSAT_NPHard`,
  `SAT_H_intermediate`);
- `#print axioms Complexity.ladnerH_polyTime` and the main new leaves (via public scratch
  wrappers, not in the library): at most `propext`, `Classical.choice`, `Quot.sound`;
- the facade `Diagonalization.lean` with zero errors.

## REPORT.md checklist

- [ ] Target 1 proved, or a frontier; the base; the step 1 commit and its SHA-256 check.
- [ ] Every new declaration with its role; every other-file definition reached and the equation
      used; the public facts searched for before each helper.
- [ ] Final check outputs, axiom prints, and `git diff --stat` touching only `Ladner.lean`.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `fill-ladner-poly-memo.zip` with `REPORT.md`, the delivered `Ladner.lean`, the patch against
the base (both commits), and the check logs. Push it, with any
`fill-ladner-poly-memo-checkpoint-N.zip`, to `arora-barak-ch3-4/inbox/fill-ladner-poly-memo/` on
the exchange branch after `git pull --rebase`, without force and touching nothing else; also attach
the final zip in chat. Do not push to any other branch or open a pull request.
