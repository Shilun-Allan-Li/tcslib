# Ladner fill 6 (Codex): target 5 — `SAT_mem_P_of_padSAT_NPHard`

## Repository and base — read this before anything else

- Repository: `https://github.com/Shilun-Allan-Li/tcslib` (the same repository as your exchange
  checkout).
- **Base commit:** `34643146ee1fe6bf6d7ffdf2e543e8342a3e16a0`, the campaign
  `complexity/arora-barak-ch3-4` after Ladner fill 4 (#321, which proved target 1
  `ladnerH_polyTime`). Work on a local branch off it (suggested `fill/ladner-shrink`). Record the
  base in `REPORT.md`. Never rebase.
- **Delivery** is by zip pushed to the exchange and attached in chat; see "Delivery".
- **Another Ladner fill may run at the same time** on the same base and file. Put your new section
  exactly where "Scope" says, and change nothing else, so the two merge cleanly (the maintainer
  checked that the two sections and target bodies merge without conflict).

## What this is

Target 5 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.SAT_mem_P_of_padSAT_NPHard`: if `h` is polynomial-time, diverges, and `padSAT h` is
NP-hard, then `SAT ∈ P`. The route (bundled `ladner-fill-routes.md` §8) is the shrinking argument: a
reduction `f` from SAT eventually maps an instance to a padded word whose prefix has length at most
the square root of the instance length, so repeatedly shrinking (with finite tables for the small
cases) decides SAT in polynomial time. The loop runs on the existing public iterator. **This fill
proves target 5.** It does not use targets 1–4.

## Scope: the private declarations to add, in `Diagonalization/Ladner.lean`

Add a section `/-! ### Shrinking a reduction into the padded language -/` of **private**
declarations in namespace `Complexity` (prefix `ladner_`) **immediately before** the header
`/-! ### Polynomial-time preparation for the bounded candidate test -/` (that is, right after the
finite-table leaves `ladner_finite_lookup_FP` and `ladner_small_SAT_table`), then replace the body
of `SAT_mem_P_of_padSAT_NPHard` (only its body). The bundled pre-ship probe
(`preship/Fill6Target5.lean.txt`) gives the statements:
- definitions `ladner_smallSAT`, `ladner_shrinkStep`, `ladner_ShrinkInv`, `ladner_shrinkMeasure`;
- proved there: `ladner_reduction_from_hardness` (R3, R2, `SAT_mem_NP`), `ladner_smallSAT_FP` (the
  finite tables), `ladner_shrinking_transfer` (iterator, `mem_P_of_test`) and the target's assembly;
- admitted there: `ladner_prefix_square_bound`, `ladner_reduction_shrinks`, `ladner_shrinkStep_FP`,
  `ladner_shrink_progress`, `ladner_shrink_orbit_size`, `ladner_shrink_final_readout`.

The statements of `ladner_reduction_shrinks`, `ladner_shrinkStep_FP`, `ladner_shrink_progress` and
`ladner_shrink_final_readout` are binding in meaning; the others are guidance.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/Diagonalization/Ladner.lean`. Every existing declaration stays
**byte-identical**; only `SAT_mem_P_of_padSAT_NPHard`'s body changes. No import changes.

## Ground rules (binding)

1. **Statement freeze** for every existing declaration; only the target's body changes.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2, bundled): read other files' TCSlib definitions
   only through their published equations; core and Mathlib definitions may reduce by `rfl`,
   `decide` or `show` but are never passed to `simp`, `rw` or `unfold`. Use `NPHard_iff` and
   `polyTimeReducible_iff` (never unfold `NPHard` or a reduction),
   `PolyTimeComputable.output_length_le`, `SAT_mem_NP`, `mem_P_of_test`,
   `BinArith.polyTimeComputable_iterate`, `iterate_invariant` and `iterate_measure_eq_zero`.
   `BinArith.decWords` is already irreducible (well-founded recursion). Escalate (E-READER) rather
   than unfold.
3. **No new hosts.** Any loop applies the existing public iterator. No new public declarations,
   files, imports, `@[simp]` attributes, `sorry`, `admit` or axioms.
4. **Cite, do not re-prove.** Before proving a helper fact, search the import closure and the file's
   existing private leaves (fills 1–4: the parser `ladner_parse` with `ladner_parse_some`,
   `ladner_parsed_length`, `ladner_parse_FP`; `ladner_padSyntax_FP`/`ladner_syntax_FP`;
   `ladner_pad_membership`; `ladner_finite_lookup_FP`, `ladner_small_SAT_table`;
   `ladner_lengthBits_FP`; …) for a lemma that already states it, possibly in another presentation.
   Re-deriving an existing fact, or copying an existing proof's text for a variant instead of
   factoring a private helper, is a duplication finding even when the copy screens miss it. If the
   fact exists but cannot be reached by published equations, escalate (E-READER).
5. **Standards** (`policy.md`): docstrings cite [AB09, Theorem 3.3 and its proof] or library
   declarations; a `**Proof sketch.**` on every proof over 20 lines; no campaign labels in Lean
   text. Keep the target's statement, citation and docstring (update its sketch only if it no longer
   describes the proof).
6. **Route risks to keep** (route §8): validity of padding is decided before any recursion; prefix
   length `< B` and input length `< K` are distinct exceptional sets, each with its finite table; a
   terminal false flag is the nonempty word `[false]`, distinct from the live empty flag `[]`; `hp`
   has no growth restriction on `h`, so every power stays capped (`powCap` through
   `ladner_padSyntax_FP`); exactly one shrinking call per round, never branching over separators;
   the size bound must hold on every reached state; never assume monotonicity of `h`. The square
   bound applies to every syntactically valid output, including outputs on no-instances.
7. **Escalate** anything unprovable as stated (E-STATEMENT) or a missing host (E-HOST). A clean
   frontier is a valid delivery; prefer finishing the arithmetic (`prefix_square_bound`,
   `reduction_shrinks`) and `shrinkStep_FP` first.

## Environment and verification

Follow the bundled fill-environment addendum (v2.6); **never run `lake build`**. Bootstrap the
import closure at the base into your own scratch olean tree. **At most 3 Lean processes may run at
once across the machine** (other fills share it): start at most one of your own at a time, and check
the machine-wide count first; record waits. Final checks, with exit codes:

- `Diagonalization/Ladner.lean` with zero errors; its only `sorry` warnings are the targets still
  admitted after your fill;
- `#print axioms` for the target and the main new leaves (via public scratch wrappers, not in the
  library): at most `propext`, `Classical.choice`, `Quot.sound`;
- the facade `Diagonalization.lean` with zero errors.

## REPORT.md checklist

- [ ] The target proved, or a frontier; the base.
- [ ] Every new declaration with its role; every other-file definition reached and the equation
  used; the existing facts searched for before each helper.
- [ ] Final check outputs, axiom prints, and `git diff --stat` touching only `Ladner.lean`.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `fill-ladner-shrink.zip` with `REPORT.md`, the delivered `Ladner.lean`, the patch against
`34643146`, and the check logs. Push it, with any `fill-ladner-shrink-checkpoint-N.zip`, to
`arora-barak-ch3-4/inbox/fill-ladner-shrink/` on the exchange branch after `git pull --rebase`,
without force and touching nothing else; also attach the final zip in chat. Do not push to any other
branch or open a pull request.
