# Ladner fill 7 (Codex): target 6 — `SAT_H_intermediate`, and with it `ladner`

## Repository and base — read this before anything else

- Repository: `https://github.com/Shilun-Allan-Li/tcslib` (the same repository as your exchange
  checkout).
- **Base commit:** `d811bdaaf5e923b2a57f0453135af5c7ee37713a`, the campaign
  `complexity/arora-barak-ch3-4` after Ladner fills 5 and 6 (#322). Targets 1–5 are proved there;
  `SAT_H_intermediate` is the file's only admission. Work on a local branch off it (suggested
  `fill/ladner-final`). Record the base in `REPORT.md`. Never rebase.
- **Delivery** is by zip pushed to the exchange and attached in chat; see "Delivery".

## What this is

Target 6 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.SAT_H_intermediate (h : P ≠ NP) : SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H`. The
packaging theorem `ladner` already follows from it with no proof change. **This fill proves target
6**, which removes the last admission from `Diagonalization/Ladner.lean`.

The route (bundled `ladner-fill-routes.md` §9):
- NP membership is target 2.
- **Outside P:** if `SAT_H ∈ P`, target 3 bounds `ladnerH` by some `C`. The literal padding map
  `x ↦ x ++ false :: 1^(|x|^h|x|)` is then polynomial-time and reduces SAT to `padSAT ladnerH`,
  so `SAT ∈ P` and `P = NP`.
- **Not NP-complete:** NP-completeness would make `padSAT ladnerH` NP-hard; target 4 gives
  divergence and target 5 then puts SAT in P.

## Scope: the private declarations to add, in `Diagonalization/Ladner.lean`

Add a section `/-! ### Bounded padding and the intermediate language -/` of **private**
declarations in namespace `Complexity` (prefix `ladner_`) **immediately before** the header
`/-! ### The theorem and its remaining targets -/` (after fill 5's NP-membership section), then
replace the body of `SAT_H_intermediate` (only its body). The bundled pre-ship probe
(`preship/Fill7Target6.lean.txt`) gives the statements:

- definition `ladner_padWord`;
- **your work** (admitted there): `ladner_bounded_pad_length`, `ladner_bounded_pad_FP` and
  `ladner_padWord_membership`;
- proved there, and usable as they stand: `ladner_bounded_pad_reduction`, `ladner_outside_P`,
  `ladner_not_complete`, and the target's assembly from targets 1–5.

`ladner_bounded_pad_FP` and `ladner_padWord_membership` are binding in meaning; the others are
guidance. Keep the proved parts unless a proof needs a change, and say so if you change one.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/Diagonalization/Ladner.lean`. Every existing declaration stays
**byte-identical**; only `SAT_H_intermediate`'s body changes (update its proof sketch only if it
no longer describes the proof). No import changes.

## Ground rules (binding)

1. **Statement freeze** for every existing declaration.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2, bundled): read other files' TCSlib
   definitions only through their published equations; core and Mathlib definitions may reduce by
   `rfl`, `decide` or `show` but are never passed to `simp`, `rw` or `unfold`. Use
   `polyTimeReducible_iff` and `NPComplete_iff` (never unfold `PolyTimeReducible` or
   `NPComplete`), `mem_P_of_polyTimeReducible`, `P_eq_NP_of_NPHard_mem_P`, `SAT_NPHard`,
   `SAT_H_eq`, `mem_padSAT_iff`, and the public FP closures (`polyTimeComputable_unary`,
   `BinArith.polyTimeComputable_mulU`, `append`, `pairEncode`, `polyTimeComputable_ite`).
   Escalate (E-READER) rather than unfold.
3. **No new hosts.** No new public declarations, files, imports, `@[simp]` attributes, `sorry`,
   `admit` or axioms. Do not publish a general "bounded padding reduces SAT" theorem; it stays
   private.
4. **Cite, do not re-prove.** The file already has the padding facts you need: `ladner_parse_pad`
   and `ladner_parse_some` (the final-false decomposition of `p ++ false :: 1^t`),
   `ladner_pad_membership`, `ladner_padSyntax_FP`, `ladner_lengthBits_FP` and fill 5's NP
   section. Search the import closure and these leaves before proving a helper fact.
   Re-deriving an existing fact, or copying an existing proof's text for a variant instead of
   factoring a private helper, is a duplication finding even when the copy screens miss it.
5. **Standards** (`policy.md`): docstrings cite [AB09, Theorem 3.3 and its proof] or library
   declarations; a `**Proof sketch.**` on every proof over 20 lines; no campaign labels in Lean
   text.
6. **Route risks to keep** (route §9): boundedness is of the exponent's **value**, not its
   encoded length, and a bit-length bound alone does not give an emitter. Build the unary power
   for the finitely many exponent values `0, …, C` (selected by canonical equality tests, each
   power by finitely many `polyTimeComputable_mulU` steps), or through `powCap` with a proven
   unary output budget. The empty prefix pads with `0 ^ 0 = 1`. The prefix is recovered at the
   **final** false separator.
7. **Escalate** anything unprovable as stated (E-STATEMENT) or a missing host (E-HOST). A clean
   frontier is a valid delivery; prefer finishing `ladner_padWord_membership` and the length
   bound first.

## Environment and verification

Follow the bundled fill-environment addendum (v2.6); **never run `lake build`**. Bootstrap the
import closure at the base into your own scratch olean tree. **At most 3 Lean processes may run at
once across the machine** (other fills share it): start at most one of your own at a time, and
check the machine-wide count first; record waits. Final checks, with exit codes:

- `Diagonalization/Ladner.lean` with zero errors and **no `sorry` warnings**;
- `#print axioms Complexity.ladner` and `#print axioms Complexity.SAT_H_intermediate` (via public
  scratch wrappers or a scratch copy, not in the library): at most `propext`, `Classical.choice`,
  `Quot.sound`;
- the facade `Diagonalization.lean` with zero errors.

## REPORT.md checklist

- [ ] Target 6 proved, or a frontier; the base.
- [ ] Every new declaration with its role; every other-file definition reached and the equation
      used; the existing facts searched for before each helper.
- [ ] Final check outputs, both axiom prints, and `git diff --stat` touching only `Ladner.lean`.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `fill-ladner-final.zip` with `REPORT.md`, the delivered `Ladner.lean`, the patch against
`d811bdaa`, and the check logs. Push it, with any `fill-ladner-final-checkpoint-N.zip`, to
`arora-barak-ch3-4/inbox/fill-ladner-final/` on the exchange branch after `git pull --rebase`,
without force and touching nothing else; also attach the final zip in chat. Do not push to any
other branch or open a pull request.
