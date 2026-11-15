# Ladner fill 5 (Codex): target 2 — `SAT_H_mem_NP`

## Repository and base — read this before anything else

- Repository: `https://github.com/Shilun-Allan-Li/tcslib` (the same repository as your exchange
  checkout).
- **Base commit:** `34643146ee1fe6bf6d7ffdf2e543e8342a3e16a0`, the campaign
  `complexity/arora-barak-ch3-4` after Ladner fill 4 (#321, which proved target 1
  `ladnerH_polyTime`). Work on a local branch off it (suggested `fill/ladner-np`). Record the base
  in `REPORT.md`. Never rebase.
- **Delivery** is by zip pushed to the exchange and attached in chat; see "Delivery".
- **Another Ladner fill may run at the same time** on the same base and file. Put your new section
  exactly where "Scope" says, and change nothing else, so the two merge cleanly (the maintainer
  checked that the two sections and target bodies merge without conflict).

## What this is

Target 2 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.SAT_H_mem_NP : SAT_H ∈ NP`. The route (bundled `ladner-fill-routes.md` §7): parse the
final false separator, check the prescribed unary suffix with the saturated power, and verify SAT of
the recovered prefix with a certificate from the linear verifier. The deterministic parser supplies
the prefix, so no split is guessed. **This fill proves target 2.**

## Scope: the private declarations to add, in `Diagonalization/Ladner.lean`

Add a section `/-! ### NP membership of the padded language -/` of **private** declarations in
namespace `Complexity` (prefix `ladner_`) **immediately before** the header
`/-! ### The theorem and its remaining targets -/`, then replace the body of `SAT_H_mem_NP` (only
its body). The bundled pre-ship probe (`preship/Fill5Target2.lean.txt`) gives the statements:
`ladner_verifier`, `ladner_verifier_P`, `ladner_verifier_equiv` (admitted there) and
`ladner_padded_NP` (proved there from the two), and the target's assembly
(`rw [SAT_H_eq]; exact ladner_padded_NP ladnerH_polyTime SAT_exists_linear_verifier`), which is a
valid finish. `ladner_padded_NP`'s statement is binding in meaning; the others are guidance.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/Diagonalization/Ladner.lean`. Every existing declaration stays
**byte-identical**; only `SAT_H_mem_NP`'s body changes. No import changes.

## Ground rules (binding)

1. **Statement freeze** for every existing declaration; only the target's body changes.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2, bundled): read other files' TCSlib definitions
   only through their published equations; core and Mathlib definitions may reduce by `rfl`,
   `decide` or `show` but are never passed to `simp`, `rw` or `unfold`. Use
   `mem_NP_iff_exists_length_le`, `preimage_mem_P`, `inter_mem_P`, `mem_P_of_test`, the published
   pairing and parser leaves, and `SAT_H_eq`. `BinArith.decWords` is already irreducible
   (well-founded recursion). Escalate (E-READER) rather than unfold.
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
6. **Route risks to keep** (route §7): the SAT reader uses concatenation `prefix ++ u` while the NP
   reader uses `pairEncode y u`; keep both layouts. Check the last false separator, all-true
   rejection, the empty prefix, exponent zero and `0 ^ 0`. A polynomial bound on the exponent's
   **bit length** does not justify allocating the full power: compare through `powCap`
   (`ladner_padSyntax_FP`). `hp` is applied to the prefix, not the padded word.
7. **Escalate** anything unprovable as stated (E-STATEMENT) or a missing host (E-HOST). A clean
   frontier is a valid delivery.

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

Make `fill-ladner-np.zip` with `REPORT.md`, the delivered `Ladner.lean`, the patch against
`34643146`, and the check logs. Push it, with any `fill-ladner-np-checkpoint-N.zip`, to
`arora-barak-ch3-4/inbox/fill-ladner-np/` on the exchange branch after `git pull --rebase`, without
force and touching nothing else; also attach the final zip in chat. Do not push to any other branch
or open a pull request.
