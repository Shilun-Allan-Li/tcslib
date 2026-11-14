# Ladner fill 3 (Codex): target 1, part A — the candidate test is polynomial-time

## Repository and base — read this before anything else

- Repository: `https://github.com/Shilun-Allan-Li/tcslib` (the same repository as your exchange
  checkout).
- **Base commit:** given in the dispatch prompt: the campaign `complexity/arora-barak-ch3-4` after
  Ladner fill 2 (the saturated power `BinArith.powCap` and the private padding parser) has landed.
  Work on a local branch off it (suggested `fill/ladner-poly-candidate`). Record the base in
  `REPORT.md`. Never rebase.
- **Delivery** is by zip pushed to the exchange and attached in chat; see "Delivery".

## What this is

Target 1 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.ladnerH_polyTime : PolyTimeComputable (fun x => Nat.bits (ladnerH x.length))`. The
Codex route draft (bundled, `ladner-fill-routes.md` §6) computes `ladnerH` bottom-up: a memo table
of earlier values; at each stage, a scan over candidate indices; for each candidate, a scan over all
short words, running the uniform simulator with a capped deadline and a short SAT search. **This
fill is part A: everything up to the polynomial-time candidate test.** Part B (the candidate
selection, the memo driver, its readout and the target itself) is a later fill. **This fill proves
no Ladner target.**

## Scope: the private declarations to add, in `Diagonalization/Ladner.lean`

The route's §6 declarations from `values` through `candidate_FP`, as **private** declarations in
namespace `Complexity` (prefix names `ladner_`):

- specifications: `values`, `shortWords`, `stage`, `candidate`, `ctxGuard`, `wordVerdict`,
  `queryCount`, `testInit`, `testStep`, `testOut`, `validQuery`, `queryCode`, `queryInput`,
  `queryDeadline`, `queryPrep` (`memoInit` and `memoStep` may be added here or in part B);
- arithmetic and counting: `shortWords_complete`, `shortWords_count`, `short_deadline`,
  `numeric_envelope`, `short_SAT_envelope`, `composition_clock`, `log_eq_bits_length`;
- machines: `short_SAT_machine`, `simulation_on_image`, `short_SAT_on_image`,
  `query_preparation`, `query_budget`, `short_pad_FP`, `binary_log_FP`, `wordVerdict_FP`,
  `testInit_FP`, `testStep_FP`;
- the scan: `test_orbit`, `test_size`, `candidate_readout`;
- the handoff to part B, **binding in meaning**:

```lean
private theorem ladner_candidate_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S => [ladner_candidate S])
```

with `ladner_candidate` as the route's `candidate`. The other statements in the bundled pre-shipped
probe (`Fill3PartA.lean.txt`) are guidance: adjust them if a proof needs it, and say so. The linear
SAT verifier is the merged public `Complexity.SAT_exists_linear_verifier`; you may keep it as a
hypothesis, as the route does, or apply it.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/Diagonalization/Ladner.lean`. Every existing declaration, including all targets
(proved and admitted) and fill 2's private leaves, stays **byte-identical**. You may add the
approved imports `ClassP.BinaryArith.Loops` and `ClassP.ModelInvariance` if not present.

## Ground rules (binding)

1. **Statement freeze** for every existing declaration.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2, bundled): read other files' TCSlib
   definitions only through their published equations; core and Mathlib definitions may reduce by
   `rfl`, `decide` or `show` but are never passed to `simp`, `rw` or `unfold`. Use the readers R0–R6
   and the route's §2 API (`BinArith.polyTimeComputable_iterate` and its `forLoop` and `getW`
   relatives, `exists_proj_decider`, the uniform simulator's `simulator_accepts`/`_rejects`,
   `FinTM.exists_comp_on_image`, `powCap`'s equations). Escalate (E-READER) rather than unfold.
3. **No new hosts.** Every scan is an application of the existing public iterator; no private
   enumeration machine, memo host or transition table. No new public declarations, files,
   `@[simp]` attributes, `sorry`, `admit` or axioms.
4. **Standards** (`policy.md`): docstrings cite [AB09, Theorem 3.3 and its proof] or library
   declarations; a `**Proof sketch.**` on every proof over 20 lines; no campaign labels in Lean text.
5. **Route risks to keep** (route §6): the simulator's time is polynomial in the **numeric**
   deadline; nested scans are charged inside the step's FP proof; a size bound must hold on **every**
   state reached, not only the final one; malformed states must not cause long loops or huge
   allocations; never assume `ladnerH` is monotone; a classical equation is not an FP
   implementation.
6. **Escalate** anything unprovable as stated (E-STATEMENT) or a missing host (E-HOST). A clean
   frontier with the leaves it completed is a valid delivery; prefer finishing the arithmetic,
   preparation and simulator leaves before the scan.

## Environment and verification

Follow the bundled fill-environment addendum (v2.6); **never run `lake build`**. Bootstrap the
import closure at the base into your own scratch olean tree. **At most 3 Lean processes may run at
once across the machine** (other fills share it): start at most one of your own at a time, and
check the machine-wide count first; record waits. Final checks, with exit codes:

- `Diagonalization/Ladner.lean` with zero errors; its only `sorry` warnings are its four admitted
  targets;
- `#print axioms` for `ladner_candidate_FP` (via a public wrapper in a scratch probe, not in the
  library) and the main leaves: at most `propext`, `Classical.choice`, `Quot.sound`;
- the facade `Diagonalization.lean` with zero errors.

## REPORT.md checklist

- [ ] What is complete (through `candidate_FP`, or a frontier); the base.
- [ ] Every new declaration with its role; every other-file definition reached and the equation used.
- [ ] Final check outputs, axiom prints, and `git diff --stat` touching only `Ladner.lean`.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `fill-ladner-poly-candidate.zip` with `REPORT.md`, the delivered `Ladner.lean`, the patch
against the base and the check logs. Push it, with any `fill-ladner-poly-candidate-checkpoint-N.zip`,
to `arora-barak-ch3-4/inbox/fill-ladner-poly-candidate/` on the exchange branch after
`git pull --rebase`, without force and touching nothing else; also attach the final zip in chat.
Do not push to any other branch or open a pull request.
