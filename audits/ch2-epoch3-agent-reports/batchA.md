# Chapter 2, epoch 3, batch A — partial continuation delivery

**INCOMPLETE: zero of the six public targets is fully closed.** The first
public target has 35 new, proved private components and one remaining local
admission for a native exponential split-search body. Its degree-zero case
is closed. Targets 2–6 remain untouched, respecting the brief's order.
The six-target no-`sorryAx` gate **does not pass**. This is a continuation
checkpoint under ground rule 6 of `briefs/ch2-epoch3-batchA.md`, not a
completed batch or a statement escalation.

## Repository and provenance

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested base branch: `complexity/arora-barak-ch1`.
- Required and actual source base: `b55180a8bb38b94427e75e63630aa6eab5fd6e95`.
- Working branch: `fill/ch2-e3-A`.
- Delivery commit: `6b521020358c97303f1dd550b10776de1df0ea25`.
- The brief was read before source work from the specified remote branch,
  whose cloned tip was `3293de776053bf755a89c16c5cfbcc7f7d3b8501`. The work
  branch was then created at the brief's required source base. No rebase,
  push, PR, or modification of another named branch occurred.
- Single-agent execution, without delegation.

## Target status

| Order | Target | Status and remaining work |
|---|---|---|
| 1 | `ntime_expPow_subset_NEXP` | **Partial.** Exact exponential certificate correspondence, split semantics, native binary evaluator, loop instantiation conditional on concrete body contracts, and timed loader/simulator composition are proved. One local `sorry` remains in the positive-degree search-body construction. |
| 2 | `NEXP_subset_iUnion_NTIME` | Original admission, byte-identical. The exponential emission scheduler and its integration with the existing B2 host have not been implemented. |
| 3 | `NEXP_eq_iUnion_NTIME` | Original admission, byte-identical. Not filled ahead of the two directions. |
| 4 | `EXP_eq_NEXP_of_P_eq_NP` | Original admission and audited sketch, byte-identical. Neither the nested-pair verifier with both exact checks nor the pad-emission/relocated-decider construction has been implemented. |
| 5 | `P_ne_NP_of_EXP_ne_NEXP` | Original admission, byte-identical. Not filled ahead of target 4. |
| 6 | `EXP_subset_NEXP` | Original admission; the entire `EXP.lean` file is byte-identical to the required base. No completed exponential padding verifier is claimed. |

The admission count is unchanged: five explicit `sorry` sites in
`Nondeterminism.lean`, one in `EXP.lean`, and 21 warnings in the complete
campaign sweep. **There are no admitted new private helpers.** The first
public theorem's single `sorry` moved from its whole proof to the exact
native-body existential below. The other five public admissions are
unmodified. Kernel traversal confirms each of the six targets is rooted
only in its own admission.

## Proved components and binding seams

| Obligation | Discharging declarations and precise limitation |
|---|---|
| Strict increase and unique exact-width split | `e3_split_strictMono`, `e3_split_unique`; coefficient zero and degree zero are included. |
| Finite search, exact equation, all-input failure | `e3Split`, `e3_split_spec`, `e3_split_none_iff`, `e3_split_complete`; `e3_split_empty` rejects the empty input for positive coefficient. These are semantic contracts, not a native split implementation. |
| Exact choice-word verifier and source-budget transfer | `e3ChoiceVerifier`, `e3_choice_append`, `e3_choice_no_split`, `e3_choice_budget`, `e3_choice_certificate`. The existing `acceptsWithin_iff_of_halts` uses all-branch halting for backward truncation; the certificate width is not enlarged. `e3_coefficient_pos` proves the zero-time case impossible. |
| Binary evaluation before validation | `e3_bits_shift` proves the exact little-endian representation for a positive coefficient; `e3_bits_length_bound` proves the polynomial bit bound from the candidate's input-length bound, without any padding-validity hypothesis. |
| Native binary evaluator | `e3ShiftTM`, `e3_shift_scan`, `e3_shift_computes`, `e3_shift_timed`, `e3_exp_bits_timed`. The catalog unary generator emits only the exponent's polynomial number of symbols; the scanner replaces them with zero bits and appends the fixed coefficient's bits. Coefficient zero uses the constant empty binary word. Timed composition gives a coefficient times degree `c+1`. |
| Loader, guarded input simulation, choice alignment and output | `e3_split_answer` reuses the unchanged `cont_pair_computes`, `cont_pair_empty`, and their already audited loader/core. It rejects the empty failure payload and handles every successful split. The core's guarded input, isolated tapes, exact choice alignment, halting-emission capture and singleton verdict remain those of the existing proof. |
| Complete verifier after a split emitter | `e3_split_length` bounds every emitted intermediate word by twice the original length plus two. `e3_verifier_of_split` carries the actual intermediate-length and timed phase contracts through `bufferedComp_start`/`bufferedSecondCfg_run`, adding thirteen copies of the positive polynomial envelope. Its split-emitter hypothesis is still uninstantiated in the positive-degree case. |
| Result-bearing loop and complete failed-search branch | `e3SplitStep`, `e3SplitAccept`, `e3_step_inv`, `e3_step_orbit`, `e3_find_congr`, `e3_find_eq`, `e3_loop_result`, `e3_loop_bound`, `e3_split_of_body`. The last lemma invokes `exists_loopFindTM`, uses `computesFunInTime_lengthBits` for fuel, and proves the first-success payload and exhaustion semantics. It explicitly requires native startup and positive first-return, scratch-restoring round contracts. |
| Small cases | `e3_split_degree_zero` is the catalog split with coefficient `2*C`, exponent zero; `e3_split_coefficient_zero` is the catalog's zero-width split. The former closes the first target's degree-zero branch. |
| Reverse-host seam | Not attempted in this continuation. Existing B2 and `cont_*` material is byte-identical. No guessing phase is presented as a decider, and no mathematical deadline is presented as a native clock. |
| Theorem-2.22 pad-validation seam | Not implemented. The binary evaluator and pre-validation bit estimate are reusable components only; they do not perform the two required exact checks, parsing, assembly, or captured verifier call. |

## Exact first-target frontier and continuation plan

Inside the sole remaining local admission of `ntime_expPow_subset_NEXP`,
the context contains a positive time coefficient, a nonzero degree, and
`Eval`, `B`, `hEval` from the proved `e3_exp_bits_timed`. That evaluator
computes the exact binary padding length in time
`B * (n + 1) ^ (c + 1)` on **every** input word of length `n`.

The remaining goal is to construct a finite deterministic `body`, an
`anchor`, and constants `A,r` with exactly these contracts:

1. **Startup:** from the genuine blank-tape initial configuration on `w`,
   reach `Cfg.ofWords anchor (stateWord body.k [])` within
   `A * (w.length + 1) ^ (r + 1)`; no earlier configuration has the anchor
   state.
2. **Round:** from `Cfg.ofWords anchor (stateWord body.k s)`, for every
   `s.length <= w.length + 1`, take a positive number of steps within the
   same input-length-only envelope and do not visit the anchor at a
   positive earlier time. If
   `s.length + a * 2 ^ (s.length + 1) ^ c = w.length`, halt with output
   exactly `pairEncode (w.take s.length) (w.drop s.length)`. Otherwise
   return exactly the canonical seam with candidate `e3SplitStep w s`.
   Every scratch tape, work head, input head, and output is covered by
   this full-configuration equality.

The source contains the complete Lean existential; it is deliberately not
weakened to a function-level computation. A continuation should proceed:

1. Handle the one-past-end candidate by a positive silent stall. For a
   live candidate, preserve the original input and state word, prepare the
   evaluator's virtual candidate input with blank source work tapes, and
   capture its binary output. Dispatch at actual completed source states.
2. Compute the remaining suffix length in binary on its actual prepared
   input, and compare the entire canonical binary words. Charge evaluation
   before any validity check. The candidate invariant permits length at
   most `w.length+1`, so the pre-validation envelope must absorb the
   corresponding `w.length+2` factor; do not use an unjustified logarithmic
   bound.
3. On success emit the exact threaded split of the preserved original
   input, with no leaked evaluator output. On failure restore all source
   and administrative scratch, append one true to the state word where
   permitted, restore the input head, and prove the exact canonical seam.
4. Prove the positive first-return property and the common polynomial
   envelope. The existing `e3_split_of_body` and `e3_verifier_of_split`
   then finish target 1 without further machine constructions.
5. Continue with target 2's exponential scheduler and B2 host, followed by
   targets 3–6 in the brief's order. Preserve all existing proofs.

The catalog's polynomial-width `splitSolve` instance cannot be supplied
for this positive-degree exponential equation. The loop engine has been
adapted, but its **body remains missing**. Neither the binary evaluator nor
the conditional loop lemma is claimed to supply that body.

Statement escalations: **none**. Requested shared lemmas: **none**. The
obstruction is unfinished native construction work, not evidence that a
frozen statement is false.

## All new declarations

All 35 declarations below are `private`, have proved bodies, and have empty
kernel admission roots. Definitions and their generated descendants are
included in the separate closure traversal.

- `e3_split_strictMono`
- `e3_split_unique`
- `e3Split`
- `e3_split_spec`
- `e3_split_none_iff`
- `e3_split_complete`
- `e3_split_empty`
- `e3ChoiceVerifier`
- `e3_choice_append`
- `e3_choice_no_split`
- `e3_choice_budget`
- `e3_choice_certificate`
- `e3_coefficient_pos`
- `e3_bits_shift`
- `e3_bits_length_bound`
- `e3ShiftTM`
- `e3_shift_scan`
- `e3_shift_computes`
- `e3_shift_timed`
- `e3_exp_bits_timed`
- `e3SplitWord`
- `e3_split_length`
- `e3_split_answer`
- `e3_verifier_of_split`
- `e3SplitStep`
- `e3SplitAccept`
- `e3_step_inv`
- `e3_step_orbit`
- `e3_find_congr`
- `e3_find_eq`
- `e3_loop_result`
- `e3_loop_bound`
- `e3_split_of_body`
- `e3_split_degree_zero`
- `e3_split_coefficient_zero`

## Source preservation and size

Only `TCSlib/Complexity/ClassNP/Nondeterminism.lean` changes in git: 561
insertions, two deletions (the former whole-target `sorry` and the target
comment's old closing line). The first target's docstring gains a clearly
marked append-only partial-fill appendix; its original content and its
entire theorem signature are preserved. The complete prefix containing all
previously proved material is byte-identical. The suffix beginning at
target 2 is byte-identical. No existing private was changed or removed.

- `Nondeterminism.lean`: 3,013 lines, 157,403 UTF-8 bytes;
  SHA-256 `deed194fd5abc2d7b10ad64306d952a669c860b278bb5f87f1a8558c14905c22`.
- `EXP.lean`: 2,534 lines, unchanged; included as an explicitly unchanged
  reference snapshot.
- The brief records size exceptions for both owned modules. The new
  private families stay in the owned file under its exclusive-ownership
  rule; no split or cross-file visibility change was attempted.
- `verify_surface.py` reproduces the exact prefix/suffix, public-signature,
  append-only docstring, helper-inventory, unchanged-EXP and changed-path
  checks against the required base. `surface-check.json` records the result.
- Style lint: **0 FAIL / 3 WARN**, all three recorded large-file warnings.

## Verification and environment

- Lean **4.25.0**, commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib **029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e**; all 11 installed
  dependency revisions match the committed manifest (`dependency-pins.json`).
- Required `lake exe cache get`: invoked once. It built the cache utility
  but **failed in its ProofWidgets cloud-release step** (`cache-get.log`).
  The underlying release-step failure was not diagnosed beyond its nonzero
  exit. This is not reported as a successful `cache get`.
- Recovery used the pin-matched existing compressed cache and the cache
  package's hash-directed unpacking API (`RecoverCache.lean` and
  `cache-recovery.log`). Unneeded generated artifacts were pruned locally
  to preserve disk space; no dependency source or pinned revision changed.
- The existing pinned toolchain was reused. Its process-location workaround
  redirects only its own `/proc/<pid>/exe` lookup to `/proc/self/exe` in
  this execution environment; it does not modify Lean or its kernel.
- No direct `lake build` was run. All TCSlib checking used the committed
  `lean_check_tree.sh` script. Intermediate failures while filling the new
  proofs were repaired before the final sweep.
- **Final full fresh sweep: 57/57**, 57 fresh nonempty oleans, exit **0**,
  **zero `error:` lines**, `FULL_SWEEP_COMPLETE`. The output tree was new
  and empty before the sweep. There are **21 expected admission warnings**,
  unchanged from the required source base.
- Owned-and-downstream sweep: pass (`downstream-final.log`).
- Axiom prints and checked-kernel traversal on the final fresh tree:
  exit **0**. **35 source helpers / 83 helper-and-generated declarations**
  have empty admission roots and axioms within
  `[propext, Classical.choice, Quot.sound]`.
- The five regression headlines (`ntime_poly_subset_NP`,
  `NP_subset_iUnion_NTIME`, `NP_eq_iUnion_NTIME`, `NP_subset_EXP`, and
  `mem_NP_iff_exists_length_le`) retain empty roots and the standard triple.
- **All six batch targets still print `sorryAx`**, each rooted only in its
  own declaration. `PARTIAL_CLOSURE_AUDIT_PASS` means the partial inventory
  and regression expectations passed; it does **not** mean the batch's
  completion gate passed.
- `git diff --check`, surface verification, git-bundle verification and
  detached patch replay pass. Replay produces the identical complete git
  tree `d22abd101f493db5a145bde5ae4eb3d63ad43577` and byte-identical source.

Final sweep tail:

```text
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

## Flat archive and integration

`fill-ch2-e3-A.zip` is flat: every member, including `SHA256SUMS`, is at
its root. It contains this report, the full modified source, the unchanged
EXP reference snapshot, one numbered `git format-patch`, an incremental
git bundle, final sweep and axiom logs, the axiom program, and verification
records and scripts. `SHA256SUMS` covers every other member; no oleans,
toolchain or dependency cache is included.

| Archive file | Repository path / purpose |
|---|---|
| `Nondeterminism.lean` | `TCSlib/Complexity/ClassNP/Nondeterminism.lean`, full modified source |
| `EXP.lean` | `TCSlib/Complexity/ClassNP/EXP.lean`, unchanged pinned reference |
| `0001-*.patch` | Apply with `git am` at the required source base; preserves Codex authorship |
| `fill-ch2-e3-A.bundle` | Alternative containing the same commit; requires the recorded base |
| `AxiomChecks.lean` | Run on the fresh tree with pinned package build paths in `LEAN_PATH` |
| `verify_surface.py` | Run with the repository path to reproduce the source-preservation checks |

Verify the extracted payload using `sha256sum -c SHA256SUMS`. Use the
repository's committed script and 57-module order for elaboration. The
archive's check-script copy is provenance; its relative-root convention
expects its original `scripts/` location when executed.

## Notation

`n` is a candidate or evaluator input length; `w` is the original verifier
input; `s` is the loop's current candidate state word. `a` (or generic `C`)
is the exact exponential-width coefficient; `c` is its degree. `Eval` and
`B` are the binary evaluator and its time coefficient. `body`, `anchor`,
`A`, and `r` are the missing round machine, return state, common time
coefficient and round-envelope degree parameter. All other code names
refer to declarations in the pinned source or this delivery.
