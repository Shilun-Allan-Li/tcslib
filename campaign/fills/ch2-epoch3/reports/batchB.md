# Epoch 3, Batch B — partial delivery

Date: 2026-10-05. Repository: https://github.com/Shilun-Allan-Li/tcslib.

**Partial delivery under brief ground rule 5.** Targets 1 and 2 are proved with
no admitted dependencies. Target 3 remains admitted at its original public
root. Its formula semantics, all-string reduction equivalence, size bounds,
and the machine initialization/maximum-variable pass are proved. The streaming
serializer correctness and time proof remain for continuation. The construction
budget was exhausted at that boundary; this is not a completion claim for all
three targets.

## Branch, base, scope, and delivery

- Required upstream branch: `complexity/arora-barak-ch1`; no `main` work.
- Required immutable base: `b55180a8bb38b94427e75e63630aa6eab5fd6e95`.
- Sole working branch: `fill/ch2-e3-B`.
- Delivery head: `d93ef0cb88c7e9758b0b6a0e309ef8c4ac90799a`.
- The brief was read from the requested upstream branch at
  `3293de776053bf755a89c16c5cfbcc7f7d3b8501`; the work branch was then created at
  the brief's required base. No rebase, push, or PR was performed.
- Commits, in order:
  1. `fdbb1dcd30e90ec4d55067fde04307ba42c14049` — guarded finite SAT/3SAT verifiers.
  2. `d93ef0cb88c7e9758b0b6a0e309ef8c4ac90799a` — clause-splitting semantics and
     the explicit machine continuation frontier.
- Only repository path changed: `TCSlib/Complexity/ClassNP/SAT.lean`.
  The full replacement appears as **`SAT.lean` at the archive root**.
- Final source: **2363 lines; 123206 bytes**.
  SHA-256: `a74dc1dd898c0ad8649d28e38b4625a035a2705689ba59aed4958d2dff0d0c8a`.
- The repository working tree is clean. Other branches and all out-of-scope
  source files are unchanged. A temporary detached verification worktree was
  used only to replay the patch series, then removed.
- `fill-ch2-e3-B.bundle` is an **incremental bundle requiring the exact base
  above**. It advertises only `refs/heads/fill/ch2-e3-B` and passed `git bundle
  verify`. It is not intended as a stand-alone clone without the base objects.

The archive is flat: every member, including `SHA256SUMS`, is at the root.
`SHA256SUMS` covers every other member and excludes itself. The two patches
apply in numeric order. Replay with `git am --committer-date-is-author-date`
from the required base reproduced the exact head hash, not only an equivalent
source tree; see `patch-replay.log`.

## Target status and admissions

| Frozen target | Status | Checked admission roots |
| --- | --- | --- |
| `Complexity.SAT_mem_NP` | Proved first, exact `(1,1)` certificate parameters | `[]` |
| `Complexity.SAT3_mem_NP` | Proved second, exact `(1,1)` certificate parameters | `[]` |
| `Complexity.SAT_reducible_SAT3` | **Admitted; original `by sorry` body retained** | `[Complexity.SAT_reducible_SAT3]` |

The owned file has exactly **one** admission, the third target at line 2360.
There are no admitted private helpers, new axioms, weakened statements, or
sanctioned admitted dependencies. Neither completed membership uses the
remaining reduction admission.

## Verifier obligations and their proofs

| Obligation | Discharging declarations and behavior |
| --- | --- |
| Exactly `n+1` certificate bits | `satAssignment`, `sat_certificate`, `sat_verifier_equiv`, `sat3_verifier_equiv`; use `CNF.numVars_decode_le` and `eval_congr_of_lt_numVars` |
| Unique odd split, including total length one | `sat_split_some`, `sat_split_exists`, `satVerdict_append`; actual machine uses `computesFunInTime_splitSolve 1 1` |
| **Explicit even-length rejection** | `sat_split_even` proves split failure on every even total length; `satVerdict` and both polynomial verifier constructions reject that failure branch |
| Exact complete syntax check | `sat_takeTrues_repr`, `sat_parseLit_repr`, `sat_parseClause_repr`, `sat_parseClauses_repr`, `sat_parse_repr`, and the `satSyntaxSuffix_*` invariant |
| Parser realized by a finite machine | `satSyntaxStep`, `satScanTM`, `satScan_computes`, `satSyntax_spec`, `satSyntax_poly` |
| Parse failure accepts the fallback | `satSafe_spec`, `satVerdict_false_poly`, `satVerdict_true_poly`; malformed instances decode to the satisfiable empty formula |
| Unary assignment walks | `satEval_index`, `satEval_literal`, `satEval_clause`, `satEval_formula`; each literal of index `v` takes `3*v+8` transitions in the doubled input representation |
| Capture and output isolation | `sat_first_halt`, `satEval_start`; catalog capture includes a final halting emission, then native and certificate heads rewind |
| Buffered final verdict | Evaluation accumulates clause/formula Booleans in finite control and emits only at the final formula terminator; conditional/composition wrappers capture intermediate outputs |
| Width pass for 3SAT | `satWidthStep` counts occurrences with a saturated finite counter; `satWidthScan_serialize`, `satWidthScan_poly`, `satVerdict_true_poly` |
| Polynomial-time composition | `sat_pipeline_poly`, `satSafeValue_poly`, `sat_comp_on_image`, `sat_pt_cond`, `satVerifier_of_poly` |

**Complete syntax comes first.** The six-state grammar machine distinguishes
formula markers, clause markers, unary indices, polarity, exact end, and error.
Any trailing bit after the formula terminator enters the error state. Clause
and formula zero terminators are accepted even at zero parser fuel; successful
parse reconstruction and `parse_serialize` connect this machine to the frozen
parser on every string. No failed clause or excessive width may reject an
incompletely parsed prefix. In particular the malformed prefix/trailing-data
case `[true,false,false,true]` follows the accepting fallback branch. The 3SAT
width machine runs only after full syntax success; evaluation runs only after
width success. Length-zero instances have a one-bit certificate and are
covered by the same proof.

Both syntax and width scanners use zero work tapes and run in exactly `m+1`
steps on an `m`-bit scanner input. The uniform evaluation contract is linear
in its safe paired-input length. The audited `(1,1)` split catalog contract
uses a cubic bound. The full verifiers obtain actual finite-machine polynomial
witnesses through the audited wrappers; no appeal to informal algorithmic
complexity or output length substitutes for a machine proof.

## Reduction work proved so far

The private transform is exactly the requested construction:
`head :: b :: c :: d :: rest` produces `[head,b,(n,true)]`, then recurses on
`(n,false) :: c :: d :: rest` at cursor `n+1`. Clauses of width at most three,
including the empty clause, pass through. The whole-formula transform starts
at `φ.numVars` and threads the cursor between clauses.

| Mathematical obligation | Discharging declarations |
| --- | --- |
| Monotone fresh cursor and width at most three | `satChain_cursor`, `satChain_width`, `satSplitClause_cursor`, `satSplitClause_width`, `satTransformFrom_width` |
| Soundness: transformed satisfying assignment satisfies the original clause/formula | `satChain_sound`, `satSplitClause_sound`, `satTransformFrom_sound` |
| Completeness: extend assignments without changing smaller indices | `satChain_extend_step`, `satChain_complete`, `satSplitClause_complete`, `satTransformFrom_complete` |
| Fresh-variable preservation | `satChain_vars`, `satSplitClause_vars`, `sat_numVars_le`; whole-formula preservation uses the existing `eval_congr_of_lt_numVars` |
| Equisatisfiability | `satTransform_equisat` |
| String reduction is `serialize ∘ transform ∘ decode` | `satReduction` |
| Correctness for **every string** | `satReduction_correct`, with no well-formedness premise |
| Fallback fixed by transform | `satReduction_fallback`; failed parsing maps to `CNF.serialize []` |
| Cursor, clause-count, and serialization growth | `satChain_sizes`, `satSplitClause_sizes`, `satTransformFrom_bounds`, `sat_clause_serial_bound`, `sat_serial_bound` |
| All-input output-size bound | `satReduction_size`: at most `6*|x|^2 + 8*|x| + 1` bits |

Completeness assigns the new fresh variable the truth value of the remaining
tail clause. The first emitted link and the recursively transformed clause
beginning with the negated fresh variable are then true. Each extension
preserves all smaller indices, which keeps earlier chains true when later
clauses allocate more variables. Soundness follows the converse link
induction. The serialized output bound is explicitly a **size bound**, not a
polynomial-time computation theorem.

## Exact machine continuation frontier

`satRedTM` defines a **candidate** two-work-tape, 35-state transducer. Its
unproved streaming states are documented as a candidate, not a completed
reduction witness. All definitions and proved support lemmas are axiom-clean.

The first tape is a contiguous unary fresh-variable counter. The second tape
is a temporary literal buffer with a permanent marker at position -1.
The following machine stages are fully proved:

- `satRed_init`: two silent transitions install the buffer marker.
- `satRedCounter_write`, `satRed_maxOnes`: the counter records the maximum
  unary literal length encountered, without losing a larger earlier maximum.
- `satRed_maxLiteral`: the literal pass costs `2*v+5` transitions and restores
  the counter head to zero.
- `satRed_maxClause`, `satRed_maxFormula`: the complete maximum pass is
  silent and costs at most twice the serialized input length.
- `satRed_start`: initialization, maximum pass, and audited native rewind
  reach state 9 with the native input and both work heads at their starting
  positions, empty output, an empty marked buffer, and **exactly `φ.numVars`**
  on the counter tape, in at most `3*|serialize φ|+5` transitions.

The proposed streaming states have these roles:

| States | Role | Proof status |
| --- | --- | --- |
| 9–16 | Formula/clause markers and copying the first two literals | Transition definition only |
| 17–21 | Buffer the prospective third literal and inspect whether another follows | Transition definition only |
| 22–32 | Emit positive fresh literal, close/open clauses, emit its negation, increment/rewind counter | Transition definition only |
| 33–34 | Replay/erase the buffered literal and restore its head | Transition definition only |

**Next obligations:**

1. Prove the streaming literal-buffer, fresh-variable emission, and replay
   invariants. Then induct over clauses/chains to show that the output is
   exactly `CNF.serialize (satTransform φ)`, including empty clauses/formulas.
2. Establish a uniform polynomial transition bound for those streaming states,
   then compose it with `satRed_start`. The existing output-size bound alone
   is insufficient.
3. Guard the core on **all strings** using the existing complete syntax pass.
   One suitable route is a polynomial canonicalizer
   `x ↦ if satSyntax x then x else CNF.serialize []`; parse reconstruction
   identifies its output with `serialize (decode x)`. Compose on this safe
   image using `sat_comp_on_image`, measuring its bound at the original
   input length. Finally prove `PolyTimeComputable satReduction` and combine
   it with `satReduction_correct` to fill the frozen public reduction target.

There is no new placeholder admission for these obligations: the sole owned
`sorry` remains the original public target. No statement obstruction was
encountered; continuation is a proof-construction task.

## Verification and environment

- Pinned Lean **4.25.0**, commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Pinned mathlib **`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**.
- Setup command `lake exe cache get` was attempted once. It checked out the
  pinned dependencies but failed fetching the ProofWidgets cloud release.
  Existing official cache archives were then unpacked with `lake exe cache
  unpack` (7506 files). Both setup logs are included. No dependency sources
  or repository build configuration were edited. `lake build` was never run.
- The available pinned toolchain was used from
  `/tmp/ch2-b2-toolchain/lean-4.25.0-linux/bin`. This host's PID namespace
  required a pre-existing `readlink` shim, supplied as `proc-self.c`: it maps
  only the current process's `/proc/<pid>/exe` lookup to `/proc/self/exe`.
  It does not modify the Lean kernel or proof checks. The shim was active
  through `LD_PRELOAD=/tmp/ch2-b2-toolchain/proc-self.so`.
- Bootstrap and iteration used `scripts/lean_check_tree.sh` and the committed
  57-module order. The **final sweep used a previously nonexistent olean
  directory**, and checked all 57 modules from scratch through that script.
- Final result: **57/57 passed; 0 `error:` lines; 19 admission warnings**,
  comprising the one documented owned admission and 18 unchanged out-of-scope
  declarations. The source had 21 campaign admissions before these two fills.
- `style_lint.py TCSlib/Complexity/ClassNP`: **0 FAIL, 4 WARN**. The SAT warning
  is its 2363-line size. Positive reason for keeping the file together:
  exclusive ownership permits only this file and requires private helpers;
  splitting into shared modules would exceed the batch's authority. The
  other three size warnings concern unchanged files. Lean also reports
  nonfatal tactic/simp linter warnings; no linter options were suppressed.
- `git diff --check` passed.
- `check-freeze.py` verifies the unchanged ordered five public declarations,
  both language definition bodies, every original comment/docstring, the
  copyright, and the option headers. Only the two precise imports
  `Mathlib.Tactic.FinCases` and `Mathlib.Data.List.MinMax` were added.
- `Ch2E3BAxioms.lean`, adapted from the committed closure template, traverses
  checked kernel declarations through types, opaque values, and constructors.
  It checks all three targets, **all 373 private/generated declarations**, and
  17 previously closed regressions. It ran against the final fresh oleans.

Headline axiom prints:

```text
SAT_mem_NP: [propext, Classical.choice, Quot.sound]
SAT3_mem_NP: [propext, Classical.choice, Quot.sound]
SAT_reducible_SAT3: [propext, sorryAx, Classical.choice, Quot.sound]
```

Both completed headline roots are empty. The union of all private/generated
closure roots is empty and its axiom set is the standard triple. The remaining
public reduction has only itself as an admission root. The audit explicitly
expects this partial-delivery exception and does not claim the all-three-target
completion gate has passed.

Final sweep tail:

```text
BEGIN 55/57 TCSlib/Complexity/Formulas
PASS 55/57 TCSlib/Complexity/Formulas
BEGIN 56/57 TCSlib/Complexity/CookLevin
PASS 56/57 TCSlib/Complexity/CookLevin
BEGIN 57/57 TCSlib/Complexity/ClassNP
PASS 57/57 TCSlib/Complexity/ClassNP
FINAL_SWEEP_PASS 57/57; elapsed_seconds=199.0
ERROR_LINES 0
ADMISSION_WARNINGS 19
```

For reproduction, apply the patches to the required base, provide the pinned
cache/toolchain, choose a fresh `TCSLIB_OLEANS`, and run the committed checker
in `scripts/ab_ch1_module_order.txt` order, exiting on any failed module. Run
`Ch2E3BAxioms.lean` with that fresh olean directory first in `LEAN_PATH`, followed
by the repository and package build-library paths. Run `python check-freeze.py
/path/to/tcslib` for the source freeze check.

## Complete final admission inventory

Only the SAT reduction row is owned by this batch. All other rows are unchanged.
The table records declarations emitting admission warnings, not every theorem
that transitively depends on an admission.

| Repository path | Line | Declaration |
| --- | ---: | --- |
| `TCSlib/Complexity/ClassNP/EXP.lean` | 2531 | `EXP_subset_NEXP` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2377 | `ntime_expPow_subset_NEXP` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2398 | `NEXP_subset_iUnion_NTIME` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2409 | `NEXP_eq_iUnion_NTIME` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2445 | `EXP_eq_NEXP_of_P_eq_NP` |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2451 | `P_ne_NP_of_EXP_ne_NEXP` |
| `TCSlib/Complexity/ClassNP/SAT.lean` | 2360 | `SAT_reducible_SAT3` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 176 | `oblivious_schedule_eq` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 192 | `snapshotAt_zero` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 204 | `snapshotAt_state_succ` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 217 | `snapshotAt_inputSymbol` |
| `TCSlib/Complexity/CookLevin/Snapshot.lean` | 244 | `snapshotAt_workSymbol` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 82 | `NPHard.polyTimeReducible` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 212 | `SAT_NPHard` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 219 | `SAT_NPComplete` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 228 | `SAT3_NPHard` |
| `TCSlib/Complexity/CookLevin/Hardness.lean` | 234 | `SAT3_NPComplete` |
| `TCSlib/Complexity/ClassNP/Tautology.lean` | 110 | `TAUTOLOGY_mem_coNP` |
| `TCSlib/Complexity/ClassNP/Tautology.lean` | 130 | `TAUTOLOGY_coNPComplete` |

## New declaration inventory

There are **135 new source declarations**, all `private`, all in namespace
`Complexity`. There are no new public declarations. Every name is listed
below and in `PRIVATE_DECLARATIONS.txt`. `KERNEL_DECLARATIONS.txt` lists all
**373** private source/generated kernel names; the same exhaustive inventory
and its axiom closure result appear in `axiom-print.log`.

```text
satAssignment
sat_certificate
sat_split_some
sat_split_exists
sat_split_even
satWidth
satWidth_spec
satVerdict
satVerifier
satVerdict_append
sat_verifier_equiv
sat3_verifier_equiv
sat_takeTrues_repr
sat_parseLit_repr
sat_parseClause_repr
sat_parseClauses_repr
sat_parse_repr
satSyntaxStep
satSyntaxSuffix
satSyntaxSuffix_cons
satSyntaxSuffix_nil
satSyntaxSuffix_run
satSyntax
satSyntax_spec
satScanTM
satScanCfg
satScan_step
satScan_run
satScan_computes
satSyntax_poly
SatEvalControl
satEvalQ
satEvalAction
satEvalTM
satEvalCfg
satEvalCfg_input
satEvalCfg_work
satEvalAction_apply
satEval_skip
satEval_double
satEval_rewind
satBits
satBits_length
satEval_index
satEval_literal
satEval_clause
satEval_formula
sat_first_halt
satEval_start
satEval_computes
sat_comp_on_image
sat_pt_linear
sat_pt_const
sat_pt_cond
sat_pt_and
satSplit
satInstance
satWitness
satSplitValid
satGood
satSafe
satSafeValue
sat_literal_lt_numVars
satSafe_spec
sat_pipeline_poly
satSafeValue_poly
satVerdict_false_poly
satVerifier_of_poly
satWidthCap
satWidthStep
satWidth_index
satWidth_literal
satWidth_clause
satWidth_formula
satWidthScan
satWidthScan_serialize
satWidthScan_poly
satVerdict_true_poly
satClause_congr
satChain
satSplitClause
satChain_cursor
satChain_width
satChain_sound
satChain_extend_step
satChain_complete
satChain_vars
satSplitClause_cursor
satSplitClause_width
satSplitClause_vars
satSplitClause_sound
satSplitClause_complete
satTransformFrom
sat_numVars_le
satTransformFrom_width
satTransformFrom_sound
satTransformFrom_complete
satTransform
satTransform_equisat
satReduction
satReduction_correct
satReduction_fallback
satChain_sizes
satSplitClause_sizes
satMeasure
satTransformFrom_bounds
sat_clause_measure
sat_measure_serialize
sat_measure_decode
sat_clause_serial_bound
sat_serial_bound
satReduction_size
satRedAction
satRedTM
satRedCounter
satRedBuffer
satRedCfg
satRedCfg_input
satRedCounter_read
satRedCounter_left
satRedCounter_write
satRedAction_apply
satRed_move
satRed_one
satRed_counterBack
satRed_maxOnes
satRed_maxLiteral
sat_foldMax_append
satClauseVars
sat_numVars_cons
satRed_maxClause
satRed_maxFormula
satRedBuffer_empty
satRed_init
satRed_start
```

## Requested shared lemmas and escalations

**None.** No frozen statement or docstring was changed, and no unprovability
obstruction was discovered. The private construction utilities remain local
as required. The sole outstanding item is the precisely described machine
proof continuation for target 3.
