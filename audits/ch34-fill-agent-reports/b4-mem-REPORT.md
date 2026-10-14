# B4 membership fill — partial delivery

## Result and frozen base

**0/1 target completed.** `Complexity.TQBF_mem_PSPACE` remains its original
`sorry`. It is not proved modulo the new helpers. All 29 new explicit helper theorems are closed without admissions, as verified
by the final imported-module axiom audit. Final verification is recorded below.
The unfinished items are machine constructions and their representation/resource
proofs, not extra admitted declarations.
This is the continuation delivery allowed by brief ground rule 9.

- Repository: [tcslib](https://github.com/Shilun-Allan-Li/tcslib)
- Requested base branch: `complexity/arora-barak-ch3-4`.
- Base commit: `3462c1b49a49d2cd458f595624c1dbac1f868af3`.
- Working branch: `fill/ch34-b4-mem`, created directly from that base; no rebase,
  push or PR. No other branch was changed.
- `git merge-base --is-ancestor 13957bf73eb37763259be1fd01a5cca9bd03c21f HEAD`
  succeeded before branch creation and was rechecked during delivery.
- Only `TCSlib/Complexity/ClassPSPACE/TQBF.lean` is modified. The new declarations
  form one private block immediately after `def TQBF`; the only other change is
  the flagged Fill appendix in the target docstring. Imports, all original
  declarations, the target statement and body, B4a, hardness and completeness
  are unchanged.
- The two completion-only status changes were deliberately **not made**:
  the module still says three statements remain sorried and the target still
  says “spec, fill pending”. Changing either would misstate this partial.

## Addendum 1 and point of receipt

Received Addendum 1 at **2026-10-12 14:12:55 America/New_York
(18:12:55 UTC)**. At that point, the syntax validator and its framed input-fold
facts had been checked; the record transducer, rank progress and termination
had been checked; and the first CNF-specific pure semantic proof was undergoing
a component check. No machine wrapper or streaming CNF evaluator had been built.

The pure semantic proof was then generalized over an arbitrary Boolean leaf.
`b4mValue`, the invariant, carry correctness and walker correctness do not
mention QBF or CNF. `b4mValue_truth` and `b4mWalk_truth` give the separate CNF
instance. A hypothesis-carrying machine parameter, `b4mLeafModule`, explicitly
requires the framed leaf contract `b4mLeafFramed`.

**Addendum frontier:** the generic *machine* host and its combined time/space
contract are not yet constructed. The addendum's optional leaf-specific fallback
was not taken; this delivery supplies a generic pure core and a typed leaf
interface, but does not claim the machine form is finished. No cost-based
exception or statement change is requested. The §14 reference in the promotion
flag is the reference supplied by the addendum; that section is not present at
the frozen base and was not treated as a proved library row.

## What is proved

1. The finite automaton accepts precisely successful pair decoding followed by
   exact CNF parsing. It consumes the full native input, so A13's trailing garbage
   cannot inherit a false prefix verdict. Both rejection paths select the true
   fallback. Accepted inputs have an exact pair/serialization representation.
2. The validator uses the public `inputFoldTM` contract and never moves a work
   head; its work-space bound is the number of work tapes, including origins.
3. Each record consists of `(branch bit, node-kind bit)` in two adjacent Boolean
   cells, physically root first. Kind `false` is AND/universal; kind `true` is
   OR/existential. Proof-side carry lists are innermost first. The backward scan
   reads kind before branch. On a neutral first branch it sets the branch bit
   and stops; otherwise it resets the bit and carries the verdict outward.
4. The record transducer computes exactly this carry, preserves node kinds and
   length, and has the public scan realization. A nonterminal carry strictly
   increases the branch rank; the pure walker terminates within the full Boolean
   assignment budget. The empty tree takes one leaf round.
5. The neutral-first-branch invariant proves the generic short-circuit AND/OR
   semantics. The QBF connection and the free-variable base convention are
   separate lemmas. No per-level matrix or formula copies are used.
6. The all-true word of paired-input length has more than enough numerical fuel.
   This lemma uses public digit arithmetic, not the private B2b exact-value proof.

## Exact continuation frontier

No new private helper remains `sorry`. The only owned admission is the original
`TQBF_mem_PSPACE` body, whose original proof sketch remains intact.

Continue with these obligations, in this order:

1. Build the generic Boolean AND/OR machine host parameterized by
   `b4mLeafModule`. Compose a leaf call, the public odometer scan, a constant-size
   verdict flag and the return/escape dispatch. Use `phaseHostTM`/seams and R1
   embedding, with a distinct body anchor; carry all cross-round data on tape.
   Relate its rounds to `b4mWalk`, then use `counterLoopTM_run_escape`, the rank
   theorem and the fuel theorem. Do not reprove a loop, scan or seam trace.
2. Construct the public-row literal-lookup idiom and the streaming CNF leaf
   instance. Count/consume unary literal indices with public counter loops;
   reuse fixed banks; return false for indices beyond the assignment prefix.
   Prove that a bounded-index record read agrees with `b4mAssigned`, and use
   `b4mAssigned_free` beyond the prefix. Read clauses from the native input,
   restore the record word and all work
   heads, blank every scratch tape, and return the input head to a fixed home.
   Prove every clause of `b4mLeafFramed`, including silence during the run.
3. Initialize records and fuel from the validated native input using input copy,
   public scans and `writeAdvTM`/counter rounds. Handle zero prefix uniformly.
4. Assemble validation, rejection, initialization, walking and one-bit answer
   phases using the public phase/seam and emission contracts. No output occurs
   before the final answer phase.
5. Compose trajectory envelopes, count visited cells on every tape using
   `MultiTapeTM.spaceUsedByTape_le_card_Icc`, prove a concrete constant times
   `n + 1`, and package the decider in `SPACE (fun n => n + 1)`. Finish with
   `SPACE.mono` and `space_poly_subset_PSPACE 1`.

**Additional shared-lemma requests: none. Escalations: none.** The promotion
candidates requested by Addendum 1 are listed separately below. The specialized
record-word proof avoids both private generic `mealyRun` lemmas.

No cited public statement was found unprovable or unusable as stated. There is
**no mathematical escalation** and no request to weaken a statement. The missing
construction and its ledger must not be mistaken for a completed membership proof.

## Space and time ledger

The following entries distinguish proved local facts from unfinished composition.
Here `m` is the number of records and `n` the input length.

| Phase/bank | Head interval relative to entry | Status |
|---|---|---|
| Validation, every work tape | `[0, 0]` | Proved; total at most `k` visited cells on `k` tapes. |
| Odometer, record tape | `[-1, 2m]` | Public scan interval; specialized envelope at most `2m + 1`; exactly `4m + 2` steps. |
| Odometer, every other work tape | `[0, 0]` | Proved from the same public scan contract. |
| Leaf record/scratch banks | `[-radius x m, radius x m]` | A required hypothesis in `b4mLeafFramed`, not yet discharged for CNF. |
| Counter fuel | `[-1, length w]` | Available from the public counter-loop contract; not yet composed with this walker. |
| Initialization, flags and final answer | Unfinished | No global trajectory proof yet. |

The generic machine time should be bounded by the number of executed rounds
multiplied by the leaf's time plus `4m + 2` for the record scan and fixed dispatch
costs, plus `counterOverhead` for those rounds. Its space must be bounded by a
constant times the record length, plus the leaf's framed space and fixed flag/
origin costs, independently of the number of rounds. A fuel word with length
linear in the record count suffices for the generic host; the TQBF instance may
use the brief's input-length fuel and charge it to its linear input-sized banks.
These are continuation obligations, **not proved global estimates**. In
particular, **no final constant `c'` is claimed**. Empty-input origins must still
be counted in the final packaging.

## Promotion candidates

The pure generic evaluator (`b4mValue`, the carry/record family, and
`b4mWalk_value`) and the framed leaf parameter are private promotion candidates
for **host H1, AND/OR evaluator; machine-library-design.md §14**, per Addendum 1.
They do not depend on the CNF instance. Promotion of the machine host must wait
for the unfinished construction and resource contract.

### Generic contracts, verbatim

```lean
private theorem b4mWalk_value (leaf : (ℕ → Bool) → Bool) (qs : List Bool) :
    ∃ v, b4mWalk (b4mLeaf leaf) (2 ^ qs.length)
        (qs.map (fun q => (false, q))).reverse = some v ∧
      (b4mValue leaf qs (fun _ => false) 0 = v)
```

```lean
private def b4mLeafFramed {k : ℕ} {S : Type} (M : MultiTapeTM (k + 1) Bool S)
    (entry : S) (exit : Bool → S) (leaf : List Bool → (ℕ → Bool) → Bool)
    (home : List Bool → ℕ) (time radius : List Bool → ℕ → ℕ) : Prop :=
  ∀ (x : List Bool) (rs : List (Bool × Bool)) (d : Cfg (k + 1) Bool S x),
    d.state = some entry → d.inputPos.val = home x →
    (∀ p : ℤ, -1 ≤ p → p ≤ ((b4mRecordWord rs).length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (b4mRecordWord rs) p) →
    (∀ j : Fin k, ∀ p, d.workTapes j.succ p = none) →
    ∃ t ≤ time x rs.length,
      (∀ u < t, ∀ v, (M.runFrom d u).state ≠ some (exit v)) ∧
      (∀ u ≤ t, ∀ j, |(M.runFrom d u).workTapePos j - d.workTapePos j| ≤
        (radius x rs.length : ℤ)) ∧
      (∀ u ≤ t, (M.runFrom d u).output = d.output) ∧
      (M.runFrom d t).state = some (exit (b4mLeaf (leaf x) rs)) ∧
      (M.runFrom d t).inputPos.val = home x ∧
      (M.runFrom d t).workTapes = d.workTapes ∧
      (M.runFrom d t).workTapePos = d.workTapePos
```

```lean
private structure b4mLeafModule (k : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (leaf : List Bool → (ℕ → Bool) → Bool) where
  machine : MultiTapeTM (k + 1) Bool S
  entry : S
  exit : Bool → S
  exit_injective : Function.Injective exit
  home : List Bool → ℕ
  home_bound : ∀ x, home x ≤ x.length + 1
  time : List Bool → ℕ → ℕ
  radius : List Bool → ℕ → ℕ
  framed : b4mLeafFramed machine entry exit leaf home time radius
```

The main theorem above is deliberately identified as the **pure** contract.
`b4mLeafFramed` is a hypothesis on a supplied machine, and `b4mLeafModule` bundles
that hypothesis with the machine; neither asserts the existence of a CNF leaf
machine or of the composed evaluator host.

### CNF instance obligations

`leaf x` must evaluate the validated matrix using the assignment represented by
the unchanged record word and the all-false base. The instance must supply a
finite Boolean-work-tape machine, entry and distinguishable verdict exits, a
fixed valid native-input home, a uniform time bound, and the absolute head
bounds in `b4mLeafFramed`. It must restore all work tapes and heads, leave every
scratch tape blank, preserve output throughout, and return the input head home.
The pure bridge is already isolated in `b4mValue_truth`/`b4mWalk_truth`; the
streaming machine and framed proof are unfinished.

### Non-Bool digit generalization, not built

For Savitch-style digits, replace the branch bit with a fixed record walked by
first/next rows. The invariant must say that every previously visited child was
neutral, not only the first Boolean child. The carry must distinguish “next
child” from exhaustion, and the rank/round bound becomes the ordered digit-domain
product instead of the binary rank and `2^m`. The assignment representation,
leaf frame, record widths and scan resource bounds must use those digit records.
The AND/OR node-kind bit and short-circuiting principle remain. This delivery
builds none of that generalization and introduces no public declaration.

## New declarations

| Private declaration | Kind | Role |
|---|---|---|
| `b4mSyntaxState` | abbrev | Finite pair/grammar control state. |
| `b4mSyntaxStep` | def | Aligned-pair stage feeding the public CNF grammar. |
| `b4mValid` | def | Full-input syntax verdict. |
| `b4mSyntax_matrix` | theorem | Matrix-stage fold equals the public grammar fold. |
| `b4mValid_spec` | theorem | Exact acceptance characterization through the two decoders. |
| `b4mTruth_empty` | theorem | Empty matrix is true under every quantifier prefix. |
| `b4mReject_mem` | theorem | Both syntax failures imply membership via true fallbacks. |
| `b4mValid_repr` | theorem | Successful validation reconstructs exact serialized input. |
| `b4mValidation_reject` | theorem | Public input-fold rejection has fallback semantics. |
| `b4mValidation_space` | theorem | Validation costs at most one origin cell per work tape. |
| `b4mCarryState` | abbrev | Finite state for stopped, carrying and pending-kind cases. |
| `b4mBack` | def | Backward two-cell record transducer. |
| `b4mCarryRecords` | def | Logical innermost-first short-circuit carry. |
| `b4mRecordWord` | def | Physical root-first two-cell word. |
| `b4mBack_run` | theorem | Mealy execution equals logical carry. |
| `b4mCarryRecords_quants` | theorem | Carry preserves node-kind sequence. |
| `b4mRecordWord_length` | theorem | Two cells per record. |
| `b4mScan_result` | theorem | Public two-pass scan result equals the record carry. |
| `b4mOdometer_envelope` | theorem | Public scan gives record-head and other-head envelopes. |
| `b4mCarryRecords_length` | theorem | Carry preserves record count. |
| `b4mRank` | def | Proof-only binary branch rank. |
| `b4mRank_lt` | theorem | Rank is below the full assignment count. |
| `b4mRank_progress` | theorem | Every nonterminal carry strictly advances rank. |
| `b4mWalk` | def | Fuel-bounded mathematical leaf/carry rounds. |
| `b4mWalk_terminates` | theorem | Any leaf function terminates within the remaining assignment budget. |
| `b4mValue` | def | Generic short-circuit Boolean AND/OR value. |
| `b4mValue_close` | theorem | The carry-closing rule has the generic node semantics. |
| `b4mCarryRecords_done` | theorem | Overflow preserves verdict and resets inner branches. |
| `b4mCarryRecords_outer` | theorem | An outer record composes after its inner suffix. |
| `b4mAssigned` | def | Assignment represented by a root-first record list. |
| `b4mAssigned_free` | theorem | Unmentioned indices retain the base assignment. |
| `b4mLegal` | def | Neutral-earlier-child invariant, generic in the leaf. |
| `b4mLegal_reset` | theorem | All-first-branch records satisfy the invariant. |
| `b4mAdvance` | def | Proof-side root-first view of the same carry. |
| `b4mAdvance_quants` | theorem | Root-first carry preserves node kinds. |
| `b4mAdvance_cons` | theorem | Recursive decomposition at the outermost node. |
| `b4mAdvance_correct` | theorem | One round preserves the invariant or returns the generic value. |
| `b4mLeaf` | def | Apply an arbitrary leaf to the represented complete assignment. |
| `b4mWalk_correct` | theorem | Any returned verdict equals the generic tree value. |
| `b4mWalk_value` | theorem | Initialized generic walk returns that value within the round bound. |
| `b4mLeafFramed` | def | Required leaf-machine timing, envelope, silence and restoration contract. |
| `b4mLeafModule` | structure | Hypothesis-carrying finite-state machine parameter. |
| `b4mValue_truth` | theorem | CNF value instance agrees with QBF.truthAux. |
| `b4mWalk_truth` | theorem | Specialize the generic walker to CNF semantics. |
| `b4mFuel_sufficient` | theorem | Input-length all-true fuel exceeds the assignment budget. |

## Duplication governance

The original committed screen was run before edits over the exact population in
`audits/evidence/fills-5/ch34-b4-mem-screen-population.txt`. Its complete output
matches the committed screen base byte for byte:

```text
declarations screened: 1472; copy pairs (target reproduces >= half of source): 871; reproduced text: 297,548 chars
```

The final run of the same original script and population is recorded below.
An additional owned-block-only diagnostic used the original extraction and
comparison functions to identify potential new pairs before the full final run;
it does not replace that full screen.

```text
declarations screened: 1508; copy pairs (target reproduces >= half of source): 873; reproduced text: 297,817 chars
```

All 871 baseline pairs remain unchanged. The 36 eligible new bodies contribute
exactly two new in-file pairs (269 reproduced characters), and **no new cross-file
pair**:

| New in-file match | Screen measure | Justification |
|---|---|---|
| `b4mRank_progress` reproduces `b4mCarryRecords_done` | 178/287 = 62% | The same carry case split and recursive projection rewrite support different conclusions: rank growth versus verdict preservation/reset. |
| `b4mBack_run` reproduces `b4mCarryRecords_quants` | 91/171 = 53% | Both split the record's Boolean cases; one proves transducer execution and the other node-kind preservation. |

Neither pair reaches the 90% factoring threshold. No private SAT parser,
streaming evaluator, B2b host/ledger, input-seek table, or generic private Mealy
lemma was copied. **new copies: none**.

The complete original before/after stdout is quoted verbatim in the appendices
and also supplied as separate log files.


## Verification

The required 73-module bootstrap is run in the committed order with
`scripts/lean_check_tree.sh`. No `lake build` was used. The Lean toolchain is
v4.25.0 and mathlib remains pinned at
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. A runtime-only `readlink` compatibility
shim corrected this environment's executable-path lookup (`/proc/<pid>/exe` to
`/proc/self/exe`); it does not change the kernel, proof checking, sources or the
check script. Dependencies were restored using `lake exe cache get`.

The base admission set, by declaration, is unchanged:

- `Constructible`: `spaceConstructible_logSpace`, `spaceConstructible_linear`.
- `ConfigGraph`: `NSPACE_subset_exp_dtime`, `NL_subset_P`, `polyTimeReducible_of_mem_NL`.
- `TQBF`: `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`.

The unrelated parallel fills were not imported into the frozen base. This
partial retains all eight base admissions and adds none. The final target axiom
print contains `sorryAx`, so the complete-delivery axiom gate is
**not satisfied**; the new helper audit separately rejects every axiom outside
`propext`, `Classical.choice`, and `Quot.sound`.

| Check | Result | Evidence |
|---|---|---|
| Required 73-module order | 73/73, zero errors; exactly the unchanged eight base admissions | `logs/final-sweep.log` |
| Owned module | Zero errors; exactly the three original admissions, no new helper admission | `logs/final-sweep.log` |
| Downstream `Games` and facade | Zero errors and no admissions | `logs/final-sweep.log` |
| Original pre-ship probe | 124 public-name checks, exit 0 | `evidence/B4MemPreShip.lean.txt`, `logs/preship.log` |
| Seven sanity cases | All seven pass by explicit reduction, `rfl`, `simp` and `decide`; exit 0 | `evidence/B4MemSanity.lean.txt`, `logs/sanity.log` |
| New-helper axiom audit | 94 theorem declarations including generated equations; all axioms within the permitted three | `evidence/B4MemAxioms.lean.txt`, `logs/axioms.log` |
| Target axiom gate | **Incomplete**, as expected for this partial; `sorryAx` remains | `logs/axioms.log` |
| Campaign style lint | **0 FAIL, 1 WARN** (file size, justified below) | `logs/lint.log` |
| Statement/file freeze | Exact byte comparisons pass outside the owned insertion and appendix | `logs/freeze.log` |
| Duplication | Original before/after screens complete; no new cross-file pair | `logs/screen-before.txt`, `logs/screen-after.txt`, `logs/screen-review.txt` |

The required bootstrap also serves as the final full sweep: all upstream source
files remained unchanged, and the final source was committed before the sweep
reached `TQBF`. Every invocation used the unchanged `lean_check_tree.sh`, including
its fresh-olean and error-diagnostic gates. The process exited 0.

The final target axiom print is:

```text
'Complexity.TQBF_mem_PSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The audit rejects any other axiom in a new helper and checks that at least the
29 explicit theorem declarations were found; it reports 94 including generated
equations and structure-related theorems. The sanity file uses explicit unfolding
because no global decidability instance for `TQBF` membership is installed; no
public instance or repository statement was changed to run the examples.

Final sweep tail:

```text
CHECK TCSlib/Complexity/SpaceComplexity/SpaceClasses
CHECK TCSlib/Complexity/SpaceComplexity/Constructible
TCSlib/Complexity/SpaceComplexity/Constructible.lean:76:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Constructible.lean:92:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity/ConfigGraph
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:568:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:588:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:608:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity/Inclusions
CHECK TCSlib/Complexity/TuringMachine/Build/CfgRecord
CHECK TCSlib/Complexity/ClassPSPACE/TQBF
TCSlib/Complexity/ClassPSPACE/TQBF.lean:2576:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:2628:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:2636:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassPSPACE/Games
CHECK TCSlib/Complexity/ClassPSPACE
PASS: 73/73 modules, zero errors, exactly eight unchanged base sorry warnings.
```


## Sizes, freeze and delivery

- Local delivery commit: `92c9a743d22c05c0f30541e4b2ecd42361ff55b7`.
- `TQBF.lean`: **2,639 lines; 8 public and 164 private explicit declarations**.
- New block: **713 lines; 0 public and 45 private declarations**, including
  **29 theorem declarations**. The remaining 16 are definitions, abbreviations
  and the framed-module structure. Generated equation/projection declarations
  are not included in these source-level counts.
- Diff: **738 inserted lines and 1 replaced docstring-closing line** (737 net new lines),
  no deleted or modified original lines outside the permitted docstring insertion.
- `freeze.log` verifies the unchanged original prefix (including B4a and imports),
  unchanged original docstring before its appendix, and unchanged suffix from
  the target theorem onward. It also checks the branch, ancestor and whitespace.
- The git bundle is incremental against base
  `3462c1b49a49d2cd458f595624c1dbac1f868af3`; that prerequisite commit is required
  when importing it. It contains only the `fill/ch34-b4-mem` delivery ref.
- `git bundle verify` succeeds, with the recorded base as its sole prerequisite.
- The format-patch applies cleanly to an isolated copy of the exact base file;
  the result is byte-identical to the delivered source. No other branch was
  created or changed to test application.
- `SHA256SUMS` covers every archive payload file except the checksum manifest
  itself. The delivery packager checks ZIP integrity and rehashes every entry.


The source remains in one file because the binding brief owns only this target
and expressly requires a single private block. That is the recorded reason for
the file-size lint warning; no shared file was edited.

The archive includes this report, the full modified source, a format-patch series
against the recorded base, a git bundle, final sweep/axiom/sanity/probe/lint and
duplication evidence, the executed evidence sources, and `SHA256SUMS`. The patch
and bundle are the integration paths; this archive is not a PR or a push.

## Verbatim duplication screen outputs

### Before

```text
declarations screened: 1472; copy pairs (target reproduces >= half of source): 871; reproduced text: 297,548 chars
   Catalog.lean::f2_loopBody_step  reproduces  Loop.lean::loopBody_step: 1094/1094 = 100%
   Loop.lean::loop_find_run  reproduces  Catalog.lean::f2_loop_find_run: 678/678 = 100%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_find_run: 678/678 = 100%
   Loop.lean::loop_halted_run  reproduces  Catalog.lean::a2_loop_halted_run: 659/659 = 100%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_halted_run: 659/659 = 100%
   Loop.lean::loop_rewind_bounded  reproduces  Catalog.lean::f2_loop_rewind_bounded: 514/514 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Loop.lean::loop_rewind_bounded: 514/514 = 100%
   Catalog.lean::f2_loopBody_run  reproduces  Loop.lean::loopBody_run: 452/452 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Loop.lean::loopBodyTM  reproduces  Catalog.lean::f2_loopBodyTM: 428/428 = 100%
   Catalog.lean::f2_loopBodyTM  reproduces  Loop.lean::loopBodyTM: 428/428 = 100%
   Catalog.lean::f2_loopFuel_init  reproduces  Loop.lean::loopFuel_init: 410/410 = 100%
   Loop.lean::loopBuffer_write  reproduces  Catalog.lean::f2_loopBuffer_write: 408/408 = 100%
   Catalog.lean::f2_loopBuffer_write  reproduces  Loop.lean::loopBuffer_write: 408/408 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::f2_loopBody_stop  reproduces  Loop.lean::loopBody_stop: 346/346 = 100%
   Catalog.lean::f2_loopReplay_run  reproduces  Loop.lean::loopReplay_run: 345/345 = 100%
   Loop.lean::loop_first_halt  reproduces  Catalog.lean::f2_loop_first_halt: 341/341 = 100%
   Catalog.lean::f2_loop_first_halt  reproduces  Loop.lean::loop_first_halt: 341/341 = 100%
   Catalog.lean::f2_loopCopy_erase  reproduces  Loop.lean::loopCopy_erase: 285/285 = 100%
   Loop.lean::loopFrame  reproduces  Catalog.lean::f2_loopFrame: 270/270 = 100%
   Catalog.lean::f2_loopFrame  reproduces  Loop.lean::loopFrame: 270/270 = 100%
   Loop.lean::loop_output_length_le  reproduces  Catalog.lean::f2_loop_output_length_le: 254/254 = 100%
   Catalog.lean::f2_loop_output_length_le  reproduces  Loop.lean::loop_output_length_le: 254/254 = 100%
   Catalog.lean::f2_loopFuel_run  reproduces  Loop.lean::loopFuel_run: 230/230 = 100%
   Loop.lean::loopBodyCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 212/212 = 100%
   Catalog.lean::f2_loopBodyCfg  reproduces  Loop.lean::loopBodyCfg: 212/212 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Loop.lean::loopControlAction  reproduces  Catalog.lean::f2_loopControlAction: 150/150 = 100%
   Catalog.lean::f2_loopControlAction  reproduces  Loop.lean::loopControlAction: 150/150 = 100%
   Catalog.lean::f2_loopCall  reproduces  Loop.lean::loopCall: 141/141 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::f2_loopValue_bits  reproduces  Loop.lean::loopValue_bits: 135/135 = 100%
   Loop.lean::loopReplayTM  reproduces  Catalog.lean::f2_loopReplayTM: 130/130 = 100%
   Catalog.lean::f2_loopReplayTM  reproduces  Loop.lean::loopReplayTM: 130/130 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Loop.lean::loopFuelSource  reproduces  Catalog.lean::f2_loopFuelSource: 122/122 = 100%
   Catalog.lean::f2_loopFuelSource  reproduces  Loop.lean::loopFuelSource: 122/122 = 100%
   Catalog.lean::f2_loopBodySource  reproduces  Loop.lean::loopBodySource: 119/119 = 100%
   Loop.lean::emCall_erase_last  reproduces  Catalog.lean::f2_catalogBuffer_erase: 118/118 = 100%
   Catalog.lean::f2_loopCopy_final  reproduces  Loop.lean::loopCopy_final: 110/110 = 100%
   Loop.lean::loop_orbit_inv  reproduces  Catalog.lean::f2_loop_orbit_inv: 94/94 = 100%
   Catalog.lean::f2_loop_orbit_inv  reproduces  Loop.lean::loop_orbit_inv: 94/94 = 100%
   Catalog.lean::f2_loopBorrowPos_le  reproduces  Loop.lean::loopBorrowPos_le: 93/93 = 100%
   Loop.lean::loopFuelCfg  reproduces  Catalog.lean::f2_loopFuelCfg: 90/90 = 100%
   Catalog.lean::f2_loopFuelCfg  reproduces  Loop.lean::loopFuelCfg: 90/90 = 100%
   Loop.lean::loopBuffer_read  reproduces  Catalog.lean::f2_loopBuffer_read: 89/89 = 100%
   Catalog.lean::f2_loopBuffer_read  reproduces  Loop.lean::loopBuffer_read: 89/89 = 100%
   Loop.lean::loop_fuel_width  reproduces  Catalog.lean::f2_loop_fuel_width: 87/87 = 100%
   Catalog.lean::f2_loop_fuel_width  reproduces  Loop.lean::loop_fuel_width: 87/87 = 100%
   Catalog.lean::f2_loopFrame_payload  reproduces  Loop.lean::loopFrame_payload: 79/79 = 100%
   Catalog.lean::f2_loopFlag_clear  reproduces  Loop.lean::loopFlag_clear: 60/60 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Loop.lean::loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Loop.lean::loopBody_run  reproduces  Catalog.lean::f2_loopBody_run: 452/455 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Catalog.lean::f2_loopHost_contracts  reproduces  Loop.lean::loopHost_contracts: 3565/3596 = 99%
   Loop.lean::loopBody_step  reproduces  Catalog.lean::f2_loopBody_step: 1094/1109 = 99%
   Loop.lean::loopBody_stop  reproduces  Catalog.lean::f2_loopBody_stop: 346/352 = 98%
   Loop.lean::loopReplay_run  reproduces  Catalog.lean::f2_loopReplay_run: 345/351 = 98%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   InputCall.lean::inputSeekRewind  reproduces  Inclusions.lean::b2b_rewindTM: 204/208 = 98%
   Catalog.lean::f2_loopHost  reproduces  Loop.lean::loopHostM: 2368/2417 = 98%
   Loop.lean::loopCopy_erase  reproduces  Catalog.lean::f2_loopCopy_erase: 285/291 = 98%
   Loop.lean::loopCall  reproduces  Catalog.lean::f2_loopCall: 141/144 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Tautology.lean::taut_syntax_double  reproduces  Tautology.lean::taut_syntax_separator: 416/426 = 98%
   Loop.lean::loopBodySource  reproduces  Catalog.lean::f2_loopBodySource: 119/122 = 98%
   SAT.lean::satClean_install  reproduces  SAT.lean::satClean_emit: 589/604 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Loop.lean::loopFuel_run  reproduces  Catalog.lean::f2_loopFuel_run: 230/236 = 97%
   Loop.lean::loopFuel_init  reproduces  Catalog.lean::f2_loopFuel_init: 410/422 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Zone.lean::zoneShiftOut  reproduces  Zone.lean::zoneShiftIn: 251/259 = 97%
   Loop.lean::loopBorrowPos_le  reproduces  Catalog.lean::f2_loopBorrowPos_le: 93/96 = 97%
   Tautology.lean::tautDual_valid  reproduces  Tautology.lean::tautDual_copy_end: 338/349 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Tautology.lean::taut_work_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Simulation.lean::bufferedScanCfg_run  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_maxFormula  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_maxClause  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_counterBack  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satPair_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_right_scan  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_finish_transfer  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_finish_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_finish_erase  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_finish_arg  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_splitRestore_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_rawStrip_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_extract_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_catalogPoly_setup  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_catalogPoly_emit  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_replay  reproduces  Loop.lean::loopHost_replay: 1032/1069 = 97%
   Loop.lean::loopFrame_payload  reproduces  Catalog.lean::f2_loopFrame_payload: 79/82 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Loop.lean::loopHost_frame_replay: 888/923 = 96%
   Catalog.lean::f2_loopReplay_step  reproduces  Loop.lean::loopReplay_step: 316/329 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   SAT.lean::sat_pt_head  reproduces  SAT.lean::sat_pt_tail: 379/395 = 96%
   Tautology.lean::taut_syntax_separator  reproduces  Tautology.lean::taut_syntax_double: 416/434 = 96%
   Loop.lean::loopValue_bits  reproduces  Catalog.lean::f2_loopValue_bits: 135/141 = 96%
   Catalog.lean::f2_loopControl_payload  reproduces  Loop.lean::loopControl_payload: 235/246 = 96%
   SAT.lean::sat_pt_tail  reproduces  SAT.lean::sat_pt_head: 379/397 = 95%
   Zone.lean::zoneShiftIn  reproduces  Zone.lean::zoneShiftOut: 251/263 = 95%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   SAT.lean::satDrop_skip  reproduces  SAT.lean::satRed_one: 60/63 = 95%
   Loop.lean::loopFlag_clear  reproduces  Catalog.lean::f2_loopFlag_clear: 60/63 = 95%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_halted_run: 627/659 = 95%
   Loop.lean::loop_run  reproduces  Catalog.lean::a2_loop_halted_run: 627/659 = 95%
   Catalog.lean::f2_loopHost_accept  reproduces  Loop.lean::loopHost_accept: 2127/2238 = 95%
   Catalog.lean::f2_loopDebit_value  reproduces  Loop.lean::loopDebit_value: 187/197 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Loop.lean::loopHostM  reproduces  Catalog.lean::f2_loopHost: 2368/2495 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Loop.lean::loopCopy_final  reproduces  Catalog.lean::f2_loopCopy_final: 110/116 = 95%
   SAT.lean::satClean_emit  reproduces  SAT.lean::satClean_install: 589/623 = 95%
   SAT.lean::satVerdict_true_poly  reproduces  SAT.lean::satVerdict_false_poly: 381/403 = 95%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_bank_initial: 3070/3250 = 94%
   Loop.lean::loopControl_payload  reproduces  Catalog.lean::f2_loopControl_payload: 235/249 = 94%
   Loop.lean::loopHost_round  reproduces  Catalog.lean::f2_loopHost_round: 1989/2114 = 94%
   Catalog.lean::f2_loopDebit_success  reproduces  Loop.lean::loopDebit_success: 141/150 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::f2_exists_loopFind_space  reproduces  Loop.lean::exists_loopFindTM: 851/910 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Loop.lean::loopHost_replay  reproduces  Catalog.lean::f2_loopHost_replay: 1032/1105 = 93%
   Catalog.lean::f2_loopBodyPadded  reproduces  Loop.lean::loopBodyPadded: 137/147 = 93%
   Loop.lean::loopHost_frame_replay  reproduces  Catalog.lean::f2_loopHost_frame_replay: 888/953 = 93%
   Loop.lean::loop_first_halt  reproduces  SAT.lean::sat_call_first_halt: 307/330 = 93%
   Catalog.lean::f2_loop_first_halt  reproduces  SAT.lean::sat_call_first_halt: 307/330 = 93%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Loop.lean::loopReplay_step  reproduces  Catalog.lean::f2_loopReplay_step: 316/341 = 93%
   Loop.lean::loopHost_accept  reproduces  Catalog.lean::f2_loopHost_accept: 2127/2297 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Loop.lean::loopHost_borrow_run: 489/531 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::f2_loop_live_prefix  reproduces  SAT.lean::sat_live_prefix: 139/152 = 91%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Loop.lean::loopBodyPadded  reproduces  Catalog.lean::f2_loopBodyPadded: 137/150 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Catalog.lean::f2_loopHost_round  reproduces  Loop.lean::loopHost_round: 1989/2194 = 91%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Loop.lean::loopFuelCaptured_frame: 1423/1570 = 91%
   Tautology.lean::tautDual_copy  reproduces  Tautology.lean::tautDual_scan: 842/929 = 91%
   Tautology.lean::taut_syntax_unary  reproduces  Tautology.lean::taut_syntax_bad: 77/85 = 91%
   Simulation.lean::rewind_from_any  reproduces  Loop.lean::loop_rewind_bounded: 465/514 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Loop.lean::loopDebit_success  reproduces  Catalog.lean::f2_loopDebit_success: 141/156 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   SAT.lean::sat_call_first_halt  reproduces  Loop.lean::loop_first_halt: 307/341 = 90%
   SAT.lean::sat_call_first_halt  reproduces  Catalog.lean::f2_loop_first_halt: 307/341 = 90%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Loop.lean::loopHost_fuel_copy: 1319/1466 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   Loop.lean::loopHost_borrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 489/544 = 90%
   SAT.lean::satPairCfg  reproduces  SAT.lean::satEvalCfg: 131/146 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Loop.lean::loopHost_anchor_return: 829/926 = 90%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Catalog.lean::f2_exists_loopFind_space  reproduces  Loop.lean::exists_loopTM: 687/770 = 89%
   Tautology.lean::taut_split_exists  reproduces  SAT.lean::sat_split_exists: 123/138 = 89%
   SAT.lean::sat_live_prefix  reproduces  Catalog.lean::f2_loop_live_prefix: 139/156 = 89%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopTM: 686/770 = 89%
   Catalog.lean::f2_loopReady  reproduces  Loop.lean::loopReady: 119/134 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   SAT.lean::satEvalCfg  reproduces  SAT.lean::satPairCfg: 131/148 = 89%
   Catalog.lean::f2_splitCount_run  reproduces  Loop.lean::emCall_right_run: 152/172 = 88%
   Tautology.lean::tautDual_invalid  reproduces  Tautology.lean::tautDual_copy_end: 308/349 = 88%
   Loop.lean::loopDebit_value  reproduces  Catalog.lean::f2_loopDebit_value: 187/212 = 88%
   Catalog.lean::f2_catalogBuffer_erase  reproduces  Loop.lean::emCall_erase_last: 118/134 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Tautology.lean::tautSplit  reproduces  SAT.lean::satSplit: 65/74 = 88%
   SAT.lean::satSplit  reproduces  Tautology.lean::tautSplit: 65/74 = 88%
   Tautology.lean::tautDual_rewind  reproduces  Tautology.lean::tautDual_copy_end: 305/349 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Loop.lean::emCall_first_entry  reproduces  Catalog.lean::f2_catalogFirstEntry: 327/375 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Loop.lean::loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopFuelCaptured_frame: 1423/1639 = 87%
   Catalog.lean::f2_loopBodySource_run  reproduces  Loop.lean::loopBodySource_run: 78/90 = 87%
   Catalog.lean::f2_loopHost_borrow_step  reproduces  Loop.lean::loopHost_borrow_step: 581/671 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Loop.lean::loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 1319/1527 = 86%
   CfgRecord.lean::recordStep_reject_run  reproduces  CfgRecord.lean::recordStep_empty_run: 467/541 = 86%
   Loop.lean::loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_anchor_return: 829/963 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_rewind: 1025/1195 = 86%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_pair_triple: 138/161 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::f2_loopDebit_iterate_value  reproduces  Loop.lean::loopDebit_iterate_value: 248/290 = 86%
   SAT.lean::sat_split_exists  reproduces  Tautology.lean::taut_split_exists: 123/144 = 85%
   CfgRecord.lean::recordStep_empty_run  reproduces  CfgRecord.lean::recordStep_reject_run: 467/547 = 85%
   Loop.lean::loopReady  reproduces  Catalog.lean::f2_loopReady: 119/140 = 85%
   Loop.lean::loopHost_fuel_setup  reproduces  Catalog.lean::f2_loopHost_fuel_setup: 782/921 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   Catalog.lean::f2_loopHost_reject  reproduces  Loop.lean::loopHost_reject: 2023/2398 = 84%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CNF.lean::le_foldr_max_of_mem  reproduces  Tautology.lean::taut_le_max: 115/137 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_bank_final: 3070/3669 = 84%
   Catalog.lean::f2_loopHost_fuel_setup  reproduces  Loop.lean::loopHost_fuel_setup: 782/935 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Loop.lean::loopHost_fuel_return: 982/1176 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::f2_loopCopy_initial  reproduces  Loop.lean::loopCopy_initial: 78/94 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Loop.lean::loopHost_borrow_step  reproduces  Catalog.lean::f2_loopHost_borrow_step: 581/704 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   SAT.lean::satDrop_rewind  reproduces  SAT.lean::satDrop_dispatch: 256/311 = 82%
   Loop.lean::exists_emitCallTM  reproduces  Loop.lean::exists_installCallTM: 194/236 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Loop.lean::loopHost_contracts  reproduces  Catalog.lean::f2_loopHost_contracts: 3565/4347 = 82%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_reject_run: 448/547 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_loopHost_prepare  reproduces  Loop.lean::loopHost_prepare: 1091/1338 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Loop.lean::loopBodySource_run  reproduces  Catalog.lean::f2_loopBodySource_run: 78/96 = 81%
   Catalog.lean::f2_loopControl_apply  reproduces  Loop.lean::loopControl_apply: 643/792 = 81%
   Loop.lean::loopHost_reject  reproduces  Catalog.lean::f2_loopHost_reject: 2023/2493 = 81%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Loop.lean::emCall_first_entry: 327/403 = 81%
   Tautology.lean::tautDual_scan  reproduces  Tautology.lean::tautDual_copy: 842/1039 = 81%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopTM: 624/770 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   SAT.lean::satReq_round  reproduces  SAT.lean::satReq_fields: 93/115 = 81%
   Loop.lean::loopDebit_iterate_value  reproduces  Catalog.lean::f2_loopDebit_iterate_value: 248/308 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Zone.lean::zoneSide_cascadeRight  reproduces  Zone.lean::zoneCascadeRight_zero: 117/146 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   CNFEncoding.lean::parseClauses_bounds  reproduces  CNFEncoding.lean::parseClause_bounds: 731/920 = 79%
   Inclusions.lean::b2b_rewindTM  reproduces  InputCall.lean::inputSeekRewind: 204/257 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   SAT.lean::satMax_prefix  reproduces  SAT.lean::satMax_finish: 428/540 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_borrow_rewind: 932/1181 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   SAT.lean::satSplitClause_width  reproduces  SAT.lean::satSplitClause_vars: 67/85 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Loop.lean::emCall_finish_final  reproduces  Loop.lean::emCall_finish_initial: 1279/1629 = 79%
   InputCall.lean::inputSeekStep_run  reproduces  Games.lean::playOut_eq_iterate: 69/88 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Tautology.lean::taut_le_max  reproduces  CNF.lean::le_foldr_max_of_mem: 115/147 = 78%
   Loop.lean::exists_installCallTM  reproduces  Loop.lean::exists_emitCallTM: 194/248 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Loop.lean::loopCopy_initial  reproduces  Catalog.lean::f2_loopCopy_initial: 78/100 = 78%
   CfgRecord.lean::record_digits_value  reproduces  MeyerTableau.lean::ctrVal_enumWord: 145/186 = 78%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_reject_run: 426/547 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::f2_loopDebit_iterate_length  reproduces  Loop.lean::loopDebit_iterate_length: 68/88 = 77%
   Loop.lean::loopControl_apply  reproduces  Catalog.lean::f2_loopControl_apply: 643/834 = 77%
   SAT.lean::satPairAction_apply  reproduces  SAT.lean::satEvalAction_apply: 121/157 = 77%
   SAT.lean::satEvalAction_apply  reproduces  SAT.lean::satPairAction_apply: 121/157 = 77%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_erase: 972/1264 = 77%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::a2_mapSetup_run: 125/163 = 77%
   Loop.lean::loopHost_halt_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 389/508 = 77%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Loop.lean::loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Tautology.lean::tautDual_valid  reproduces  Tautology.lean::tautDual_invalid: 633/832 = 76%
   CNFEncoding.lean::parseClauses_repr  reproduces  CNFEncoding.lean::parseClause_repr: 380/501 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Loop.lean::exists_loopTM  reproduces  Loop.lean::exists_loopFindTM: 686/910 = 75%
   Zone.lean::zoneSide_shiftOutW  reproduces  Zone.lean::zoneSide_shiftInW: 296/394 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 879/1176 = 75%
   Loop.lean::loopDebit_iterate_length  reproduces  Catalog.lean::f2_loopDebit_iterate_length: 68/91 = 75%
   SAT.lean::satReqStep_poly  reproduces  SAT.lean::satReqEmit_poly: 333/446 = 75%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopFindTM: 679/910 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 879/1181 = 74%
   TQBF.lean::codecCnf_numVars  reproduces  TQBF.lean::codecCnfCost_relabel: 61/82 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_finish_final: 1279/1731 = 74%
   CNFEncoding.lean::parseClause_bounds  reproduces  CNFEncoding.lean::parseClauses_bounds: 731/992 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   CNFEncoding.lean::parseClause_repr  reproduces  CNFEncoding.lean::parseClauses_repr: 380/517 = 74%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Loop.lean::loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Loop.lean::loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Loop.lean::loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Loop.lean::emCall_right_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 125/171 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   CfgRecord.lean::recordStep_map_snapshot  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 875/1198 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Loop.lean::loopBuffer_read: 65/89 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   CNFEncoding.lean::numVars_le_of_literal_bounds  reproduces  CNF.lean::foldr_max_le_of_forall: 97/133 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Loop.lean::loopHost_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1091/1499 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Loop.lean::emCall_right_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Loop.lean::loopHost_start  reproduces  Catalog.lean::f2_loopHost_start: 209/289 = 72%
   Loop.lean::loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Loop.lean::loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_return: 982/1366 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Loop.lean::loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_arg: 1025/1438 = 71%
   Catalog.lean::f2_loopReady_call  reproduces  Loop.lean::loopReady_call: 708/994 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Loop.lean::emCall_right_run: 122/172 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   TQBF.lean::configurationValidity_size_raw  reproduces  TQBF.lean::configurationValidity_numVars: 68/96 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Loop.lean::loopReplayTM: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Loop.lean::loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 932/1329 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_reject_run: 383/547 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_inverse: 128/183 = 70%
   Zone.lean::zoneMoveRight  reproduces  Zone.lean::zoneMoveLeft: 265/379 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_rewind: 835/1195 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   SAT.lean::satReqStep  reproduces  SAT.lean::satReqEmit: 159/229 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Zone.lean::zoneMoveLeft  reproduces  Zone.lean::zoneMoveRight: 265/382 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   MeyerTableau.lean::wstep_some_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 79/114 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   CfgRecord.lean::recordStep_probe_run  reproduces  CfgRecord.lean::recordStep_read_run: 103/149 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Loop.lean::loopBody_step  reproduces  Loop.lean::loopBody_stop: 239/346 = 69%
   SAT.lean::satSplitClause_vars  reproduces  SAT.lean::satSplitClause_width: 67/97 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::f2_counterInc_bits  reproduces  Loop.lean::loopValue_bits: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Loop.lean::loopHost_init  reproduces  Catalog.lean::f2_loopHost_init: 65/95 = 68%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_empty_run: 370/541 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_input_rewind  reproduces  Loop.lean::loopHost_input_rewind: 164/241 = 68%
   Catalog.lean::skipBackTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 969/1430 = 68%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_arg: 972/1438 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   CNFEncoding.lean::parseClause_bounds  reproduces  CNFEncoding.lean::parseClause_repr: 336/501 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Loop.lean::loopHost_input_rewind  reproduces  Catalog.lean::f2_loopHost_input_rewind: 164/245 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   CNFEncoding.lean::parseClauses  reproduces  CNFEncoding.lean::parseClause: 117/175 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_inverse: 122/183 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Catalog.lean::f2_loopDebit  reproduces  Loop.lean::loopDebit: 62/93 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Loop.lean::loopReady_call  reproduces  Catalog.lean::f2_loopReady_call: 708/1066 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   SAT.lean::satEval_double  reproduces  SAT.lean::satEval_skip: 137/207 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_find_run: 448/678 = 66%
   Loop.lean::loop_run  reproduces  Catalog.lean::f2_loop_find_run: 448/678 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_erase: 835/1264 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_loopBody_step  reproduces  Loop.lean::loopBody_stop: 228/346 = 66%
   Inclusions.lean::b2b_callEmb  reproduces  Inclusions.lean::b2b_bankEmb: 67/102 = 66%
   Catalog.lean::f2_loopHost_init  reproduces  Loop.lean::loopHost_init: 65/99 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_empty_run: 355/541 = 66%
   Loop.lean::emCall_track_action  reproduces  Simulation.lean::bufferedFirstCfg_init: 211/322 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_empty_run: 353/541 = 65%
   SAT.lean::satMax_finish  reproduces  SAT.lean::satMax_prefix: 428/656 = 65%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_pair: 152/233 = 65%
   CNFEncoding.lean::parseClauses_bounds  reproduces  CNFEncoding.lean::parseClauses_repr: 337/517 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   SAT.lean::sat_pt_append  reproduces  SAT.lean::sat_pt_pair: 65/100 = 65%
   Loop.lean::loopBodyImage  reproduces  Loop.lean::emLoopCall: 87/134 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Loop.lean::loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 228/352 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_right_step: 134/207 = 65%
   Inclusions.lean::b2b_trialCfg  reproduces  Inclusions.lean::b2b_setupCfg: 119/184 = 65%
   Tautology.lean::taut_certificate_equiv  reproduces  SAT.lean::sat_certificate: 243/376 = 65%
   Catalog.lean::f2_loopCall_reframe  reproduces  Loop.lean::loopCall_reframe: 484/749 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_stamp: 450/698 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   Catalog.lean::f2_loopHost_release  reproduces  Loop.lean::loopHost_release: 524/815 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Zone.lean::zoneSide_shiftInW  reproduces  Zone.lean::zoneSide_shiftOutW: 296/462 = 64%
   Tautology.lean::tautDual_unary  reproduces  SAT.lean::satWidth_index: 62/97 = 64%
   SAT.lean::satStream_parseLit  reproduces  SAT.lean::satWidth_index: 62/97 = 64%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   SAT.lean::satAppend_copy  reproduces  SAT.lean::satAppend_seek: 528/832 = 63%
   Catalog.lean::a2_loop_prepare  reproduces  Loop.lean::loopHost_prepare: 849/1338 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Loop.lean::loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   Loop.lean::emCall_prepare_initial  reproduces  Inclusions.lean::b2b_embed_refl: 113/180 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   SAT.lean::satEval_start  reproduces  SAT.lean::satPair_start: 1086/1733 = 63%
   Loop.lean::loopDebit  reproduces  Catalog.lean::f2_loopDebit: 62/99 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Loop.lean::loopBodyDispatch  reproduces  Loop.lean::loopBodyImage: 118/190 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   CNFEncoding.lean::parseClause  reproduces  CNFEncoding.lean::parseClauses: 117/189 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   SAT.lean::satRed_maxClause  reproduces  SAT.lean::sat_clause_measure: 67/109 = 61%
   SAT.lean::satEval_clause  reproduces  SAT.lean::sat_clause_measure: 67/109 = 61%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_payload_scan: 422/688 = 61%
   SAT.lean::sat_pt_unaryLength  reproduces  CNFEncoding.lean::takeTrues_repr: 76/124 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Tautology.lean::taut_eval_double  reproduces  Tautology.lean::taut_syntax_separator: 261/426 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   SAT.lean::satScan_step  reproduces  Catalog.lean::f2_scanStep_right: 100/164 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Loop.lean::loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Loop.lean::loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 288/476 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_erase: 764/1264 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_rewind: 722/1195 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Tautology.lean::taut_syntax_formula  reproduces  Tautology.lean::taut_syntax_clause: 381/633 = 60%
   Catalog.lean::f2_loopHost_borrow  reproduces  Loop.lean::loopHost_borrow: 258/429 = 60%
   Tautology.lean::taut_eval_double  reproduces  Tautology.lean::taut_syntax_double: 261/434 = 60%
   Tautology.lean::tautDual_invalid  reproduces  Tautology.lean::tautDual_valid: 633/1053 = 60%
   Loop.lean::loopHost_release  reproduces  Catalog.lean::f2_loopHost_release: 524/872 = 60%
   Catalog.lean::seekEndTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 859/1430 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Loop.lean::loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_reframe: 484/809 = 60%
   SAT.lean::satDrop_skip  reproduces  SAT.lean::satDrop_dispatch: 186/311 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopCfgTM: 95/159 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Loop.lean::loopCall  reproduces  Loop.lean::emLoopCall: 80/134 = 60%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_clear_heads: 124/208 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   CfgRecord.lean::recordStep_read_prefix  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 712/1198 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopTM: 457/770 = 59%
   Tautology.lean::taut_syntax_separator  reproduces  Tautology.lean::taut_eval_double: 261/440 = 59%
   Tautology.lean::taut_syntax_double  reproduces  Tautology.lean::taut_eval_double: 261/440 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_pair: 138/233 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   CfgRecord.lean::recordStep_restore_digits  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   CfgRecord.lean::recordStep_prepare_native  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Loop.lean::emCall_track_initial  reproduces  Simulation.lean::bufferedFirstCfg_init: 190/322 = 59%
   Catalog.lean::f2_loopCall  reproduces  Loop.lean::emLoopCall: 79/134 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   SAT.lean::satWidth_clause  reproduces  Tautology.lean::tautDual_clause: 142/242 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Tautology.lean::taut_syntax_clause  reproduces  Tautology.lean::taut_syntax_formula: 381/653 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   SAT.lean::satPair_start  reproduces  SAT.lean::satEval_start: 1086/1871 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   SAT.lean::satPad_run  reproduces  Catalog.lean::f2_splitEmbed_run: 109/188 = 58%
   Loop.lean::loopHost_borrow  reproduces  Catalog.lean::f2_loopHost_borrow: 258/445 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopCfgTM: 92/159 = 58%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_empty_run: 313/541 = 58%
   Loop.lean::emCall_clear_left  reproduces  Loop.lean::emCall_clear_scan: 369/638 = 58%
   SAT.lean::satPair_replay  reproduces  SAT.lean::satPair_rewind: 542/938 = 58%
   Catalog.lean::seekStartTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 825/1430 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Loop.lean::emCallTripleEmbedding  reproduces  Loop.lean::emCallPairEmbedding: 69/120 = 57%
   SAT.lean::satScanTM  reproduces  SAT.lean::satMapTM: 73/127 = 57%
   Loop.lean::emCall_track_stamp  reproduces  Loop.lean::emCall_track_initial: 398/693 = 57%
   CfgRecord.lean::recordStep_clear_snapshot  reproduces  CfgRecord.lean::recordStep_map_snapshot: 875/1525 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Loop.lean::emCall_prepare_final  reproduces  Inclusions.lean::b2b_embed_refl: 103/180 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_pair_triple: 92/161 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Loop.lean::loop_output_length_le: 145/254 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Tautology.lean::taut_copy_run  reproduces  Tautology.lean::taut_move_right: 69/121 = 57%
   Loop.lean::emCall_track_initial  reproduces  Loop.lean::emCall_track_stamp: 398/698 = 57%
   SAT.lean::satStreamStep_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 65/114 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Zone.lean::zoneStage_leftWindow  reproduces  Zone.lean::zoneStage_rightWindow: 266/467 = 57%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_arg: 819/1438 = 57%
   TQBF.lean::configurationAdjacency_bounds  reproduces  TQBF.lean::configurationInputEquality_bounds: 169/297 = 57%
   SAT.lean::satPair_rewind  reproduces  SAT.lean::satEval_rewind: 446/785 = 57%
   Loop.lean::emLoopCall  reproduces  Loop.lean::loopCall: 80/141 = 57%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_copyback_run: 1173/2070 = 57%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 666/1176 = 57%
   Tautology.lean::taut_syntax_bad  reproduces  Tautology.lean::taut_syntax_unary: 77/136 = 57%
   SAT.lean::satMax_finish  reproduces  SAT.lean::satDrop_dispatch: 176/311 = 57%
   CfgRecord.lean::RecordEqIndex  reproduces  CfgRecord.lean::RecordTestIndex: 73/129 = 57%
   SAT.lean::satStop_clean  reproduces  Seam.lean::seamCompTM_runFrom_left: 95/168 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Loop.lean::emCallPairIndex  reproduces  Loop.lean::emCallPairSelect: 61/108 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Loop.lean::loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Loop.lean::loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_transfer: 819/1459 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::catalogCopyF  reproduces  Scan.lean::scanWriteCfg: 113/202 = 56%
   Zone.lean::zoneSide_cascadeRight  reproduces  Zone.lean::zoneCascadeRight_blocked: 432/773 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   SAT.lean::satMapTM  reproduces  SAT.lean::satScanTM: 73/131 = 56%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_finish_initial: 904/1629 = 55%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Loop.lean::loopHost_halt_return: 389/701 = 55%
   TQBF.lean::configurationCodec_input_eq  reproduces  TQBF.lean::configurationCodec_eq_iff: 81/146 = 55%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 322/581 = 55%
   SAT.lean::satAppendTM  reproduces  Inclusions.lean::b2b_rewindTM: 115/208 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   CfgRecord.lean::RecordTestIndex  reproduces  CfgRecord.lean::RecordEqIndex: 73/133 = 55%
   Loop.lean::emLoopCall  reproduces  Catalog.lean::f2_loopCall: 79/144 = 55%
   Scan.lean::scanWriteCfg  reproduces  Catalog.lean::catalogCopyF: 113/206 = 55%
   CNFEncoding.lean::parseClauses_serialize  reproduces  CNFEncoding.lean::parseClause_serializeClause: 402/733 = 55%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Loop.lean::emCall_first_entry: 221/403 = 55%
   SAT.lean::satPad_run  reproduces  Seam.lean::seamRelease_step_right: 74/135 = 55%
   SAT.lean::satPad_run  reproduces  Seam.lean::seamComp_step_right: 74/135 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   Loop.lean::loopHost_body_run  reproduces  Catalog.lean::f2_loopHost_body_capture: 64/117 = 55%
   Loop.lean::loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 203/372 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Catalog.lean::f2_loopBorrow_run  reproduces  Loop.lean::loopHost_borrow_run: 288/531 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Loop.lean::loopReplay_run: 187/345 = 54%
   CfgRecord.lean::recordRun_trans  reproduces  Tautology.lean::tautDual_segment_add: 91/168 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   SAT.lean::satAppend_rewind  reproduces  SAT.lean::satAppend_seek: 450/832 = 54%
   Loop.lean::loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 285/527 = 54%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopFindTM: 491/910 = 54%
   SAT.lean::satStreamRead_word  reproduces  SAT.lean::satReq_fields: 62/115 = 54%
   SAT.lean::satMap_run  reproduces  SAT.lean::satScan_run: 269/499 = 54%
   Loop.lean::emCallPairEmbedding  reproduces  Loop.lean::emCallTripleEmbedding: 69/128 = 54%
   Loop.lean::emCall_track_run  reproduces  Loop.lean::emCall_track_extent: 145/269 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SAT.lean::satWidth_formula  reproduces  Tautology.lean::tautDual_serialize: 167/310 = 54%
   MeyerTableau.lean::RW_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   MeyerTableau.lean::RI_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   CNFEncoding.lean::parseClause_serializeClause  reproduces  CNFEncoding.lean::parseClauses_serialize: 402/747 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 633/1181 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   SAT.lean::satReq_fields_poly  reproduces  SAT.lean::sat_pt_append: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_initial: 370/693 = 53%
   SAT.lean::satEvalTM  reproduces  Inclusions.lean::b2b_rewindTM: 111/208 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_prepare_final: 377/707 = 53%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_emitLoopTM: 1204/2258 = 53%
   SAT.lean::satStreamRound  reproduces  SAT.lean::satStreamTail: 65/122 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_other: 152/287 = 53%
   Catalog.lean::f2_loopBorrow_step  reproduces  Loop.lean::loopReplay_step: 174/329 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Zone.lean::zoneCascadeRight_lengths  reproduces  Zone.lean::zoneSide_cascadeRight: 761/1444 = 53%
   MeyerTableau.lean::incFixed_enumWord  reproduces  MeyerTableau.lean::ctrVal_enumWord: 98/186 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   SAT.lean::satDrop_rewind  reproduces  SAT.lean::satDrop_skip: 269/512 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_transfer: 764/1459 = 52%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_triple_pair: 122/233 = 52%
   Catalog.lean::a2_map_setup  reproduces  Loop.lean::loopFuel_init: 214/410 = 52%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_payload_scan: 359/688 = 52%
   SAT.lean::satStreamPos_succ  reproduces  Catalog.lean::f2_splitPos_succ: 192/368 = 52%
   Loop.lean::emCall_track_stamp  reproduces  Simulation.lean::bufferedFirstCfg_init: 168/322 = 52%
   SAT.lean::satMax_prefix  reproduces  SAT.lean::satDrop_skip: 267/512 = 52%
   SAT.lean::satStop_clean  reproduces  Catalog.lean::a2_mapSetup_run: 85/163 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   SAT.lean::satStop_clean  reproduces  SAT.lean::sat_run_agree: 111/213 = 52%
   Embed.lean::embedThroughHalt  reproduces  SAT.lean::sat_run_agree: 111/213 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_prepare_final: 366/707 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_reject_run: 282/547 = 52%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Loop.lean::loopHost_fuel_return: 606/1176 = 52%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Loop.lean::loopHost_fuel_return: 606/1176 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 322/627 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Tautology.lean::taut_syntax_run  reproduces  Tautology.lean::taut_unary_run: 353/688 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   SAT.lean::satPair_copy  reproduces  Catalog.lean::f2_scanCopy_suffix: 444/868 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Loop.lean::loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   CfgRecord.lean::recordStep_read_fields  reproduces  CfgRecord.lean::recordStep_write_back: 1389/2734 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   TQBF.lean::codecRowOf_eq_iff  reproduces  TQBF.lean::codecObserve_congr: 165/326 = 51%
   SAT.lean::sat_run_agree  reproduces  Seam.lean::seamCompTM_runFrom_left: 85/168 = 51%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 322/637 = 51%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 322/637 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   SAT.lean::satDrop_copy  reproduces  Loop.lean::loopReplay_run: 174/345 = 50%
   Tautology.lean::tautDual_scan  reproduces  Tautology.lean::tautDual_copy_end: 176/349 = 50%
   SAT.lean::sat_pt_pair  reproduces  SAT.lean::sat_pt_append: 65/129 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Loop.lean::emCall_clear_run  reproduces  Loop.lean::emCall_clear_origin: 428/850 = 50%
   SAT.lean::satRed_maxLiteral  reproduces  SAT.lean::satRed_maxOnes: 505/1003 = 50%
   Loop.lean::emCall_track_computes  reproduces  Loop.lean::emCall_right_computes: 77/153 = 50%
   Loop.lean::emCall_right_computes  reproduces  Loop.lean::emCall_track_computes: 77/153 = 50%
   Catalog.lean::a2_mapVirtual  reproduces  VirtualInput.lean::vhostCfg: 91/181 = 50%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_inverse: 92/183 = 50%
   Catalog.lean::compareTM_run_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Loop.lean::loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Loop.lean::loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 666/1329 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Tautology.lean::taut_syntax_run  reproduces  SAT.lean::satStreamWord_length: 90/180 = 50%
   SAT.lean::satReq_fields  reproduces  SAT.lean::satStreamRead_word: 62/124 = 50%
```

### After

```text
declarations screened: 1508; copy pairs (target reproduces >= half of source): 873; reproduced text: 297,817 chars
   Catalog.lean::f2_loopBody_step  reproduces  Loop.lean::loopBody_step: 1094/1094 = 100%
   Loop.lean::loop_find_run  reproduces  Catalog.lean::f2_loop_find_run: 678/678 = 100%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_find_run: 678/678 = 100%
   Loop.lean::loop_halted_run  reproduces  Catalog.lean::a2_loop_halted_run: 659/659 = 100%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_halted_run: 659/659 = 100%
   Loop.lean::loop_rewind_bounded  reproduces  Catalog.lean::f2_loop_rewind_bounded: 514/514 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Loop.lean::loop_rewind_bounded: 514/514 = 100%
   Catalog.lean::f2_loopBody_run  reproduces  Loop.lean::loopBody_run: 452/452 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Loop.lean::loopBodyTM  reproduces  Catalog.lean::f2_loopBodyTM: 428/428 = 100%
   Catalog.lean::f2_loopBodyTM  reproduces  Loop.lean::loopBodyTM: 428/428 = 100%
   Catalog.lean::f2_loopFuel_init  reproduces  Loop.lean::loopFuel_init: 410/410 = 100%
   Loop.lean::loopBuffer_write  reproduces  Catalog.lean::f2_loopBuffer_write: 408/408 = 100%
   Catalog.lean::f2_loopBuffer_write  reproduces  Loop.lean::loopBuffer_write: 408/408 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::f2_loopBody_stop  reproduces  Loop.lean::loopBody_stop: 346/346 = 100%
   Catalog.lean::f2_loopReplay_run  reproduces  Loop.lean::loopReplay_run: 345/345 = 100%
   Loop.lean::loop_first_halt  reproduces  Catalog.lean::f2_loop_first_halt: 341/341 = 100%
   Catalog.lean::f2_loop_first_halt  reproduces  Loop.lean::loop_first_halt: 341/341 = 100%
   Catalog.lean::f2_loopCopy_erase  reproduces  Loop.lean::loopCopy_erase: 285/285 = 100%
   Loop.lean::loopFrame  reproduces  Catalog.lean::f2_loopFrame: 270/270 = 100%
   Catalog.lean::f2_loopFrame  reproduces  Loop.lean::loopFrame: 270/270 = 100%
   Loop.lean::loop_output_length_le  reproduces  Catalog.lean::f2_loop_output_length_le: 254/254 = 100%
   Catalog.lean::f2_loop_output_length_le  reproduces  Loop.lean::loop_output_length_le: 254/254 = 100%
   Catalog.lean::f2_loopFuel_run  reproduces  Loop.lean::loopFuel_run: 230/230 = 100%
   Loop.lean::loopBodyCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 212/212 = 100%
   Catalog.lean::f2_loopBodyCfg  reproduces  Loop.lean::loopBodyCfg: 212/212 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Loop.lean::loopControlAction  reproduces  Catalog.lean::f2_loopControlAction: 150/150 = 100%
   Catalog.lean::f2_loopControlAction  reproduces  Loop.lean::loopControlAction: 150/150 = 100%
   Catalog.lean::f2_loopCall  reproduces  Loop.lean::loopCall: 141/141 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::f2_loopValue_bits  reproduces  Loop.lean::loopValue_bits: 135/135 = 100%
   Loop.lean::loopReplayTM  reproduces  Catalog.lean::f2_loopReplayTM: 130/130 = 100%
   Catalog.lean::f2_loopReplayTM  reproduces  Loop.lean::loopReplayTM: 130/130 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Loop.lean::loopFuelSource  reproduces  Catalog.lean::f2_loopFuelSource: 122/122 = 100%
   Catalog.lean::f2_loopFuelSource  reproduces  Loop.lean::loopFuelSource: 122/122 = 100%
   Catalog.lean::f2_loopBodySource  reproduces  Loop.lean::loopBodySource: 119/119 = 100%
   Loop.lean::emCall_erase_last  reproduces  Catalog.lean::f2_catalogBuffer_erase: 118/118 = 100%
   Catalog.lean::f2_loopCopy_final  reproduces  Loop.lean::loopCopy_final: 110/110 = 100%
   Loop.lean::loop_orbit_inv  reproduces  Catalog.lean::f2_loop_orbit_inv: 94/94 = 100%
   Catalog.lean::f2_loop_orbit_inv  reproduces  Loop.lean::loop_orbit_inv: 94/94 = 100%
   Catalog.lean::f2_loopBorrowPos_le  reproduces  Loop.lean::loopBorrowPos_le: 93/93 = 100%
   Loop.lean::loopFuelCfg  reproduces  Catalog.lean::f2_loopFuelCfg: 90/90 = 100%
   Catalog.lean::f2_loopFuelCfg  reproduces  Loop.lean::loopFuelCfg: 90/90 = 100%
   Loop.lean::loopBuffer_read  reproduces  Catalog.lean::f2_loopBuffer_read: 89/89 = 100%
   Catalog.lean::f2_loopBuffer_read  reproduces  Loop.lean::loopBuffer_read: 89/89 = 100%
   Loop.lean::loop_fuel_width  reproduces  Catalog.lean::f2_loop_fuel_width: 87/87 = 100%
   Catalog.lean::f2_loop_fuel_width  reproduces  Loop.lean::loop_fuel_width: 87/87 = 100%
   Catalog.lean::f2_loopFrame_payload  reproduces  Loop.lean::loopFrame_payload: 79/79 = 100%
   Catalog.lean::f2_loopFlag_clear  reproduces  Loop.lean::loopFlag_clear: 60/60 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Loop.lean::loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Loop.lean::loopBody_run  reproduces  Catalog.lean::f2_loopBody_run: 452/455 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Catalog.lean::f2_loopHost_contracts  reproduces  Loop.lean::loopHost_contracts: 3565/3596 = 99%
   Loop.lean::loopBody_step  reproduces  Catalog.lean::f2_loopBody_step: 1094/1109 = 99%
   Loop.lean::loopBody_stop  reproduces  Catalog.lean::f2_loopBody_stop: 346/352 = 98%
   Loop.lean::loopReplay_run  reproduces  Catalog.lean::f2_loopReplay_run: 345/351 = 98%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   InputCall.lean::inputSeekRewind  reproduces  Inclusions.lean::b2b_rewindTM: 204/208 = 98%
   Catalog.lean::f2_loopHost  reproduces  Loop.lean::loopHostM: 2368/2417 = 98%
   Loop.lean::loopCopy_erase  reproduces  Catalog.lean::f2_loopCopy_erase: 285/291 = 98%
   Loop.lean::loopCall  reproduces  Catalog.lean::f2_loopCall: 141/144 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Tautology.lean::taut_syntax_double  reproduces  Tautology.lean::taut_syntax_separator: 416/426 = 98%
   Loop.lean::loopBodySource  reproduces  Catalog.lean::f2_loopBodySource: 119/122 = 98%
   SAT.lean::satClean_install  reproduces  SAT.lean::satClean_emit: 589/604 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Loop.lean::loopFuel_run  reproduces  Catalog.lean::f2_loopFuel_run: 230/236 = 97%
   Loop.lean::loopFuel_init  reproduces  Catalog.lean::f2_loopFuel_init: 410/422 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Zone.lean::zoneShiftOut  reproduces  Zone.lean::zoneShiftIn: 251/259 = 97%
   Loop.lean::loopBorrowPos_le  reproduces  Catalog.lean::f2_loopBorrowPos_le: 93/96 = 97%
   Tautology.lean::tautDual_valid  reproduces  Tautology.lean::tautDual_copy_end: 338/349 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Tautology.lean::taut_work_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Simulation.lean::bufferedScanCfg_run  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_maxFormula  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_maxClause  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_counterBack  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satPair_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_right_scan  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_finish_transfer  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_finish_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_finish_erase  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Loop.lean::emCall_finish_arg  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_splitRestore_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_rawStrip_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_extract_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_catalogPoly_setup  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_catalogPoly_emit  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Catalog.lean::f2_loopHost_replay  reproduces  Loop.lean::loopHost_replay: 1032/1069 = 97%
   Loop.lean::loopFrame_payload  reproduces  Catalog.lean::f2_loopFrame_payload: 79/82 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Loop.lean::loopHost_frame_replay: 888/923 = 96%
   Catalog.lean::f2_loopReplay_step  reproduces  Loop.lean::loopReplay_step: 316/329 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   SAT.lean::sat_pt_head  reproduces  SAT.lean::sat_pt_tail: 379/395 = 96%
   Tautology.lean::taut_syntax_separator  reproduces  Tautology.lean::taut_syntax_double: 416/434 = 96%
   Loop.lean::loopValue_bits  reproduces  Catalog.lean::f2_loopValue_bits: 135/141 = 96%
   Catalog.lean::f2_loopControl_payload  reproduces  Loop.lean::loopControl_payload: 235/246 = 96%
   SAT.lean::sat_pt_tail  reproduces  SAT.lean::sat_pt_head: 379/397 = 95%
   Zone.lean::zoneShiftIn  reproduces  Zone.lean::zoneShiftOut: 251/263 = 95%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   SAT.lean::satDrop_skip  reproduces  SAT.lean::satRed_one: 60/63 = 95%
   Loop.lean::loopFlag_clear  reproduces  Catalog.lean::f2_loopFlag_clear: 60/63 = 95%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_halted_run: 627/659 = 95%
   Loop.lean::loop_run  reproduces  Catalog.lean::a2_loop_halted_run: 627/659 = 95%
   Catalog.lean::f2_loopHost_accept  reproduces  Loop.lean::loopHost_accept: 2127/2238 = 95%
   Catalog.lean::f2_loopDebit_value  reproduces  Loop.lean::loopDebit_value: 187/197 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Loop.lean::loopHostM  reproduces  Catalog.lean::f2_loopHost: 2368/2495 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Loop.lean::loopCopy_final  reproduces  Catalog.lean::f2_loopCopy_final: 110/116 = 95%
   SAT.lean::satClean_emit  reproduces  SAT.lean::satClean_install: 589/623 = 95%
   SAT.lean::satVerdict_true_poly  reproduces  SAT.lean::satVerdict_false_poly: 381/403 = 95%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_bank_initial: 3070/3250 = 94%
   Loop.lean::loopControl_payload  reproduces  Catalog.lean::f2_loopControl_payload: 235/249 = 94%
   Loop.lean::loopHost_round  reproduces  Catalog.lean::f2_loopHost_round: 1989/2114 = 94%
   Catalog.lean::f2_loopDebit_success  reproduces  Loop.lean::loopDebit_success: 141/150 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::f2_exists_loopFind_space  reproduces  Loop.lean::exists_loopFindTM: 851/910 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Loop.lean::loopHost_replay  reproduces  Catalog.lean::f2_loopHost_replay: 1032/1105 = 93%
   Catalog.lean::f2_loopBodyPadded  reproduces  Loop.lean::loopBodyPadded: 137/147 = 93%
   Loop.lean::loopHost_frame_replay  reproduces  Catalog.lean::f2_loopHost_frame_replay: 888/953 = 93%
   Loop.lean::loop_first_halt  reproduces  SAT.lean::sat_call_first_halt: 307/330 = 93%
   Catalog.lean::f2_loop_first_halt  reproduces  SAT.lean::sat_call_first_halt: 307/330 = 93%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Loop.lean::loopReplay_step  reproduces  Catalog.lean::f2_loopReplay_step: 316/341 = 93%
   Loop.lean::loopHost_accept  reproduces  Catalog.lean::f2_loopHost_accept: 2127/2297 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Loop.lean::loopHost_borrow_run: 489/531 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::f2_loop_live_prefix  reproduces  SAT.lean::sat_live_prefix: 139/152 = 91%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Loop.lean::loopBodyPadded  reproduces  Catalog.lean::f2_loopBodyPadded: 137/150 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Catalog.lean::f2_loopHost_round  reproduces  Loop.lean::loopHost_round: 1989/2194 = 91%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Loop.lean::loopFuelCaptured_frame: 1423/1570 = 91%
   Tautology.lean::tautDual_copy  reproduces  Tautology.lean::tautDual_scan: 842/929 = 91%
   Tautology.lean::taut_syntax_unary  reproduces  Tautology.lean::taut_syntax_bad: 77/85 = 91%
   Simulation.lean::rewind_from_any  reproduces  Loop.lean::loop_rewind_bounded: 465/514 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Loop.lean::loopDebit_success  reproduces  Catalog.lean::f2_loopDebit_success: 141/156 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   SAT.lean::sat_call_first_halt  reproduces  Loop.lean::loop_first_halt: 307/341 = 90%
   SAT.lean::sat_call_first_halt  reproduces  Catalog.lean::f2_loop_first_halt: 307/341 = 90%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Loop.lean::loopHost_fuel_copy: 1319/1466 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   Loop.lean::loopHost_borrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 489/544 = 90%
   SAT.lean::satPairCfg  reproduces  SAT.lean::satEvalCfg: 131/146 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Loop.lean::loopHost_anchor_return: 829/926 = 90%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Catalog.lean::f2_exists_loopFind_space  reproduces  Loop.lean::exists_loopTM: 687/770 = 89%
   Tautology.lean::taut_split_exists  reproduces  SAT.lean::sat_split_exists: 123/138 = 89%
   SAT.lean::sat_live_prefix  reproduces  Catalog.lean::f2_loop_live_prefix: 139/156 = 89%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopTM: 686/770 = 89%
   Catalog.lean::f2_loopReady  reproduces  Loop.lean::loopReady: 119/134 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   SAT.lean::satEvalCfg  reproduces  SAT.lean::satPairCfg: 131/148 = 89%
   Catalog.lean::f2_splitCount_run  reproduces  Loop.lean::emCall_right_run: 152/172 = 88%
   Tautology.lean::tautDual_invalid  reproduces  Tautology.lean::tautDual_copy_end: 308/349 = 88%
   Loop.lean::loopDebit_value  reproduces  Catalog.lean::f2_loopDebit_value: 187/212 = 88%
   Catalog.lean::f2_catalogBuffer_erase  reproduces  Loop.lean::emCall_erase_last: 118/134 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Tautology.lean::tautSplit  reproduces  SAT.lean::satSplit: 65/74 = 88%
   SAT.lean::satSplit  reproduces  Tautology.lean::tautSplit: 65/74 = 88%
   Tautology.lean::tautDual_rewind  reproduces  Tautology.lean::tautDual_copy_end: 305/349 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Loop.lean::emCall_first_entry  reproduces  Catalog.lean::f2_catalogFirstEntry: 327/375 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Loop.lean::loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopFuelCaptured_frame: 1423/1639 = 87%
   Catalog.lean::f2_loopBodySource_run  reproduces  Loop.lean::loopBodySource_run: 78/90 = 87%
   Catalog.lean::f2_loopHost_borrow_step  reproduces  Loop.lean::loopHost_borrow_step: 581/671 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Loop.lean::loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 1319/1527 = 86%
   CfgRecord.lean::recordStep_reject_run  reproduces  CfgRecord.lean::recordStep_empty_run: 467/541 = 86%
   Loop.lean::loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_anchor_return: 829/963 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_rewind: 1025/1195 = 86%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_pair_triple: 138/161 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::f2_loopDebit_iterate_value  reproduces  Loop.lean::loopDebit_iterate_value: 248/290 = 86%
   SAT.lean::sat_split_exists  reproduces  Tautology.lean::taut_split_exists: 123/144 = 85%
   CfgRecord.lean::recordStep_empty_run  reproduces  CfgRecord.lean::recordStep_reject_run: 467/547 = 85%
   Loop.lean::loopReady  reproduces  Catalog.lean::f2_loopReady: 119/140 = 85%
   Loop.lean::loopHost_fuel_setup  reproduces  Catalog.lean::f2_loopHost_fuel_setup: 782/921 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   Catalog.lean::f2_loopHost_reject  reproduces  Loop.lean::loopHost_reject: 2023/2398 = 84%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CNF.lean::le_foldr_max_of_mem  reproduces  Tautology.lean::taut_le_max: 115/137 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_bank_final: 3070/3669 = 84%
   Catalog.lean::f2_loopHost_fuel_setup  reproduces  Loop.lean::loopHost_fuel_setup: 782/935 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Loop.lean::loopHost_fuel_return: 982/1176 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::f2_loopCopy_initial  reproduces  Loop.lean::loopCopy_initial: 78/94 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Loop.lean::loopHost_borrow_step  reproduces  Catalog.lean::f2_loopHost_borrow_step: 581/704 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   SAT.lean::satDrop_rewind  reproduces  SAT.lean::satDrop_dispatch: 256/311 = 82%
   Loop.lean::exists_emitCallTM  reproduces  Loop.lean::exists_installCallTM: 194/236 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Loop.lean::loopHost_contracts  reproduces  Catalog.lean::f2_loopHost_contracts: 3565/4347 = 82%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_reject_run: 448/547 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_loopHost_prepare  reproduces  Loop.lean::loopHost_prepare: 1091/1338 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Loop.lean::loopBodySource_run  reproduces  Catalog.lean::f2_loopBodySource_run: 78/96 = 81%
   Catalog.lean::f2_loopControl_apply  reproduces  Loop.lean::loopControl_apply: 643/792 = 81%
   Loop.lean::loopHost_reject  reproduces  Catalog.lean::f2_loopHost_reject: 2023/2493 = 81%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Loop.lean::emCall_first_entry: 327/403 = 81%
   Tautology.lean::tautDual_scan  reproduces  Tautology.lean::tautDual_copy: 842/1039 = 81%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopTM: 624/770 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   SAT.lean::satReq_round  reproduces  SAT.lean::satReq_fields: 93/115 = 81%
   Loop.lean::loopDebit_iterate_value  reproduces  Catalog.lean::f2_loopDebit_iterate_value: 248/308 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Zone.lean::zoneSide_cascadeRight  reproduces  Zone.lean::zoneCascadeRight_zero: 117/146 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   CNFEncoding.lean::parseClauses_bounds  reproduces  CNFEncoding.lean::parseClause_bounds: 731/920 = 79%
   Inclusions.lean::b2b_rewindTM  reproduces  InputCall.lean::inputSeekRewind: 204/257 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   SAT.lean::satMax_prefix  reproduces  SAT.lean::satMax_finish: 428/540 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_borrow_rewind: 932/1181 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   SAT.lean::satSplitClause_width  reproduces  SAT.lean::satSplitClause_vars: 67/85 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Loop.lean::emCall_finish_final  reproduces  Loop.lean::emCall_finish_initial: 1279/1629 = 79%
   InputCall.lean::inputSeekStep_run  reproduces  Games.lean::playOut_eq_iterate: 69/88 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Tautology.lean::taut_le_max  reproduces  CNF.lean::le_foldr_max_of_mem: 115/147 = 78%
   Loop.lean::exists_installCallTM  reproduces  Loop.lean::exists_emitCallTM: 194/248 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Loop.lean::loopCopy_initial  reproduces  Catalog.lean::f2_loopCopy_initial: 78/100 = 78%
   CfgRecord.lean::record_digits_value  reproduces  MeyerTableau.lean::ctrVal_enumWord: 145/186 = 78%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_reject_run: 426/547 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::f2_loopDebit_iterate_length  reproduces  Loop.lean::loopDebit_iterate_length: 68/88 = 77%
   Loop.lean::loopControl_apply  reproduces  Catalog.lean::f2_loopControl_apply: 643/834 = 77%
   SAT.lean::satPairAction_apply  reproduces  SAT.lean::satEvalAction_apply: 121/157 = 77%
   SAT.lean::satEvalAction_apply  reproduces  SAT.lean::satPairAction_apply: 121/157 = 77%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_erase: 972/1264 = 77%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::a2_mapSetup_run: 125/163 = 77%
   Loop.lean::loopHost_halt_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 389/508 = 77%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Loop.lean::loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Tautology.lean::tautDual_valid  reproduces  Tautology.lean::tautDual_invalid: 633/832 = 76%
   CNFEncoding.lean::parseClauses_repr  reproduces  CNFEncoding.lean::parseClause_repr: 380/501 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Loop.lean::exists_loopTM  reproduces  Loop.lean::exists_loopFindTM: 686/910 = 75%
   Zone.lean::zoneSide_shiftOutW  reproduces  Zone.lean::zoneSide_shiftInW: 296/394 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 879/1176 = 75%
   Loop.lean::loopDebit_iterate_length  reproduces  Catalog.lean::f2_loopDebit_iterate_length: 68/91 = 75%
   SAT.lean::satReqStep_poly  reproduces  SAT.lean::satReqEmit_poly: 333/446 = 75%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopFindTM: 679/910 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 879/1181 = 74%
   TQBF.lean::codecCnf_numVars  reproduces  TQBF.lean::codecCnfCost_relabel: 61/82 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_finish_final: 1279/1731 = 74%
   CNFEncoding.lean::parseClause_bounds  reproduces  CNFEncoding.lean::parseClauses_bounds: 731/992 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   CNFEncoding.lean::parseClause_repr  reproduces  CNFEncoding.lean::parseClauses_repr: 380/517 = 74%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Loop.lean::loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Loop.lean::loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Loop.lean::loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Loop.lean::emCall_right_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 125/171 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   CfgRecord.lean::recordStep_map_snapshot  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 875/1198 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Loop.lean::loopBuffer_read: 65/89 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   CNFEncoding.lean::numVars_le_of_literal_bounds  reproduces  CNF.lean::foldr_max_le_of_forall: 97/133 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Loop.lean::loopHost_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1091/1499 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Loop.lean::emCall_right_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Loop.lean::loopHost_start  reproduces  Catalog.lean::f2_loopHost_start: 209/289 = 72%
   Loop.lean::loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Loop.lean::loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_return: 982/1366 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Loop.lean::loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_arg: 1025/1438 = 71%
   Catalog.lean::f2_loopReady_call  reproduces  Loop.lean::loopReady_call: 708/994 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Loop.lean::emCall_right_run: 122/172 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   TQBF.lean::configurationValidity_size_raw  reproduces  TQBF.lean::configurationValidity_numVars: 68/96 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Loop.lean::loopReplayTM: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Loop.lean::loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 932/1329 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_reject_run: 383/547 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_inverse: 128/183 = 70%
   Zone.lean::zoneMoveRight  reproduces  Zone.lean::zoneMoveLeft: 265/379 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_rewind: 835/1195 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   SAT.lean::satReqStep  reproduces  SAT.lean::satReqEmit: 159/229 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Zone.lean::zoneMoveLeft  reproduces  Zone.lean::zoneMoveRight: 265/382 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   MeyerTableau.lean::wstep_some_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 79/114 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   CfgRecord.lean::recordStep_probe_run  reproduces  CfgRecord.lean::recordStep_read_run: 103/149 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Loop.lean::loopBody_step  reproduces  Loop.lean::loopBody_stop: 239/346 = 69%
   SAT.lean::satSplitClause_vars  reproduces  SAT.lean::satSplitClause_width: 67/97 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::f2_counterInc_bits  reproduces  Loop.lean::loopValue_bits: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Loop.lean::loopHost_init  reproduces  Catalog.lean::f2_loopHost_init: 65/95 = 68%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_empty_run: 370/541 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_input_rewind  reproduces  Loop.lean::loopHost_input_rewind: 164/241 = 68%
   Catalog.lean::skipBackTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 969/1430 = 68%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_arg: 972/1438 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   CNFEncoding.lean::parseClause_bounds  reproduces  CNFEncoding.lean::parseClause_repr: 336/501 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Loop.lean::loopHost_input_rewind  reproduces  Catalog.lean::f2_loopHost_input_rewind: 164/245 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   CNFEncoding.lean::parseClauses  reproduces  CNFEncoding.lean::parseClause: 117/175 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_inverse: 122/183 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Catalog.lean::f2_loopDebit  reproduces  Loop.lean::loopDebit: 62/93 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Loop.lean::loopReady_call  reproduces  Catalog.lean::f2_loopReady_call: 708/1066 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   SAT.lean::satEval_double  reproduces  SAT.lean::satEval_skip: 137/207 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_find_run: 448/678 = 66%
   Loop.lean::loop_run  reproduces  Catalog.lean::f2_loop_find_run: 448/678 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_erase: 835/1264 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_loopBody_step  reproduces  Loop.lean::loopBody_stop: 228/346 = 66%
   Inclusions.lean::b2b_callEmb  reproduces  Inclusions.lean::b2b_bankEmb: 67/102 = 66%
   Catalog.lean::f2_loopHost_init  reproduces  Loop.lean::loopHost_init: 65/99 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_empty_run: 355/541 = 66%
   Loop.lean::emCall_track_action  reproduces  Simulation.lean::bufferedFirstCfg_init: 211/322 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_empty_run: 353/541 = 65%
   SAT.lean::satMax_finish  reproduces  SAT.lean::satMax_prefix: 428/656 = 65%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_pair: 152/233 = 65%
   CNFEncoding.lean::parseClauses_bounds  reproduces  CNFEncoding.lean::parseClauses_repr: 337/517 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   SAT.lean::sat_pt_append  reproduces  SAT.lean::sat_pt_pair: 65/100 = 65%
   Loop.lean::loopBodyImage  reproduces  Loop.lean::emLoopCall: 87/134 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Loop.lean::loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 228/352 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_right_step: 134/207 = 65%
   Inclusions.lean::b2b_trialCfg  reproduces  Inclusions.lean::b2b_setupCfg: 119/184 = 65%
   Tautology.lean::taut_certificate_equiv  reproduces  SAT.lean::sat_certificate: 243/376 = 65%
   Catalog.lean::f2_loopCall_reframe  reproduces  Loop.lean::loopCall_reframe: 484/749 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_stamp: 450/698 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   Catalog.lean::f2_loopHost_release  reproduces  Loop.lean::loopHost_release: 524/815 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Zone.lean::zoneSide_shiftInW  reproduces  Zone.lean::zoneSide_shiftOutW: 296/462 = 64%
   Tautology.lean::tautDual_unary  reproduces  SAT.lean::satWidth_index: 62/97 = 64%
   SAT.lean::satStream_parseLit  reproduces  SAT.lean::satWidth_index: 62/97 = 64%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   SAT.lean::satAppend_copy  reproduces  SAT.lean::satAppend_seek: 528/832 = 63%
   Catalog.lean::a2_loop_prepare  reproduces  Loop.lean::loopHost_prepare: 849/1338 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Loop.lean::loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   Loop.lean::emCall_prepare_initial  reproduces  Inclusions.lean::b2b_embed_refl: 113/180 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   SAT.lean::satEval_start  reproduces  SAT.lean::satPair_start: 1086/1733 = 63%
   Loop.lean::loopDebit  reproduces  Catalog.lean::f2_loopDebit: 62/99 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Loop.lean::loopBodyDispatch  reproduces  Loop.lean::loopBodyImage: 118/190 = 62%
   TQBF.lean::b4mRank_progress  reproduces  TQBF.lean::b4mCarryRecords_done: 178/287 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   CNFEncoding.lean::parseClause  reproduces  CNFEncoding.lean::parseClauses: 117/189 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   SAT.lean::satRed_maxClause  reproduces  SAT.lean::sat_clause_measure: 67/109 = 61%
   SAT.lean::satEval_clause  reproduces  SAT.lean::sat_clause_measure: 67/109 = 61%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_payload_scan: 422/688 = 61%
   SAT.lean::sat_pt_unaryLength  reproduces  CNFEncoding.lean::takeTrues_repr: 76/124 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Tautology.lean::taut_eval_double  reproduces  Tautology.lean::taut_syntax_separator: 261/426 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   SAT.lean::satScan_step  reproduces  Catalog.lean::f2_scanStep_right: 100/164 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Loop.lean::loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Loop.lean::loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 288/476 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_erase: 764/1264 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_rewind: 722/1195 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Tautology.lean::taut_syntax_formula  reproduces  Tautology.lean::taut_syntax_clause: 381/633 = 60%
   Catalog.lean::f2_loopHost_borrow  reproduces  Loop.lean::loopHost_borrow: 258/429 = 60%
   Tautology.lean::taut_eval_double  reproduces  Tautology.lean::taut_syntax_double: 261/434 = 60%
   Tautology.lean::tautDual_invalid  reproduces  Tautology.lean::tautDual_valid: 633/1053 = 60%
   Loop.lean::loopHost_release  reproduces  Catalog.lean::f2_loopHost_release: 524/872 = 60%
   Catalog.lean::seekEndTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 859/1430 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Loop.lean::loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_reframe: 484/809 = 60%
   SAT.lean::satDrop_skip  reproduces  SAT.lean::satDrop_dispatch: 186/311 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopCfgTM: 95/159 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Loop.lean::loopCall  reproduces  Loop.lean::emLoopCall: 80/134 = 60%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_clear_heads: 124/208 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   CfgRecord.lean::recordStep_read_prefix  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 712/1198 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopTM: 457/770 = 59%
   Tautology.lean::taut_syntax_separator  reproduces  Tautology.lean::taut_eval_double: 261/440 = 59%
   Tautology.lean::taut_syntax_double  reproduces  Tautology.lean::taut_eval_double: 261/440 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_pair: 138/233 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   CfgRecord.lean::recordStep_restore_digits  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   CfgRecord.lean::recordStep_prepare_native  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Loop.lean::emCall_track_initial  reproduces  Simulation.lean::bufferedFirstCfg_init: 190/322 = 59%
   Catalog.lean::f2_loopCall  reproduces  Loop.lean::emLoopCall: 79/134 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   SAT.lean::satWidth_clause  reproduces  Tautology.lean::tautDual_clause: 142/242 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Tautology.lean::taut_syntax_clause  reproduces  Tautology.lean::taut_syntax_formula: 381/653 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   SAT.lean::satPair_start  reproduces  SAT.lean::satEval_start: 1086/1871 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   SAT.lean::satPad_run  reproduces  Catalog.lean::f2_splitEmbed_run: 109/188 = 58%
   Loop.lean::loopHost_borrow  reproduces  Catalog.lean::f2_loopHost_borrow: 258/445 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopCfgTM: 92/159 = 58%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_empty_run: 313/541 = 58%
   Loop.lean::emCall_clear_left  reproduces  Loop.lean::emCall_clear_scan: 369/638 = 58%
   SAT.lean::satPair_replay  reproduces  SAT.lean::satPair_rewind: 542/938 = 58%
   Catalog.lean::seekStartTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 825/1430 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Loop.lean::emCallTripleEmbedding  reproduces  Loop.lean::emCallPairEmbedding: 69/120 = 57%
   SAT.lean::satScanTM  reproduces  SAT.lean::satMapTM: 73/127 = 57%
   Loop.lean::emCall_track_stamp  reproduces  Loop.lean::emCall_track_initial: 398/693 = 57%
   CfgRecord.lean::recordStep_clear_snapshot  reproduces  CfgRecord.lean::recordStep_map_snapshot: 875/1525 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Loop.lean::emCall_prepare_final  reproduces  Inclusions.lean::b2b_embed_refl: 103/180 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_pair_triple: 92/161 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Loop.lean::loop_output_length_le: 145/254 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Tautology.lean::taut_copy_run  reproduces  Tautology.lean::taut_move_right: 69/121 = 57%
   Loop.lean::emCall_track_initial  reproduces  Loop.lean::emCall_track_stamp: 398/698 = 57%
   SAT.lean::satStreamStep_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 65/114 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Zone.lean::zoneStage_leftWindow  reproduces  Zone.lean::zoneStage_rightWindow: 266/467 = 57%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_arg: 819/1438 = 57%
   TQBF.lean::configurationAdjacency_bounds  reproduces  TQBF.lean::configurationInputEquality_bounds: 169/297 = 57%
   SAT.lean::satPair_rewind  reproduces  SAT.lean::satEval_rewind: 446/785 = 57%
   Loop.lean::emLoopCall  reproduces  Loop.lean::loopCall: 80/141 = 57%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_copyback_run: 1173/2070 = 57%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 666/1176 = 57%
   Tautology.lean::taut_syntax_bad  reproduces  Tautology.lean::taut_syntax_unary: 77/136 = 57%
   SAT.lean::satMax_finish  reproduces  SAT.lean::satDrop_dispatch: 176/311 = 57%
   CfgRecord.lean::RecordEqIndex  reproduces  CfgRecord.lean::RecordTestIndex: 73/129 = 57%
   SAT.lean::satStop_clean  reproduces  Seam.lean::seamCompTM_runFrom_left: 95/168 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Loop.lean::emCallPairIndex  reproduces  Loop.lean::emCallPairSelect: 61/108 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Loop.lean::loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Loop.lean::loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_transfer: 819/1459 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::catalogCopyF  reproduces  Scan.lean::scanWriteCfg: 113/202 = 56%
   Zone.lean::zoneSide_cascadeRight  reproduces  Zone.lean::zoneCascadeRight_blocked: 432/773 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   SAT.lean::satMapTM  reproduces  SAT.lean::satScanTM: 73/131 = 56%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_finish_initial: 904/1629 = 55%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Loop.lean::loopHost_halt_return: 389/701 = 55%
   TQBF.lean::configurationCodec_input_eq  reproduces  TQBF.lean::configurationCodec_eq_iff: 81/146 = 55%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 322/581 = 55%
   SAT.lean::satAppendTM  reproduces  Inclusions.lean::b2b_rewindTM: 115/208 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   CfgRecord.lean::RecordTestIndex  reproduces  CfgRecord.lean::RecordEqIndex: 73/133 = 55%
   Loop.lean::emLoopCall  reproduces  Catalog.lean::f2_loopCall: 79/144 = 55%
   Scan.lean::scanWriteCfg  reproduces  Catalog.lean::catalogCopyF: 113/206 = 55%
   CNFEncoding.lean::parseClauses_serialize  reproduces  CNFEncoding.lean::parseClause_serializeClause: 402/733 = 55%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Loop.lean::emCall_first_entry: 221/403 = 55%
   SAT.lean::satPad_run  reproduces  Seam.lean::seamRelease_step_right: 74/135 = 55%
   SAT.lean::satPad_run  reproduces  Seam.lean::seamComp_step_right: 74/135 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   Loop.lean::loopHost_body_run  reproduces  Catalog.lean::f2_loopHost_body_capture: 64/117 = 55%
   Loop.lean::loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 203/372 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Catalog.lean::f2_loopBorrow_run  reproduces  Loop.lean::loopHost_borrow_run: 288/531 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Loop.lean::loopReplay_run: 187/345 = 54%
   CfgRecord.lean::recordRun_trans  reproduces  Tautology.lean::tautDual_segment_add: 91/168 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   SAT.lean::satAppend_rewind  reproduces  SAT.lean::satAppend_seek: 450/832 = 54%
   Loop.lean::loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 285/527 = 54%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopFindTM: 491/910 = 54%
   SAT.lean::satStreamRead_word  reproduces  SAT.lean::satReq_fields: 62/115 = 54%
   SAT.lean::satMap_run  reproduces  SAT.lean::satScan_run: 269/499 = 54%
   Loop.lean::emCallPairEmbedding  reproduces  Loop.lean::emCallTripleEmbedding: 69/128 = 54%
   Loop.lean::emCall_track_run  reproduces  Loop.lean::emCall_track_extent: 145/269 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SAT.lean::satWidth_formula  reproduces  Tautology.lean::tautDual_serialize: 167/310 = 54%
   MeyerTableau.lean::RW_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   MeyerTableau.lean::RI_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   CNFEncoding.lean::parseClause_serializeClause  reproduces  CNFEncoding.lean::parseClauses_serialize: 402/747 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 633/1181 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   SAT.lean::satReq_fields_poly  reproduces  SAT.lean::sat_pt_append: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_initial: 370/693 = 53%
   SAT.lean::satEvalTM  reproduces  Inclusions.lean::b2b_rewindTM: 111/208 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_prepare_final: 377/707 = 53%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_emitLoopTM: 1204/2258 = 53%
   SAT.lean::satStreamRound  reproduces  SAT.lean::satStreamTail: 65/122 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   TQBF.lean::b4mBack_run  reproduces  TQBF.lean::b4mCarryRecords_quants: 91/171 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_other: 152/287 = 53%
   Catalog.lean::f2_loopBorrow_step  reproduces  Loop.lean::loopReplay_step: 174/329 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Zone.lean::zoneCascadeRight_lengths  reproduces  Zone.lean::zoneSide_cascadeRight: 761/1444 = 53%
   MeyerTableau.lean::incFixed_enumWord  reproduces  MeyerTableau.lean::ctrVal_enumWord: 98/186 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   SAT.lean::satDrop_rewind  reproduces  SAT.lean::satDrop_skip: 269/512 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_transfer: 764/1459 = 52%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_triple_pair: 122/233 = 52%
   Catalog.lean::a2_map_setup  reproduces  Loop.lean::loopFuel_init: 214/410 = 52%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_payload_scan: 359/688 = 52%
   SAT.lean::satStreamPos_succ  reproduces  Catalog.lean::f2_splitPos_succ: 192/368 = 52%
   Loop.lean::emCall_track_stamp  reproduces  Simulation.lean::bufferedFirstCfg_init: 168/322 = 52%
   SAT.lean::satMax_prefix  reproduces  SAT.lean::satDrop_skip: 267/512 = 52%
   SAT.lean::satStop_clean  reproduces  Catalog.lean::a2_mapSetup_run: 85/163 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   SAT.lean::satStop_clean  reproduces  SAT.lean::sat_run_agree: 111/213 = 52%
   Embed.lean::embedThroughHalt  reproduces  SAT.lean::sat_run_agree: 111/213 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_prepare_final: 366/707 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_reject_run: 282/547 = 52%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Loop.lean::loopHost_fuel_return: 606/1176 = 52%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Loop.lean::loopHost_fuel_return: 606/1176 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 322/627 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Tautology.lean::taut_syntax_run  reproduces  Tautology.lean::taut_unary_run: 353/688 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   SAT.lean::satPair_copy  reproduces  Catalog.lean::f2_scanCopy_suffix: 444/868 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Loop.lean::loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   CfgRecord.lean::recordStep_read_fields  reproduces  CfgRecord.lean::recordStep_write_back: 1389/2734 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   TQBF.lean::codecRowOf_eq_iff  reproduces  TQBF.lean::codecObserve_congr: 165/326 = 51%
   SAT.lean::sat_run_agree  reproduces  Seam.lean::seamCompTM_runFrom_left: 85/168 = 51%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 322/637 = 51%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 322/637 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   SAT.lean::satDrop_copy  reproduces  Loop.lean::loopReplay_run: 174/345 = 50%
   Tautology.lean::tautDual_scan  reproduces  Tautology.lean::tautDual_copy_end: 176/349 = 50%
   SAT.lean::sat_pt_pair  reproduces  SAT.lean::sat_pt_append: 65/129 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Loop.lean::emCall_clear_run  reproduces  Loop.lean::emCall_clear_origin: 428/850 = 50%
   SAT.lean::satRed_maxLiteral  reproduces  SAT.lean::satRed_maxOnes: 505/1003 = 50%
   Loop.lean::emCall_track_computes  reproduces  Loop.lean::emCall_right_computes: 77/153 = 50%
   Loop.lean::emCall_right_computes  reproduces  Loop.lean::emCall_track_computes: 77/153 = 50%
   Catalog.lean::a2_mapVirtual  reproduces  VirtualInput.lean::vhostCfg: 91/181 = 50%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_inverse: 92/183 = 50%
   Catalog.lean::compareTM_run_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Loop.lean::loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Loop.lean::loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 666/1329 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Tautology.lean::taut_syntax_run  reproduces  SAT.lean::satStreamWord_length: 90/180 = 50%
   SAT.lean::satReq_fields  reproduces  SAT.lean::satStreamRead_word: 62/124 = 50%
```
