# P3 continuation frontier

Status: target 14 is filled. Target 15, `computesFunInTime_splitSolve`, retains its original admitted body. This is a partial checkpoint, not library closure.

Required P3 base: `b2f464197cfd071ff46b3f89aa611285d3983908`.
Checkpoint: `aa1bad68313cb2bcdb0e8c6245c2b31ae3616063`.
All source changes are in `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
The next maintainer brief controls the next exact integrated base; this document authorizes no different branch or statement changes.

## Completed target 14

`computesFunInTime_pairMapSnd` is proved, with coefficient 40 and no admission dependency. Its source is `pairMapTM (bufferedCompTM (pairExtractTM false true) Mg)`.

The exact phase lemmas are:

- `mapStart`: capture the actual-payload computation on the original input, rewind the capture, and rewind the native input. Physical output is empty at the validator entry.
- `mapValidate`: silent aligned validation, in at most the unread input length plus one. Malformed inputs halt with empty output; valid inputs reach the second native-input rewind.
- `catalogRewind`: the second native-input rewind, instantiated in `pairMap_computes`.
- `mapPrefix_replay`: emit the original doubled first component and separator, in exactly twice the first-component length plus two steps. The captured payload head stays at zero.
- `mapPayload_replay` / `mapPayload_finish`: replay the captured result once, then halt on its right blank.
- `pairMap_computes`: assemble those phases at `4 * (T n + n + 3)` for a total source with time bound `T`.

The public proof invokes `catalogPayload_computes hg hTg`, whose source time is `6 * (n+1) + Tg n + 1`. Substitution gives at most `40 * (n+1+Tg n)`. The completed proof never substitutes a padded argument into `Tg`.

## Checked target-15 components

These are separate proved components. They are not yet an instantiated body satisfying `hround`.

### Semantic and loop closure

- `splitStep` is exactly the audited append-or-stall function, preserving all existing bits.
- `splitAccept` is the audited length equation as a Boolean.
- `splitStep_inv` proves closure of the original length-only invariant, for arbitrary bit patterns.
- `splitStep_orbit` proves the unary orbit through the one-past-end state.
- `splitFind_eq`, `splitFind_none`, and `splitLoop_result` identify the finite search, its failure branch, and the payload with `solveSplit`.
- `splitLoop_bound` proves the final exponent calculation.
- `splitSolve_of_body` calls the proved `exists_loopFindTM`. It obtains the existing `lengthBits` fuel machine, enlarges the body coefficient to cover its bound, discharges `hInv0` and `hInvStep`, and transfers the loop's result and time bound. Its two explicit missing arguments are the actual `hstart` and `hround` proofs. It is a conditional, admission-free theorem; it supplies no missing body existence claim.

### Candidate preparation

`splitPrepareTM k` uses tape zero for the candidate and `k` scratch tapes. The candidate may contain arbitrary bits.

`splitPrepare_run` starts from `Cfg.ofWords (0,false) (stateWord (k+1) s)` and runs exactly `2*(s.length+1)` silent steps. It preserves the candidate, fills every scratch tape with `s.length+1` trues, and restores all work heads to zero. The native input head is `splitPos w s.length`; the finite flag records whether the candidate length already exceeded the native input length.

`splitPrepare_first` supplies the same endpoint at the first visit to its return state. It supports a host embedding that intercepts that return.

### Counted evaluation

`splitCountAction`, `splitCountCfg`, `splitCount_apply`, and `splitCount_run` are a generic source-to-host correspondence. The source has empty virtual input and arbitrary initialized source tapes. It occupies the successor-indexed work tapes; tape zero retains the candidate at head zero.

The host suppresses every source emission and instead consumes one native input cell. The native head saturates at the right boundary. A finite flag records consumption past that boundary. The counted amount is the candidate length plus the source's output length. The correspondence includes an emission on the halting transition.

`splitCount_accept` proves that blank native input together with no overflow is exactly equality of the counted amount and the native input length.

`splitCount_firstHalt` removes any padded halted suffix of a source time bound, retains the exact source-bank endpoint, and reaches the host return state at the first source halt. A host must still discharge its transition-table agreement argument.

For positive exponent, `splitPoly_loop_end` supplies the exact endpoint of the existing generator's nested-loop phase on a unary scratch bank of side length `s.length+1`: output length `C*(s.length+1)^(c+1)`, all source work heads back at zero, unary tapes unchanged, halted in `catalogPolyCost (s.length+1) C (c+1)+1` steps. Use `e=c+1`, not an off-by-one loop depth.

For exponent zero, an available route is `catalogPrefixTM (List.replicate C true)` on the empty virtual input: the existing `catalogPrefixTM_computes` yields exactly the constant unary output in `C+1` steps, and there are no source scratch tapes. This has not yet been packaged into the combined body.

### Exact rejection restoration

`splitRestoreTM k` starts at `splitRestoreScan k w s 0`: native input at origin, candidate unchanged at work-head zero, and every scratch tape holding `s.length+1` trues at head zero.

`splitRestore_run` clears every scratch tape, appends a true to the candidate exactly when its old length is at most the input length, and restores the native input and every work head. Its endpoint is exactly

```lean
Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s))
```

Its bound is `2*s.length+w.length+5`. It preserves arbitrary candidate bits. Thus the one-past-end case is a silent stall at the same word, not a replacement of arbitrary bits by trues.

`splitRestore_first` strengthens this to positive duration and no earlier visit to the return state. This is the local restoration component's first-return property; it has not yet been lifted to the complete body's anchor property.

`catalogFirstEntry` is the shared absorption argument used to expose these first-return endpoints.

## Work still required

1. Construct the combined finite body, with disjoint control phases and the candidate on tape zero. Keep all helpers private in the owned file.
2. Establish its genuine startup seam. A body whose start state is the anchor and whose initial candidate is empty can have startup time zero, but prove the exact `Cfg.ofWords` equation.
3. Embed preparation and transfer its return state to counted evaluation. Prove the configuration seam, including tape ordering, source initialized-bank configuration, zero work heads, native head, flag, and empty physical output.
4. Embed the appropriate source for positive and zero exponent; discharge `splitCount_run` / `splitCount_firstHalt` table agreement.
5. After evaluation, branch on the checked acceptance predicate and rewind the native input to its origin. The candidate head is already zero; the polynomial source endpoint has every source head zero.
6. On acceptance, implement and prove an emitter for `pairEncode (w.take s.length) (w.drop s.length)`. Use the candidate only as a length counter: emit native-input bits, not candidate bits. No acceptance emitter or accepting-round proof is present in this checkpoint.
7. On rejection, identify the configuration with `splitRestoreScan k w s 0`, invoke the checked cleanup, and map its return state to the body's anchor.
8. Prove the combined round's positive duration and strict-interior anchor exclusion across every phase. The standalone components' first-return lemmas do not by themselves prove this global condition.
9. Derive one common body coefficient for `A*(n+1)^(e+1)`, using the invariant to bound candidate length, `catalogPolyCost_le` for evaluation, and the actual scan/emission overheads of the completed controller. No complete body-envelope proof is delivered.
10. Apply `splitSolve_of_body`, remove the original target-15 admission, and rerun the required checks with empty expected root sets for all fifteen targets.

Do not reuse the old coarse-composition mistake for target 14, weaken the frozen statements, silently restrict the invariant to unary words, or count the conditional `splitSolve_of_body` theorem as a body construction.

## Verification state

The fresh 57-module sweep passes with zero errors. All fourteen completed primitive contracts, all eight wrapper/loop contracts, and all fifty-five new private declarations have only standard axioms. Traversing all 984 checked Build declarations finds exactly one admission root: the unchanged `computesFunInTime_splitSolve`.

`PrimitiveAxioms.lean` deliberately retains that one expected root for this partial checkpoint. The closure requirement is not met until it is changed to an empty root set and the body proof passes. The other 28 campaign admission warnings are out of scope and unchanged.

Notation: `w` is native input; `s` is the candidate; `n` is native input length; `k` is the number of source scratch tapes; `C` and `e` are the frozen polynomial parameters; `c` is the positive-exponent generator index, with `e=c+1`; `A` is the body-envelope coefficient; `T` is a source running-time bound; `Tg` is the given payload time bound.
