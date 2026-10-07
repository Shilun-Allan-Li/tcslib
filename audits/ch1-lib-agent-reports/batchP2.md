# Batch P2 — partial continuation delivery

**Targets 12–13 are filled; targets 14–15 remain pending.** Together with the
integrated first eleven targets, the primitive catalog now has 13 of 15 filled.
This is the partial checkpoint allowed by `briefs/lib-fill-batchP2.md`, not a
completed P2 batch. The exact continuation frontier is target 14,
`computesFunInTime_pairMapSnd`; target 15's concrete loop body is not supplied.

## Repository, base, and delivery

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required source branch: `complexity/arora-barak-ch1`.
- Required base: `90273dd6dea2f9e092ca7d4b5ab5dc72c96ef1ee`.
- The source branch was checked out first. Its observed head was
  `646b9ee6b482867cb588a67f3014dcc00ebac7d5`; the brief at that head pinned
  the older integrated checkpoint above, verified to be its ancestor.
- Working branch: `fill/lib-P2`, created from exactly the required base as
  directed by the brief. No existing branch was modified.
- Delivery commit: `f4167fc821188ef5c8ae65d340f477a3e794aa95`.
- Two commits/patches: `d94dfe8c` (target 12), `f4167fc8` (target 13 and
  proved target-14 relocation support).
- The only changed repository path is `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
- No push or PR. The worktree is clean.

## Target ledger

| Target | Status | Construction and reused assets | Buffer-before-emit discharge |
|---|---|---|---|
| 12: `computesFunInTime_pairLenCheck` | Filled, admission-free | Existing `pairFst`/`pairExtractTM` composed with `polyUnary`/`catalogPolyUnaryTM`, then new `pairCountTM`. `capture_run` stores the generated bound; `catalogRewind`, `lenParse_run`, and `lenSuffix_run` perform the native-input comparison. | The extractor validates before writing its intermediate output; composition and `lenStart` capture it silently. The final parser emits only a terminal verdict. Malformed input produces `[false]`. |
| 13: `computesFunInTime_stripLast` | Filled, admission-free | Existing `pairSnd`/`pairExtractTM`, new `anyTrueTM`, proved `computesFunInTime_cond`, and new `rawStripTM`. Its copy, rewind, and replay invariants adapt the in-file extractor's invariant pattern. `catalogMarker_cases` proves the exact `reverse.dropWhile` semantics. | The guard establishes a valid payload containing a true bit. The successful branch silently buffers the whole original encoding, locates and erases its final marker/false-run, then replays. Invalid pairs and all-false payloads select the empty-output branch. |
| 14: `computesFunInTime_pairMapSnd` | Pending; original `sorry` unchanged | New, fully proved `catalogPayload_length` and `catalogPayload_computes` supply the relocated payload run at the required time scale. The retained-prefix/captured-output host is still missing. | No claim of a completed threaded-map controller. |
| 15: `computesFunInTime_splitSolve` | Pending; original `sorry` unchanged | The prescribed `exists_loopFindTM` instance and body remain continuation work. | No claim that candidate evaluation, restoration, stall, or anchor obligations have been filled. |

Targets were filled in order. No incomplete helper, new admission, speculative
controller, axiom, or alteration of a frozen statement is included. All existing
first-eleven proof bodies remain unchanged.

## Construction details and route adaptations

For target 12 the generator receives the first extractor's buffered output. The
proved timed composition controls the budget in that buffer's length, absorbing
the extractor's linear bound into the fixed polynomial coefficient without
changing the exponent. The captured generator may run even on malformed input;
the subsequent aligned parser still emits exactly `[false]`, with no earlier
physical output. Coefficient zero, degree zero, empty components, and a zero
countdown are covered by the formal proof.

For target 13 the successful branch strips the *whole encoding* after the guard
has proved that the last true is in the payload. `catalogPair_inverse` and
`catalogMarker_cases` show that the unchanged pairing prefix survives exactly.
This implements the audited reverse-sweep route with whole-encoding buffering
instead of separate component buffers. `rawStrip_trim` proves the two right-end
recurrences directly from `splitAtLastTrue`'s `reverse.dropWhile` definition.
The underlying construction is linear; its bound is weakened to the frozen
quadratic envelope.

The module docstring has one appended implementation note describing these
adaptations and the partial status. All 15 original public docstrings are
byte-identical. No other module's private declaration is cited. `catalogRewind`
adapts the wrapper's `timed_rewind` proof pattern using public `rewind_scan`.

For target 14, `catalogPayload_computes` deliberately uses the public
`bufferedComp_start` and `bufferedSecondCfg_run` directly. They implement
relocation through `bufferTape`/`virtualMove`. Its time is
`6 * (n + 1) + Tg n + 1`; the payload length is at most `n`, including malformed
input's empty default. Applying only the coarse public timed-composition bound
would instead evaluate `Tg` at the extractor's running-time bound, which cannot
be absorbed into a constant multiple of `Tg n` for arbitrary monotone `Tg`.

## Target-15 hypothesis map: outstanding, not asserted discharged

| Obligation | Status and required continuation |
|---|---|
| `hF` | Must instantiate `computesFunInTime_lengthBits` at fuel `R n = n`, then enlarge its linear budget to the common body envelope. The existing theorem remains available; this instance has not been written. |
| `hInv0` | Must prove the empty candidate satisfies the specified length invariant. |
| `hInvStep` | Must prove append-or-stall preserves the invariant, including length `n+1`. |
| `hstart` | Concrete body startup and its seam equation remain missing. |
| `hround` | Concrete bounded round, accepting payload, rejected scratch restoration, no-interior-anchor proof, and positive-time stall remain missing. |
| Final orbit/output/budget bridge | Must identify the unary orbit with the range search and prove the frozen exponent-`e+2` envelope through `exists_loopFindTM`. |

The sanctioned root `Turing.FinTM.loopHost_contracts` is **unused** by this
checkpoint's completed proofs. It is not used to disguise either pending target.

## Verification

- Pinned Lean: `Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5115bdeec5f609e9126cce00f51ae88b3, Release)`.
- Pinned mathlib checked against its actual Git checkout:
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- `lake build` was never invoked. `lake exe cache get` was attempted once but
  failed at executable-location detection before downloading. An existing local
  cache at the exact dependency pins was copied into the isolated checkout.
- This runner exposes a PID namespace that differs from its `/proc` mount.
  Lean 4.25 asks for `/proc/<getpid()>/exe`, which therefore fails even though
  `/proc/self/exe` works. The supplied `proc_self_compat.c` maps only that exact
  self-reference to `/proc/self/exe`; all other calls are unchanged. It does not
  modify Lean, its kernel, the source, or the dependency pins. The pinned release
  binaries then execute normally. Reproduction on an ordinary host needs no shim.
- The 57-module order was bootstrapped. The owned module was checked during
  proof development; the final full sweep also checks every later module.
- **Final full fresh sweep:** 57 modules in exact committed order; fresh output
  directory; exit 0; zero `error:` lines; all 57 nonempty fresh oleans verified.
- Final admission-warning count: **31** = one out-of-scope Loop admission,
  two unchanged pending primitive targets, and 28 other campaign admissions.
- Final owned-module check has exactly two admission warnings and no other
  warnings.
- **Axiom traversal:** all 15 targets printed; the 13 completed targets and all
  29 new private declarations have empty admission-root sets. `capture_run` is
  also checked admission-free. The two pending targets each have exactly their
  own unchanged declaration root. No unexpected axiom appears.
- The walker uses checked kernel declarations, including types, opaque values,
  and inductive constructors, and rejects unexpected roots and axioms.
- **Statement freeze:** all 69 existing declarations retain their signatures;
  only the proof bodies of targets 12 and 13 changed. Every other existing body
  is unchanged. Existing declaration order is unchanged; no public declaration
  is gained, lost, or reordered; all 15 public docstrings are byte-identical.
- **Lint:** 0 FAIL, 2 WARN over the four Build files. One warning is the unchanged
  Loop file's size; the other is the owned file's size, justified below.
- `git diff --check` passes; ownership is confined to `Primitives.lean`.
- Both patches apply in order to the pinned base source and reproduce the
  checked source byte-for-byte. The incremental bundle passes `git bundle verify`.

### Final sweep tail

```text
MODULE 52/57 TCSlib/Complexity/TuringMachine
MODULE 53/57 TCSlib/Complexity/ClassP
MODULE 54/57 TCSlib/Complexity/Uncomputability
MODULE 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57 elapsed_seconds=146.4
```

### Axiom prints

```text
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairDup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairConcat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Full root results are in `verification/axioms.log`; freeze hashes and helper
inventory are in `verification/freeze.json`.

## Requests, size, and continuation

**Statement escalations: none. Requested shared lemmas: none.**

Final file size: **2504 lines**, compared with 1,687 at the
required base. Exclusive ownership keeps all finite controllers and simulation
invariants private in this file. The 29 new private declarations share the
existing parser/generator machinery and do not move code to other modules. The
larger size is recorded as the continuation of the brief's existing size
exception for the maintainer's decision log.

`CONTINUATION.md` records the exact target-14 frontier, the proved relocation
interface, and target-15's remaining obligations. The new helper inventory is
complete below. Generated Lean auxiliaries are covered by the kernel traversal.

## All new explicit private declarations

| Kind | Declaration |
|---|---|
| def | `lenAction` |
| def | `pairCountTM` |
| def | `lenCfg` |
| lemma | `lenCfg_read` |
| lemma | `lenAction_apply` |
| lemma | `lenSuffix_run` |
| lemma | `lenParse_first` |
| lemma | `lenParse_block` |
| lemma | `lenParse_run` |
| lemma | `catalogRewind` |
| lemma | `lenStart` |
| lemma | `pairCount_computes` |
| def | `rawStripTM` |
| def | `stripCfg` |
| lemma | `catalogBuffer_erase` |
| lemma | `rawStrip_copy` |
| lemma | `rawStrip_rewind` |
| lemma | `rawStrip_replay` |
| lemma | `rawStrip_finish` |
| lemma | `rawStrip_erase` |
| lemma | `rawStrip_trim` |
| lemma | `rawStrip_computes` |
| def | `anyTrueTM` |
| lemma | `anyTrue_run` |
| lemma | `anyTrue_computes` |
| lemma | `catalogPair_inverse` |
| lemma | `catalogMarker_cases` |
| lemma | `catalogPayload_length` |
| lemma | `catalogPayload_computes` |

## Integration

Verify `SHA256SUMS`, then apply the two patches in order with `git am -3` onto
the intended campaign checkpoint. Do not substitute another base silently.
The integrated source must have SHA-256:

`b3fe72dc57efaf817ce5da01ed27361ed37dea72e3cecaa6dedb5d650c124359`

Re-run the 57-module checker and the supplied axiom traversal on the fresh output
tree. The archive contains source, patches, incremental bundle, this report,
continuation notes, checksums, logs, and verification programs; it does not ship
cached oleans or the copied toolchain.

**Notation glossary.** `n` is physical input length; `Tg` is the target-14
hypothesis's monotone time function; `R` is target-15 fuel; `e` is its frozen
polynomial exponent. All other code identifiers name the committed contracts or
private declarations listed above.
