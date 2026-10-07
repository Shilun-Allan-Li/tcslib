# Chapter 2, E2 continuation, batch B2 — complete

**COMPLETE: both owned targets are proved; the full axiom gate passes.**

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested source branch: `complexity/arora-barak-ch1`.
- Required and actual source base: `e72d95bf35ebf09c21aae7e1959e5d895a345686`.
- Working branch: `fill/ch2-e2cont-B2`.
- Delivery commit: `022cd0f3cf63689b866cc0e7407db62f7e14cc77`.
- The B2 brief was read from branch tip `312a9a5b21ae84953295431a291102b3f0557ff5`,
  then the working branch was created at the brief's required base. The original
  source-branch ref was not moved. No push or PR. Single-agent execution.
- Only tracked source changed: `TCSlib/Complexity/ClassNP/Nondeterminism.lean`.

## Targets

| Order | Target | Result |
|---|---|---|
| 1 | `NP_subset_iUnion_NTIME` | Proved by the integrated native reverse host, `b2_compile`, and the inherited `cont_guess_normalize`. |
| 2 | `NP_eq_iUnion_NTIME` | Proved afterwards by antisymmetry and `ntime_poly_subset_NP`. |

The forward compiler and all 68 inherited private declarations are byte-identical.
No new public declarations, imports, assumptions, or admissions were introduced.

## Binding five-step contract

| Step | Discharging declarations and exact behavior |
|---|---|
| 1. Preserve the input and install a length-only scheduler | `b2Host`, `b2Slots`, `b2_initial`, `b2_copy_step`, `b2_copy_run`, `b2_copy_done`, `b2_rewind_step`, `b2_rewind_done`, `b2_rewind_run`, `b2_start`. The host copies the original word into its assembly buffer and returns the physical input head to one in exactly `2*|x|+2` steps. Both machine banks are blank. `b2UnaryTM`, `b2_unary_read`, `b2_unary_apply`, `b2_unary_step`, `b2_unary_run`, `b2_unary_initial`, `b2_unary_computes`, `b2_unary_mask`, and `b2_unary_first` close the missing scheduler-input seam by exact read normalization. |
| 2. Physical-position extraction and coverage | `b2_guess_step`, `b2_guess_run`, `b2_guess_word_injective`, `b2_guess_coverage`, `b2_host_contract`. Coverage explicitly invokes the inherited `cont_guess_coverage` at the actual first scheduler halt. Full branch words consist of a startup prefix, the scheduler interval, and a completion suffix. Only marked emission positions inside the scheduler interval supply guesses; the startup offset is `2*|x|+2`. |
| 3. Assemble, initialize, simulate, and capture | Guesses append directly after the copied original word, giving exactly `x++u` without a second copy. `b2_guess_return`, `b2_ready_step`, `b2_ready_done`, `b2_ready_run`, `b2_assembly` rewind this word and install `M.tm.initCfg (x++u)` with virtual input head one, blank verifier tapes, and empty captured output. `b2_verify_step` and `b2_verify_run` preserve guarded reads and clamping, all verifier work tapes, and every emission. `b2_verify_finish` emits precisely one verdict. `b2_tables_coincide` proves that both tables are definitionally the same outside live guessing states, for all symbol tuples. |
| 4. All-branch totality and acceptance equivalence | `b2_verify_timed`, `b2_finish`, `b2_host_contract`, `b2_compile`. Every sufficiently long branch yields a certificate of exactly the prescribed length and halts with the verifier's singleton decision bit. Conversely every such certificate is realized. The final verifier may halt at different actual times on different certificates; all branches satisfy the same upper bound, and extra choices are absorbed. |
| 5. Envelope and final normalization | `b2_host_bound` proves the entire native ledger is bounded by `(B+A+5)*(n+Q(n)+1)^(c+d+1)`. `b2_compile` packages the all-branch decider. The unchanged `cont_guess_normalize` applies its exact coefficient/exponent normalization and acceptance padding/truncation. |

### Scheduler-input seam and actual dispatch

`b2UnaryTM` changes only the scheduler's input reads: `some false` and
`some true` both become `some true`, while `none` remains `none`. It does
not change the physical input, work symbols, or input-head motion.
`b2UnaryCfg` identifies every configuration with one on the unary input of
the same length. `b2_unary_run` proves exact lockstep at **every elapsed
time**, and `b2_unary_mask` identifies the emission schedules.

The library's timed unary generator provides the scheduler. `b2_unary_first`
chooses its first halt on the unary word, with a bound from that generator,
and proves that the normalized scheduler on every original word of that
length has the same first halt. The host uses the scheduler's actual
completed state, followed by `b2_guess_return`, to dispatch. A polynomial
upper bound is never treated as an executable clock. The inherited
standalone phase's live return state is not mistaken for a halted decider.

The generator's emissions implement the prescribed number of guesses. Its
source/control bank cannot read the guessed buffer. This is the length-only
scheduler route in the B2 brief, rather than a claim that the library's
function-level contract alone makes arbitrary-input timing independent of
input values.

### Physical choices and edge cases

At input length `n`, the first `2n+2` physical choices are administrative.
The next `τ(n)` choices are interpreted by the emission mask of the unary
scheduler's first-halt run. The inherited selection and coverage proofs,
transferred by `b2_guess_coverage`, realize every word of length `Q(n)`.
All later physical choices are ignored by the deterministic completion.

When `C=0`, the scheduler emits no bits, so its mask has no marked positions
and the only extracted certificate is `[]`. All proofs also cover degree
zero and empty input. The assembly buffer may be empty; its mandatory left
move followed by the left-blank dispatch still installs virtual head one.
The verifier captures its halting-transition emission before testing the
complete output; only the singleton `[true]` accepts.

## Exact time ledger

| Phase | Physical-step bound |
|---|---|
| Original input copy and physical-head rewind | `2n+2` exactly |
| Guessing | `τ(n)` exactly, the scheduler's actual first halt; `τ(n) ≤ B(n+1)^(c+1)` |
| Assembly-buffer rewind and verifier dispatch | `n+Q(n)+2` exactly |
| Verifier simulation, verdict, and absorption | At most `A(n+Q(n)+1)^d+1` |

Thus the common ledger is

\[
H(n)=3n+Q(n)+\tau(n)+A(n+Q(n)+1)^d+5.
\]

Put `m=n+Q(n)+1` and `r=c+d+1`. The proof uses

\[
\begin{aligned}
\tau(n)&\le B(n+1)^{c+1}\le Bm^r,\\
Am^d&\le Am^r,\\
3n+Q(n)+5&\le5m\le5m^r,\\
H(n)&\le(B+A+5)m^r.
\end{aligned}
\]

`cont_guess_normalize` then uses `e=r*max(1,c)` and the coefficient
`(B+A+5)*(C+1)^r*2^e`, exactly as proved by the predecessor. Both enlargements
use all-branch halting for backward truncation, as well as accepting-branch
padding. No arbitrary time function is evaluated at an inflated input size;
the verifier always receives its actual input `x++u`.

## Library and predecessor contracts used

- `Turing.FinTM.computesFunInTime_polyUnary`: supplies the concrete scheduler
  and the explicit degree-`c+1` budget in `b2_compile`.
- `contGuessTM`, `contGuessCfg`, `cont_guess_step`, `cont_guess_run`,
  `cont_guess_initial`, `cont_guess_coverage`: retained native guessing phase,
  capture representation, and exact physical-mask correspondence.
- `Turing.captureAction`: used by the retained guessing table invoked by the host.
- `Turing.FinTM.leftAction`, `leftCfg`, `leftCfg_apply`: embed that table in
  the disjoint scheduler/assembly bank while the verifier bank stays blank.
- `bufferTape_inputSymbol`, `virtualMove_correct`, `VirtualTag`,
  `bufferTape_append`: exact virtual-input clamping and tape capture.
- `capturedSummary`, `captureEmission`, `captureEmission_correct`,
  `capturedSummary_true`: complete-output capture and exact singleton verdict.
- Native `NDTM.runWith_append` and `runWith_of_halt`: timed phase composition
  and absorption; `FinTM.computesInTime_iff` and `ComputesInTime.output_unique`:
  completed-source contracts at their actual first halt.
- `NDTM.HaltsWithin.mono`, inherited `acceptsWithin_iff_of_halts` (which uses
  `FinNDTM.AcceptsWithin.mono`), `cont_guess_time_bound`, and
  `cont_guess_normalize`: common-bound transfer and final NTIME packaging.

There is no use of `exists_comp_partial` or untimed computability substitution.
The deterministic copier, rewinds, and verifier phases have explicit timed
configuration contracts throughout.

## Frozen surface and hygiene

`surface-check.json` and `verify_surface.py` verify against the required base:

- all eight public declaration headers and their order are unchanged;
- the entire inherited prefix, including all 68 predecessor private
  declarations and the forward compiler, is byte-identical;
- the five epoch-3 padding declarations, their docstrings, and the full
  remainder of the file are byte-identical;
- the original reverse-target docstring is retained with an append-only B2
  completion note; the equality docstring is unchanged;
- only the owned source path differs, and `git diff --check` passes.

Final size: **2,627 lines, 138,282 UTF-8 bytes**. SHA-256:
`d2f7358daaf0c0dd43779728bf1e1b536970b82cdd58b2c7645a5b8ccfcc8317`.
The file-size exception continues under exclusive ownership and the prohibition
on moving/removing predecessor helpers. Splitting/deduplication remains the
recorded E5 task. Style lint: **0 FAIL, 3 WARN** over the ten ClassNP files;
the warnings are the sizes of EXP, Nondeterminism, and TMSAT. The final owned
module has no compiler warnings other than its five untouched padding admissions.

Requested shared lemmas: **none**. Statement escalations: **none**.
Remaining frontier for this batch: **none**. No sanctioned `sorryAx` is consumed.

## Verification

- Lean **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`;
  mathlib **029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e**. Installed dependency
  revisions match the manifest; see `environment.log`.
- The required `lake exe cache get` ran once after the pinned toolchain was
  functioning. A prior startup attempt could not locate Lake's installation.
  Cache setup then encountered archive-owner metadata unsupported by this
  environment; it was resumed through the already-built cache executable with
  `TAR_OPTIONS=--no-same-owner`, and completed successfully. No `lake build`.
- The environment's PID namespace exposes `/proc/self/exe` but not the
  namespace-relative numeric `/proc/<pid>/exe` expected by this Lean release.
  The included `proc-self.c` compatibility shim redirects only that current-
  process executable lookup. The pinned release binaries and proof checker
  were not modified. The shim was used consistently for checking and caching.
- Owned-module and downstream checks: exit **0** (`downstream-final.log`).
- Final **57/57 fresh-module sweep**: exit **0**, **zero `error:` lines**,
  `FULL_SWEEP_COMPLETE`. The committed check script deletes each old olean and
  requires a fresh nonempty replacement. Final admission warnings: **21**, down
  from **23** at the required base. Exactly **five** remain in the owned file,
  all in the frozen epoch-3 padding cluster.
- Kernel type/value traversal, including opaque values: exit **0**.
  Both targets have empty admission roots and only the standard axiom triple.
  Every new private helper and its generated descendants — **92 checked
  declarations** in all — likewise has empty admission roots and at most that
  triple. See `AxiomChecks.lean`, `run-axioms.sh`, and `axiom-print.log`.
- Epoch-wide prints cover all **11 names enumerated in the campaign's E2
  batch table**, plus `timed_universal_quantitative`: all **12** closures are
  clean. This is a superset of the brief's request for “all ten” targets.
- Flat archive, SHA-256 manifest, format-patch replay, and git-bundle
  verification pass. Detached patch replay reproduces the full source exactly
  and passes the same surface verifier.

Headline prints:

```text
'Complexity.NP_subset_iUnion_NTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NP_eq_iUnion_NTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
TARGET ROOTS Complexity.NP_subset_iUnion_NTIME: []
TARGET ROOTS Complexity.NP_eq_iUnion_NTIME: []
B2_COMPLETE_CLOSURE_AUDIT_PASS: all 12 target/bridge closures and 92 new-helper/generated-declaration closures have empty admission roots and at most the standard axiom triple.
```

Final sweep tail:

```text
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

## New private declarations

All 42 are listed below: eight definitions and 34 lemmas. There are no new
private admissions. `surface-check.json` also records this inventory.

| Kind | Name |
|---|---|
| def | `b2UnaryTM` |
| def | `b2UnaryCfg` |
| lemma | `b2_unary_read` |
| lemma | `b2_unary_apply` |
| lemma | `b2_unary_step` |
| lemma | `b2_unary_run` |
| lemma | `b2_unary_initial` |
| lemma | `b2_unary_mask` |
| lemma | `b2_unary_computes` |
| lemma | `b2_unary_first` |
| def | `b2Slots` |
| def | `b2Host` |
| def | `b2GuessCfg` |
| lemma | `b2_tables_coincide` |
| lemma | `b2_guess_step` |
| lemma | `b2_guess_run` |
| def | `b2LoadCfg` |
| lemma | `b2_copy_step` |
| lemma | `b2_copy_run` |
| lemma | `b2_rewind_done` |
| lemma | `b2_rewind_step` |
| lemma | `b2_rewind_run` |
| lemma | `b2_initial` |
| lemma | `b2_copy_done` |
| lemma | `b2_start` |
| lemma | `b2_guess_word_injective` |
| lemma | `b2_guess_coverage` |
| def | `b2VerifyCfg` |
| def | `b2ReadyCfg` |
| lemma | `b2_verify_step` |
| lemma | `b2_verify_run` |
| lemma | `b2_verify_finish` |
| lemma | `b2_guess_return` |
| lemma | `b2_ready_step` |
| lemma | `b2_ready_done` |
| lemma | `b2_ready_run` |
| lemma | `b2_assembly` |
| lemma | `b2_verify_timed` |
| lemma | `b2_finish` |
| lemma | `b2_host_contract` |
| lemma | `b2_host_bound` |
| lemma | `b2_compile` |

## Archive and replay

`fill-ch2-e2cont-B2.zip` is flat: every entry is at its root, including
`SHA256SUMS`. `Nondeterminism.lean` is the full source and maps to
`TCSlib/Complexity/ClassNP/Nondeterminism.lean` in the repository. The archive
contains this report, one numbered format-patch, an incremental git bundle,
final sweep and axiom logs, the closure instrument, source-freeze verifier,
module order/check script, environment/cache records, and replay evidence.
`SHA256SUMS` covers every other archive member. No toolchain, dependency cache,
or olean is shipped.

Verify with `sha256sum -c SHA256SUMS`. Apply the numbered patch with `git am`
to the required base; this preserves Codex authorship. The bundle provides
the same commit and requires the base to be present. To reproduce checking,
use the committed 57-module order with `scripts/lean_check_tree.sh`, then
run `bash run-axioms.sh /absolute/path/to/tcslib` from this extracted archive.
The pinned `lean` must be on `PATH`. The compatibility shim is needed only
in environments with the documented PID-namespace mismatch.

Run `python3 verify_surface.py /absolute/path/to/tcslib` on the delivery
checkout to reproduce the surface checks. No changes to another repository
branch are needed.

## Notation

`x` is the original input, `u` its certificate, and `n=|x|` its length.
`C,c` are the prescribed certificate coefficient and degree;
`Q(n)=C(n+1)^c`. `S` is the unary scheduler; `B` is its time coefficient and
`τ(n)` its actual first halt. `V` is the verifier language, `M` its decider,
and `A,d` its time coefficient and degree. `H(n)` is the whole-host common
budget; `m=n+Q(n)+1`, `r=c+d+1`, `K=B+A+5`, and `e=r*max(1,c)` are the
normalization parameters. The argument name `V` in low-level helper lemmas
instead denotes the verifier machine, as its explicit `FinTM Bool` type shows.
