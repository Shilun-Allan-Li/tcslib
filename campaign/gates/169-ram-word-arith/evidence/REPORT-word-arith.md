# RAM word arithmetic — round 2 final delivery

## Base and scope

Base: `7342f98b58704d6c25faf668ed1a64ea0b27c4af` on `ram/readers-2` (PR #375),
fetched read-only. Instructions were read at `e40383d88d79e23026c95e20608ee8827d45e59b`.
The original exchange README, bundle and SHA256SUMS, and the round-1 archive's internal
checksums were checked before applying the round-1 patch to this new base. Those input and
environment records are retained under evidence/ and evidence-r2/.

Source branch: `codex/fill-ram-word-arith-r2`, never rebased or pushed. Source HEAD:
`bc0a8f2e3f68e2900bdf7958faaa9553bab93a02`. The zip patch is against the base above.
Only WordArith.lean and one authorized pure reader in StateRenaming.lean are delivered.
Thirty unrelated preexisting blueprint edits in the shared source checkout remain untouched
and are excluded from every source commit, patch, and delivery.

## Targets

| Target | Status | Witness bound C |
|---|---|---|
| bvBits_injective | proved | — |
| exists_wordAddTM | proved | 2 |
| exists_wordSubTM | proved | 2 |
| exists_wordMulTM | proved | 30 |
| exists_wordHalfTM | proved | 9 |
| exists_wordSignExtendTM a | proved | 2*a+20 |
| exists_wordIntTM c a | proved | 2*(a+1) |
| exists_wordSignTM | proved | 2 |
| exists_wordNonzeroTM | proved | 2 |

There are zero admissions in the owned file. Every target's dependency walk lists zero
reachable direct users of sorryAx. No admitted dependency, including the table routines, is
used. All 18 original public declaration statements are byte-identical to the base.

## Construction and proof architecture

One arbitrary-frame, alias-safe `wordLockTM` is verified by the catalog trace API. It reads
both input bits before writing a cell, and returns using the source delimiter, retaining
nonblank output when the source aliases the destination. Its `wordLock_run` has no blank
scratch or destination precondition. A single ripple instance supplies add, sub, and the
multiplier's in-place addition. Carry algebra cites core's carry and bit-addition equations.

Half composes the returning copy, catalog sign fold, and the sign-filled backward delay
scan. Sign extension composes sign fold, copy, common walk, one fixed backward move,
constant suffix writer, and two prefix rewinds. The latter allow arbitrary current cells,
so the destination rewind need not traverse the appended sign suffix.

Integer constants are either `ofNat n` or its complement, using core's integer conversion
equations. A finite counter saturates at n; `Nat.testBit_lt_two_pow` and
`Nat.lt_two_pow_self` show all further natural bits are false. `wordConst_run` instantiates
the SAME lockstep sweep with all three tape choices equal to 2. Its state table is finite,
though larger than a minimal binary-length table; the statement does not bound control size.

Multiplication uses the public `phaseHostTM`, not a private host. Initialization copies u
to scratch 3 and emits zero into the destination. Each loop round probes the next tape-1
bit, conditionally adds scratch into destination IN PLACE with the alias-safe ripple row,
then invokes the catalog's forward delay shift and a single tape-1 head move. Scratch 4
is never touched, so no intermediate sum copy is needed. This specializes and simplifies
the brief's two-scratch route without changing any statement. Core's
`setWidth_setWidth_succ_eq_setWidth_setWidth_add_twoPow` supplies the partial-product
recurrence. The invariant is u times the first r low multiplier bits in tape 2 and u<<<r
in tape 3, both modulo 2^W. `Segment.trans` composes W rounds, each at most 4*W+10 steps.
The catalog clear restores globally blank scratch, and rewind returns tape 1. Initialization
costs at most 4*W+6 and cleanup costs 3*W+8. The common segment envelope is 3*(W+1), independent
of the number of rounds; C=30 bounds both total quadratic time and linear radius. Width zero
uses the empty loop and the same catalog rows.

The catalog lacks two-source carry sweeps, unconditional selected-work-head one-step moves,
and a stationary three-way optional-cell probe. These are the only new leaf machines, with
that gap documented beside each definition. The generic lockstep action is shared by the
move and probe leaves. All loops and dispatches use the existing public phase host; no new
private host, duplicated catalog run proof, or per-operation transducer proof is introduced.

## Pure reader exception and imports

`Turing.Cfg.mapState_eq` is added beside `Cfg.mapState` in StateRenaming.lean. Its statement
is exactly the defining record update, and its proof is rfl. Its docstring states the formula;
it has no simp attribute and uses no axioms. Existing projection readers and PR #375's
published readers were searched first; there was no full record equation. The updated
COMMON.md missing-readers rule explicitly authorizes this addition. Removing the six-line
reader addition reproduces its home file byte-for-byte.

Added existing Build imports: Seam (phase host/transport), Scan (constant suffix writer),
Rewind (prefix rewind allowing an arbitrary current cell), and SeamLayout (published
BufferWords prefix readers). No import outside the brief's Build/*/Mathlib allowance was
added. No new public declaration in the owned file, imported file body change other than
that reader, simp registration, axiom, admission, or statement change.

## Reuse searches and definition boundaries

The catalog registry and import closure were searched for framed copy/scan/clear/walk,
seek/rewind, action primitives, prefix patches, constant writers, and composition. The
existing scan and rewrite contracts were preferred wherever they fit. Core and Mathlib
were searched for carry, complement, subtraction, integer conversion, arithmetic-shift,
left-shift, sign-extension, and low-bit-width multiplication equations before proving list
identifications or cell equations. The scratch-word layout proof is specific to a globally
blank scratch tape; the destination layout uses `wordPatch_frame`. No existing catalog
proof text is copied for a variant. The thin phase placement and envelope adapters factor
repeated proof obligations instead of implementing control structures.

Directly consumed foreign TCSlib definition families and their published interfaces:

| Definition family | Readers / contracts used |
|---|---|
| Action.apply, moveInputPos | Action.apply_state/inputPos/workTapes/workTapePos/output; moveInputPos_zero |
| Cfg.workTapeSymbols | Cfg.workTapeSymbols_eq |
| Cfg.mapState | mapState_eq, mapState_state/inputPos/workTapes/workTapePos/output, mapState_sigma_state_ne |
| MultiTapeTM.step/runFrom | step_of_some, runFrom_zero/one, workTapePos_runFrom_mem_Icc; phase/segment run contracts |
| FinTM.bufferTape | bufferTape_nat/left, bufferTape_take, bufferTape_eq_none_of_not_mem |
| wordPatch | wordPatch_apply/frame/twice/append/self; catalog_write_take |
| catalogTrace | catalogTrace_eq and catalog_trace_run |
| scanTM, scanFold, scanShift, scanKeep, scanResult | scanTM_run_ofCfg; scanResult_fold/shiftLeft/shiftRight |
| walkTM | walkTM_run_ofCfg |
| writeConstTM | writeConstTM_run_ofCfg |
| rewindTM | rewindTM_run_ofCfg |
| clearTM | clearTM_run_ofCfg |
| phaseHostTM | phaseHostTM_run |
| Segment | segment_iff; Segment.zero/trans |
| ReachesWithin | reachesWithin_iff |

Only same-file definitions are explicitly unfolded. Core/Mathlib definitions are never
passed to simp, rw, or unfold; named equation theorems are used. All imported ordinary
TCSlib definitions are made irreducible in the strict seal, which also removes imported
simp/unfold registrations. No external project code or architecture was adapted.

## Private declaration inventory

- `wordLockAction`: Move the three selected heads together, optionally writing one destination bit. 
- `wordLockAction_apply`: The lockstep action changes only its destination cell and the selected heads.
- `wordLockTM`: A two-source finite-state sweep, followed by a return guided by the first source. The catalog's one-tape scan cannot read both source bits with a carry. The selected tapes may alias: the forward pass reads each cell before writing it, and every written cell stays nonblank. The carry is discarded at the right delimiter, so every run has the same live exit. 
- `wordLockCfg`: A lockstep configuration with a written destination prefix and a common head offset. 
- `wordLockCfg_read_fwd`: At the forward boundary no source cell has yet been overwritten, even with aliases. 
- `wordLockCfg_read_full`: A full destination patch keeps its delimiters; an aliased source reads the output word. 
- `wordLockCfg_write`: One forward action extends the output prefix by exactly its next bit.
- `wordLockCfg_move`: A non-writing lockstep action translates only the common head offset. 
- `wordLock_run`: The framed lockstep sweep computes any transducer whose successive states and bits satisfy the supplied cell equations. No scratch-blankness hypothesis is needed.
- `wordRippleStep`: One ripple-carry cell, optionally complementing the second operand for subtraction. 
- `wordRipple_run`: The framed ripple row adds the optionally complemented second word and an initial carry.
- `wordAt_mapState`: State renaming does not affect a word held at a work head. 
- `wordAt_write`: A same-width word write keeps the destination delimited. 
- `wordPhase_segment`: A public phase-host run is a segment avoiding any designated exit in another phase.
- `wordPhase_guard`: A row's exit cut supplies the phase-host guard when only its exits redirect. 
- `wordWrite_twice`: Two writes of equal-width words on one tape retain only the last word. 
- `wordMoveTM`: One fixed move of the selected heads. The catalog supplies its action primitives but no standalone fixed-distance work-head row; this one-step leaf is used between the existing scan rows. 
- `wordMove_run`: The fixed move takes one step and preserves every cell and every other head.
- `wordPhase_bounded`: A linear-time phase begun within the word's span stays in one common linear envelope.
- `wordMulAcc`: The partial product uses precisely the multiplier's first `r` low bits. 
- `wordMulAcc_succ`: One more multiplier bit adds the corresponding shifted multiplicand. 
- `wordShiftUp_bits`: A forward one-cell delay is a left shift of the little-endian word.
- `wordProbeState`: Three distinct probe verdicts encode false, true, and the right delimiter. 
- `wordProbeTM`: A stationary one-cell read. The catalog has scans but no leaf returning the currently scanned optional symbol; the phase host needs this three-way verdict at the multiplier head. 
- `wordProbe_run`: The stationary probe returns the current optional bit in exactly one step. 
- `WordMulStage`: The multiplier's finite row schedule; the probe supplies the loop condition. 
- `wordMulPh`: Only the clear and rewind catalog rows need distinct local state alphabets. 
- `wordMulPh_fintype`: Every multiplier row has finite control. 
- `wordMulPh_decidableEq`: Equality of each row's control state is decidable. 
- `wordMulRows`: The multiplier reuses the framed sweeps, catalog shift, scratch clear, and prefix rewind. 
- `wordMulRed`: Only the probe branches; all completed arithmetic rows return to its next iteration. 
- `wordMulTM`: The public phase host supplies the multiplier's loop and all stationary dispatches. 
- `wordMulExit`: The catalog exits which may dispatch out of each multiplier row. 
- `wordMulRed_none`: A multiplier row redirects only from one of its stated exits. 
- `wordMulTapes`: The multiplier frame patches just the destination and the single scratch word. 
- `wordMulHeads`: Only the multiplier-input head has a nonzero offset at the seams of its loop. 
- `wordMulCfg`: A canonical loop configuration carries the partial product, shifted word, and bit index. 
- `wordMulCfg_mapState`: Renaming a loop configuration tags only its state. 
- `wordMulCfg_write`: Replacing either canonical word keeps just its latest value.
- `wordMulCfg_words`: Both patched words remain delimited at every loop seam.
- `wordMulCfg_pos`: A canonical loop seam lies within `W` of its original frame while `r ≤ W`. 
- `wordMul_phase`: A verified returning row becomes a bounded segment in the multiplier's public host.
- `wordMul_init`: Copying the multiplicand and zeroing the destination establish the loop invariant.
- `wordMul_probe`: A stationary probe and its dispatch preserve the canonical frame in two steps.
- `wordMul_shift_advance`: A catalog delay shift and one fixed input-head move prepare the next multiplier bit.
- `wordMul_add`: The same ripple row adds occupied scratch into the destination in place.
- `wordMul_round`: One multiplier bit preserves the partial-product invariant and advances its bit index.
- `wordMul_loop`: The first `r` multiplier rounds compose with quadratic time and one linear envelope.
- `wordMulRestCfg`: After clearing scratch, the output frame has only the tape-one head left to return. 
- `wordMulRestCfg_mapState`: Tagging the final rewind frame changes only its state. 
- `wordMul_finish`: At the multiplier's right delimiter, clear scratch and return the last displaced head.
- `wordFold_run`: A Boolean fold scans one delimited word, returns the head, and preserves every cell.
- `bvBits_last_fold`: The overwrite fold of a word's bits is its most significant bit, with false for width zero. 
- `wordAny_fold`: The Boolean disjunction fold records exactly whether a true cell has occurred. 
- `bvBits_no_true`: A word has no true bit exactly when it is zero. 
- `wordHalf_bits`: Moving every bit down one position and repeating the sign bit is arithmetic halving.
- `wordHalfRows`: The rows of arithmetic halving: copy, sign fold, and either sign-filled shift. 
- `wordHalfRed`: Halving dispatches the sign flag to the corresponding fixed-sign scan, then one exit. 
- `wordHalfTM`: Arithmetic halving composed from the framed copy and the catalog scans in a phase host. 
- `wordHalf_run`: The arithmetic-shift program preserves every frame and returns all heads.
- `wordSignExtend_bits`: Sign extension appends copies of the sign bit to the little-endian word.
- `wordWrite_append`: Writing at the end of a patched prefix joins the two words, for arbitrary other heads. 
- `WordExtStage`: The finite sequence of existing rows used for sign extension. 
- `wordExtPh`: A row's own state alphabet; the sign is carried by the phase index. 
- `wordExtPh_fintype`: The sign-extension rows are finite for every fixed extension length. 
- `wordExtPh_decidableEq`: Each sign-extension row has decidable state equality. 
- `wordExtRows`: Sign extension uses the catalog's copy, walk, constant writer, and rewind rows. 
- `wordExtRed`: The finite dispatch table threads the computed sign through the extension rows. 
- `wordExtTM`: The catalog-row program for sign extension; every loop belongs to an existing row. 
- `wordExtExit`: Only catalog exits trigger a sign-extension dispatch. 
- `wordExtRed_none`: A state outside a row's catalog exits cannot redirect the extension host. 
- `wordExtHeads`: The source and destination head offsets of the extension program. 
- `wordExtCfg`: A framed extension configuration after the source has been copied, in any phase type. 
- `wordExtCfg_mapState`: Tagging an extension configuration changes only its phase state. 
- `wordExtHeads_add`: Moving both selected heads by one common offset adds it to their frame coordinates. 
- `wordExtHeads_update`: Updating either selected head sets its coordinate and preserves the other. 
- `wordExtCfg_prefix`: A rewind may read the copied prefix even when sign bits occupy its right boundary.
- `wordExt_sign_copy`: The sign fold and framed copy enter the extension's walk row with the original word.
- `wordExt_walk_write`: Walking to the source boundary, stepping back, and writing the fixed sign suffix.
- `wordExt_rewind`: Two catalog rewinds return the source and destination heads without changing the word.
- `wordConstIndex`: The constant writer counts only up to its fixed table length, then saturates. 
- `wordConstStep`: A saturated table emits a natural number's bits, optionally complemented for negatives. 
- `wordConstStep_cell`: Saturating the bit table is exact because every bit at or above `n` of `n` is false.
- `wordConst_run`: The constant table is one instance of the alias-safe framed sweep, using only tape two.

## Final verification

- Native owned-file check: final-native-01, exit 0, zero errors and zero warnings; final
  downstream replay rechecks the delivered source after documentation-only sketch additions.
- FinalAxioms: exit 0. bvBits_injective uses propext and Quot.sound; every other target uses
  at most propext, Classical.choice, and Quot.sound. Cfg.mapState_eq uses no axioms.
- FinalDependencies: exit 0; all nine reachable direct-sorryAx-user lists are empty.
- FinalSealed: exit 0; 428 imported ordinary TCSlib definitions sealed, three imported
  simp/unfold registrations removed. All nine proofs re-elaborate without warnings.
- final-freeze.log: exit 0; all 18 original public statement headers byte-identical,
  no new public declaration in owned file, and the pure reader's home-file scope exact.
- final-diff-check.log: exit 0, no whitespace errors.
- final-patch-roundtrip.log: exit 0; applying the patch to exported base files reproduces both delivered files byte-for-byte.
- final-style.log: exit 1 solely for the file-size rule. The file has 2113 lines. COMMON.md's
  tier-2 addendum explicitly permits continuing past 1500 lines and reporting it for a
  maintainer split. All missing-sketch findings were fixed; no other style findings remain.
- Full current-source replay: all 129 TCSlib modules in the import closure of the nine requested downstream consumers exit 0. This includes WordArith, the modified reader home, KeyTable, InputBit, every Sim module, Simulation, Classes, RAMSimulation, and TuringMachine. See final-replay-order.txt, final-downstream.txt, replay-summary.json, and the 129 individual logs. This is the requested closure, not a whole-project lake build.

Final check inputs and all successful/failed development logs are retained. Failed local
iterations are historical evidence, not final failures. The final probe and replay logs,
verification-index.json, and replay-summary.json identify the definitive results. The replay
may warn on unchanged admissions elsewhere in the base; it requires zero errors in every
module and no admission reachable from these nine targets.

## Environment and resource discipline

macOS host, Lean 4.25.0, 12 logical CPUs, 18 GiB RAM. Initial native macOS preflight recorded
62% memory free and about 110 GiB APFS free; native sysctl/vm_stat/memory_pressure/df/mount
replace Linux /proc/cgroup probes. Existing exact-pins package artifacts are linked from the
parallel chapter worktree; all available manifest URL/revision entries were checked. No cache
fetch or global cache-history claim. Round-2 TCSlib oleans are bootstrapped in the dedicated
`.lake/fill-ram-word-arith-r2-oleans` tree; none are reused from round 1.

Every Lean invocation goes through scripts/lean_check_tree.sh with that scratch tree and a
serial guarded runner. It checks all machine-wide Lean processes before starting and waits
while three others run, starts at most one own Lean, uses nice 10, and records count/waits,
start/end, /usr/bin/time -l RSS, and exit. No lake build, direct bypass check, or concurrent own
Lean was run. The process log has 11 threshold waits (five seconds per threshold wait); maximum observed other-Lean count is 3. Peak RSS in the final replay is 2730246144 bytes (2.54 GiB).

## Delivery

Checkpoints 1–4 were delivered to exchange commits 963bbea12, 8a7cc31f3, 369e30111,
and f90e5172c. Checkpoint 4 already had eight proved targets and empty admission walks.
The final archive adds the proved multiplier and final downstream verification.

The original shared exchange checkout had an unrelated untracked startup zip colliding
with an incoming tracked file, so a separate managed delivery checkout was used. Its zip-only
commits are preceded by `git pull --rebase origin exchange/pass-shelat-ch5-8`; no force push,
source-branch push, PR, or unrelated exchange mutation. The source branch was never rebased.
The zip includes this report, full owned source, reader home file, patch against the new base,
and evidence with internal SHA256SUMS; it excludes package artifacts and oleans. The final
archive is tested with zipfile.testzip and every internal SHA-256 before exchange delivery.

## Scoped diff against base

```
 .../Complexity/TuringMachine/Build/WordArith.lean  | 1930 +++++++++++++++++++-
 TCSlib/Complexity/TuringMachine/StateRenaming.lean |    6 +
 2 files changed, 1894 insertions(+), 42 deletions(-)
```
