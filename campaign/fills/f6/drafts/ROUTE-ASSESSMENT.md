# F6 route and prerequisites — DRAFT, not a dispatch

Prepared 2026-11-07 for the user's selected **Claude** fill. The user selected the
**ruler-hosted suffix** route (D-F6-3), after the `SPACE_linear_ne_NP` consumer merges.
The earlier roadmap/retriage descriptions of an open choice, Codex, buffered
canonization, or F6 before that consumer are historical and superseded by those rulings.

This is a records-only assessment. No F6 proof was attempted, no shared API was changed,
and no fill was dispatched. The proposed fill is **not pre-shipped**. A direct
live-anchor use of the ruler-host contract needs a cut that it does not expose, but
the existing return embedding avoids that gap; the separate coded-bundle reader
and the full concrete route still need resolution/checking before issue.

## Pins and evidence boundaries

- Provisional consumer head: `74494d669ad9f8f926844f9280812449f57263d6` (#229).
- Provisional campaign base: `3555163f40d9c101a2ef4e81407c1bda58fe5ca4`.
- Existing snapshot used for the small component checks: `oleans-mlin2`, at the
  provisional consumer head. The root maintainer's replay log records two successful
  modules and Hierarchy's one unchanged admission. This drafting task did not rerun it.
- **Final base, source blobs, gate number, order lists, cache roots, screen population,
  bundle and checksum remain unissued.** Recompute on the merged prerequisite tree.
- Gate 112 is closed. Its four proved component probes remain useful; its admitted
  arbitrary-machine `F6Probe.route_space` is explicitly withdrawn (112-01). The new
  `probes/ConditionalComponents.lean.txt` excludes that theorem completely.
- `logs/preship-DRAFT.json` distinguishes the small checks actually run here from
  historical receipts and the full route checks that remain undone.

## What the selected route needs

Write `z = pairEncode (Nat.bits s) (pairEncode α x)`,
`ℓ₁ = 2 * (Nat.bits s).length + 2`, `ℓ₂ = 2 * α.length + 2`, and `ℓ = ℓ₁ + ℓ₂`.
One fixed `SU` must be chosen before `α`; only its analysis constant may depend on `α`.

1. Scan the space header and rewind its ruler to origin `0`. The native input head is
   now at `ℓ₁ + 1`. Use H5 to run the existing startup `R` on the virtual native input
   `pairEncode α x`, with that ruler. Startup ends at virtual position `1`, with table
   and initial unary state installed, source/work scratch blank, all work heads `0`,
   and output empty. To transfer safely, first seam the native startup to a silent
   halt leaf, host that first-halting composite, and use the existing returning
   embedding to turn its first halt into a fresh live return anchor.
2. Move the same ruler head to `ℓ₁`, scan the code header while extending the ruler to
   `true^ℓ`, and rewind the ruler head to `0`. The physical input head is `ℓ + 1`,
   representing virtual input position `1` on `x`. The installed table/state and all
   other heads/tapes are preserved.
3. Host H2-F's forwarding loop on virtual input `x` with that extended ruler. H2-F
   reproduces the actual source output and visits only source cells on its mirrored
   tape; its two auxiliary heads stay in a per-code fixed interval. H5 preserves
   those bank visited sets exactly, and its ruler stays in `[-1, ℓ]`.
4. Compose with the public general seam ledger. Derive `s ≥ 1` from the one-work-tape
   coded source, then absorb the two headers, startup and fixed auxiliary intervals
   into a positive constant times `s`, uniform in `s,x,output,t`.

No payload copy, source-input-head position tape, clock, overrun verdict, output tag,
or time bound is part of this route or the frozen statement.

## Actual public bridges and remaining obligations

All names below are already in Hierarchy's transitive import context. This is not
authorization to edit their homes or to unfold their definitions in Hierarchy.

| Step | Public bridge | Premises / remaining work |
|---|---|---|
| Fixed one-tape startup | `Turing.exists_selfStartupTM` | `T_α,B_α` depend only on `α`, uniformly in suffix `x`. Instantiate the existing effective scheme. Its stated endpoint is live, not halted. |
| First header + rewind | `Turing.headerRulerTM_run` | Start with state `0` via a local initial-state override and public `initCfg_with_q₀` / `runFrom_with_q₀`; ruler must be blank. Contract includes endpoint and first-return cut. |
| Startup on suffix | `Turing.exists_rulerHostTM`, `rulerHostCfg_fields` | Supply `z.drop ℓ₁ = pairEncode α x`, exact length, `ℓ₁>0`, ruler including the two boundary blanks, and false left-boundary tag at virtual position `1`. Endpoint, time, silence, and visited sets are available. For the required cut, host the native startup seamed to a halt leaf, then use the returning embedding below. |
| Seek ruler end | `Turing.skipTM_run_ofCfg` | This row leaves the head at `ℓ₁+1`, not `ℓ₁`. A one-cell left correction is an explicit consumer leaf, not an invisible equality. Its one-step proof can use `step_of_tapeAction_move` if that leaf is authorized. |
| Second scan | `Turing.headerScanTM_run`, `headerScanCfg_ruler`, generated `headerScanCfg_*` fields | Existing ruler prefix length `m=ℓ₁`; native input offset `p=ℓ₁`; code header `α`. Do not invoke blank-only `headerRulerTM_run` on the nonblank ruler. |
| Final rewind | `Turing.rewindTM_run_ofCfg` | `u = true^ℓ`, `n=ℓ`; its framed endpoint and cut preserve the installed bank and input position. |
| Hosted return | `Turing.embedEmitRetTM_run`, `embedEmitRetTM_visitedByTapeHead`, `embedEmitTM_visitedByTapeHead` | Identity tape embedding; source first halt gives H5 first halt, and R1' gives a fresh live return cut at the same time with unchanged visited sets. |
| Prefix composition | `Turing.seamCompTM_step`, `MultiTapeTM.initCfg_with_q₀`, `MultiTapeTM.runFrom_with_q₀` | Each live phase exit needs its actual first-return cut; each dispatch contributes one step. Prefix endpoint, silence, cut and time bound must be proved at the actual fixed machine. |
| Native forwarding loop | `Turing.StepBlock.exists_forwardLoopTM`, `StepBlock.forwardLoop_forward` | Extract source halt/output with `FinTM.computesInTime_iff`; use first source halt `t₀≤t` for the ledger's live-before hypothesis. No converse is required. |
| Initial loop layout | `StepBlock.forwardLoopCfg_init_workTapes`, `_init_fields`, `_halt_iff`, `embedEmitCfg_forwardLoop_init` | Match table, summary, blank mirrored/scratch tapes, heads, input position and empty output through published equations. |
| Idle extra bank | `embedEmitTM_runFrom`, `embedEmitTM_visitedByTapeHead`, `_frame`, `embedEmitCfg_eq` / `_mapState_eq` | An unused bank head visits its singleton starting cell. Avoid re-deriving a generic embedding/frame ledger. |
| Loop under H5 | `exists_rulerHostTM`, generated `rulerHostCfg_*` fields | Instantiate the length/drop relation at `ℓ`, now on `x`. Halting/output and visited-set clauses suffice here; no live-anchor transfer out of this final host is needed. |
| Final seam + space | `startupLoopTM_runFrom`, `startupLoopTM_spaceUsed_le` | Actual `aRun`, `hexit`, `aCut`, layout equality `hcfg`, prefix bound `hB`, `S≥1`, and hosted per-tape bounds `hloop`. These must be hypotheses in a conditional probe, or proved for the actual F6 witnesses. |
| Source-bundle conversion | `FinTM.computesInTime_iff`, `CodeTM.toFinTM_k`; possibly `EffectiveMachineCode.toK_toFinTM` / `_machine` | The raw/source bundle bridge still needs a Rule-10-safe reader or a verified alternate public route; see diagnostic below. |
| Addend-free absorption | `CodeTM.one_le_spaceUsed`, `length_bits_le_self`, `MultiTapeTM.spaceUsed_le_mul_succ`, space/visited monotonicity and card lemmas | Obtain `1≤s` before dividing or absorbing constants. The final `C_α` is independent of payload, time, output and budget. |

## Direct live-anchor gap avoided by existing returning embedding

The current `exists_rulerHostTM` concludes an endpoint at a time `t'`, liveness relative
to halted state `none`, intermediate **tape/head/output** frames, and visited-set
equalities. It does not characterize intermediate controls or transport an arbitrary
live source-exit cut. Thus it cannot be used *directly* to dispatch at `inj exit false`.
The historical `hosted_startup` probe checks no such cut, while `final_seam` assumes
its prefix cut. Endpoint equality and ordinary liveness must not be substituted for it.

Independent review identified an existing composition that avoids a new shared API:

1. Seam native startup `R` to a one-step stationary, silent **halting leaf**, using
   `seamCompTM_run_ofCfg` and the source cut already supplied by
   `exists_selfStartupTM`. The composite first halts at `T_α+2`: startup time,
   one seam dispatch, one halt step. Its four data fields at halt are exactly the
   startup endpoint's. Liveness before that time follows from
   `seamCompTM_runFrom_left`, source endpoint liveness and
   `MultiTapeTM.runFrom_state_ne_none_of_le`, then the dispatch endpoint at `T_α+1`.
   The stationary halt leaf is a concrete consumer leaf, not a new generic host.
2. Apply `exists_rulerHostTM` to that halting composite on the suffix `pairEncode α x`.
   H5's halting endpoint and its `none`-liveness clause now give a **first host halt**
   at some `t'≤C_H*(ℓ₁+1)*(T_α+2)`.
3. Apply `embedEmitRetTM_run` to the hosted machine with the identity embedding on
   its existing tape bank. It reaches the fresh anchor `Sum.inr ()` at exactly that
   same `t'`, and the public theorem supplies its strict first-return cut. It adds
   no tape, ruler, payload copy or time. `embedEmitRetTM_visitedByTapeHead` followed
   by `embedEmitTM_visitedByTapeHead` preserves the host's visited sets exactly.
4. This live return is the next seam's exit; its cut comes from R1', never from an
   unjustified claim about H5's `inj`. The same ruler is subsequently extended.

`probes/HaltedHostReturn.lean.txt` checks the bounded conditional H5→R1' composition
from explicit source live/first-halt hypotheses, with actual H5 witnesses and the
same returned time for the endpoint, strict cut, output and visited sets. It passed
with zero errors and only the standard three axioms. The first failed elaboration
attempt (two local proof-script errors) is preserved as `HaltedHostReturn-attempt1`
source/log; the successful corrected attempt is in `logs/preship-DRAFT.json`.
It does not construct the native
startup+halt leaf or the complete F6 prefix; those remain named OWN leaves and
must be concretely checked before issue.

**No H5 contract extension is required by this route assessment.** An earlier draft
proposed a strengthened host theorem because the direct live-exit cut is absent;
the returning-embedding route replaces that proposal. The final brief must name
this actual composition rather than commission either a false cut or unnecessary
new public API.

## Rule-10 diagnostic: coded bundle to raw source

The frozen target supplies `(c.decode α).toFinTM` computations and space, while
`exists_selfStartupTM` installs the raw `(c.decode α).tm`. `CodeTM.toFinTM` currently
publishes only `_k`, not a full bundle equation or `_State`/`_tm` field readers.
The generic `EffectiveCodeK.toFinTM` similarly has no published field readers; the
two `EffectiveMachineCode.toK_*` equalities alone do not read its bundle.

`BundleUnsealed.lean.txt` is deliberately the direct definitional bridge control;
`BundleSealedControl.lean.txt` seals `CodeTM.toFinTM` and tries that exact bridge.
Their actual outcomes are in `logs/preship-DRAFT.json`. This is a diagnostic of the
obvious route, not a proof that every possible public route is impossible.
The positive control passed unsealed; the sealed control failed with exactly one
expected type mismatch. The minimal proposed reader is one whole-bundle equation,
beside its definition in `Encoding.lean`, with no `simp` attribute:

```lean
theorem CodeTM.toFinTM_eq (M : CodeTM) :
    M.toFinTM = { k := 1, State := Fin (M.numStates + 1), tm := M.tm } := rfl
```

`ProposedBundleEquation.lean.txt` elaborated this exact equation by `rfl` in an
Encoding-only import context. That proof is a syntax/home probe for the proposed
same-home addition, **not** a legal foreign unfolding for the eventual consumer.
`BundleConditionalSealed.lean.txt` takes the exact equation as an explicit hypothesis,
seals `CodeTM.toFinTM`, and converts both the frozen computation (halt and arbitrary
output) and source-space premises; it passed with only the standard three axioms.
No declaration named `CodeTM.toFinTM_eq` was added to campaign Lean source.

This is one concrete public-API decision for the user. Before issue, either obtain
approval and land/gate/replay that reader in its own prerequisite PR, or demonstrate
an existing public route with the same sealed conversion. Do not hide a conversion
with `change`, `rfl`, `simpa`, or an unlisted seal omission.

## Bank layout: an actual consumer obligation

H5 puts its ruler on the **last** tape. Applied to startup `R : MultiTapeTM (K+3) …`,
the physical bank has `N=K+4` tapes, ruler at index `K+3`. The ready-made
`suffixRulerCfg (k:=1) (K:=K)` instead puts its ruler at index `3`, before scratch
tapes. Those layouts are not definitionally equal for arbitrary `K`.

A candidate implementation that retains the selected input route is to keep the
global ruler last: embed H2-F's three tapes into the first three of a `K+3`-tape bank,
leave the other `K` bank tapes idle, then apply H5 to that entire bank. The startup
host and final loop host both have `N` tapes and the same last ruler. Use the generic
`startupLoopTM` seam with zero outer frame (`k:=K+2`, outer `K:=0`) and an explicit
endpoint equality. The ready-made `suffixRulerCfg_embed` is then comparison evidence,
not the literal layout lemma for this assembly. Alternatively relocate/permutate
the hosted startup with the existing emitting embedding and prove its frame.

Whichever assembly is finally selected must be checked concretely before dispatch.
It may not be silently left as the old arbitrary `aRun`, nor treated as a new generic
private relocation host. The assessment does not claim either full assembly has
already elaborated.

## Remaining OWN leaves, beyond these conditional components

1. **Concrete prefix.** Fix one finite-control assembly independent of `α,s,x`;
   establish the initial override, native startup+halt leaf and first halt, first
   header, hosted return anchor/cut, ruler-head seek/correction, code scan, rewind, preserved bank, silence and actual
   final first-return cut. Record the exact endpoint equality and all dispatches.
2. **Layout and source conversion.** Reconcile the last-ruler bank with the final
   host, using public fields; verify the raw source matches the bundled target
   without foreign-definition reduction. No new public declarations in Hierarchy.
3. **Loop ledger.** For the first source halt `t₀≤t`, use H2-F's source visited-set
   inclusion on the mirrored tape and interval on the other two tapes; transport
   through emitting embedding and H5. Include every idle tape's singleton cell and
   every ruler boundary cell, and use monotonicity to the supplied source bound.
4. **Per-code arithmetic and output.** Bound prefix space by its header-linear time
   if convenient, use `s≥1`, `|bits s|≤s`, and choose one positive `C_α`. Preserve the
   actual arbitrary output through the empty-output prefix, forwarding loop,
   embeddings and hosts. Close the exact frozen existential without a time promise.

For example, after the six prefix phases above are assembled with five dispatches,
their anticipated time is at most
`C_H * (ℓ₁+1) * (T_α+2) + 4*ℓ₁ + 2*ℓ₂ + 12`.
This is **an arithmetic planning bound, not an executed route attestation**; confirm
the actual assembly's row costs before prescribing its coefficient. The generic
bound `N*(prefixTime+1)` then gives prefix space linear in `s` with per-code
coefficient. For the final loop, a deliberately loose common per-tape budget is
`S = s + (2*D_α+1) + ℓ + 3`; it covers source tape, auxiliary intervals, idle heads
and ruler. The public seam gives `B_prefix + N*S`. This shows why no time bound or
payload length needs to enter `C_α`.

Check empty `α`, empty `x`, arbitrary outputs, zero source time, first halt before
the supplied `t`, `s=0` (excluded by the source-space premise), and both positive
header lengths. A source malformed code is still a valid decoded one-tape machine;
do not add a well-formed-code premise or replace the all-`α` clause by canonical codes.

## Issue checklist

Hold the fill until #229 has merged, the source-conversion route is resolved, and the full
concrete conditional route probe discharges every prescribed premise. Then refresh
the source pins, exact target/admission census and ownership overlap; generate
bootstrap/downstream/final orders and narrowed cache roots from that tree; run the
baseline screen and candidate searches, complete home/guard/statement probes, and
stage a checksum-pinned Claude packet. None of those final receipts is supplied by
the small component checks or by gate 112's historical PASS.
