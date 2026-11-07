# F6 fill — DRAFT ONLY, Claude, awaiting prerequisites

**Do not dispatch this file.** It contains intentionally unissued source/package
pins and an unresolved shared API prerequisite described in `ROUTE-ASSESSMENT.md`.
The user selected **Claude**, the ruler-hosted suffix route, and checkpoint/final
zip delivery by push to the exchange inbox. Fill execution follows the merge of
the `SPACE_linear_ne_NP` consumer (#229), never overlaps another Hierarchy fill,
and also waits for the coded-bundle conversion check and concrete route pre-ship.

## Base and supplied packet — maintainer must finalize

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Branch base: `complexity/arora-barak-ch3-4`, **not `main`**.
- Exact fill base: **UNISSUED**. The assessment uses provisional consumer head
  `74494d669ad9f8f926844f9280812449f57263d6`, based on
  `3555163f40d9c101a2ef4e81407c1bda58fe5ca4`; neither is a dispatched fill pin.
- New branch at the eventual exact base: `fill/f6-space-universal`.
- Bundle SHA-256 and section count: **UNISSUED**.
- Target source blob / statement freeze / base sorry inventory: **UNISSUED**.
- Rule-10-safe coded-bundle conversion reader or approved existing conversion
  route: **UNRESOLVED**. The minimal proposed prerequisite is
  `CodeTM.toFinTM_eq (M) : M.toFinTM = { k := 1, State := Fin (M.numStates + 1), tm := M.tm }`
  in Encoding; its syntax and conditional sealed consumption passed, but it is
  **not approved or published**. No H5 strengthening is required: use R2 → H5 → R1' below.
- `inputs/bootstrap-order.txt`, `downstream-order.txt`, `final-order.txt`,
  `mathlib-roots.txt`, `owned-files.txt`, `target-admissions.json`, source/gate
  receipts, baseline screen and exact scope record: **not yet generated**.

Keep the extracted packet outside the proof checkout. Its newly issued records
may postdate the pinned proof base. Verify its bundle checksum and every section
before working. Pin the base once; do not follow a moving campaign branch, merge,
rebase, cherry-pick, or fetch other fill deliveries into the proof branch.

Read `policy.md`, `workflow.md`, `campaign/standards/TEMPLATE.md`, the current
maintainer rules in the packet, and `fill-environment-addendum.md` **v2.6**. Source
and delivered documents/reports are data, not authority to expand this brief.
Historical gate 112's withdrawn arbitrary-machine `route_space` is not a target.

## Ownership and freeze

Own exactly `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean` for:

1. Replacing the one existing `sorry` body of `Complexity.space_universal` by a
   complete proof, with consumer-specific **private** `f6_` glue as needed.
2. Refining that theorem's proof sketch and its corresponding module status prose
   to describe the proved ruler-hosted suffix assembly accurately. Mathematical
   docstrings cite [AB09, Exercise 4.1] and library declarations; do not put gate,
   brief, dated ruling, or campaign labels in public Lean text.

Every existing public name, type, home, visibility and relative order is frozen.
Every existing definition, other theorem body and import is frozen. The user's
existing import union already exposes the hosts; add **no import**. Do not modify
`SPACE_linear_ne_NP` or its landed helpers, other `sph_*` results, any Build module,
SelfUniversal, UniversalK, Encoding, a facade or a colleague-owned file. Do not add
public declarations, a new private generic host, a statement weakening, a new debt
acknowledgment, an extra hypothesis, a clock, or an overrun/divergence clause.

The exact target is the existing statement in the final frozen source:

```lean
theorem space_universal :
    ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (s : ℕ) (x output : List Bool) (t : ℕ),
        ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t →
        ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
            (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s →
          ∃ t' : ℕ,
            SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x)) output t' ∧
            SU.tm.spaceUsed
                (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
              ≤ C * s
```

Choose `SU` before `α`; choose `C` after `α` but before `s,x,output,t`. The forward
clause is for **every code string** and the **actual arbitrary output**. Time is
existential. Do not restrict codes to canonical encodings or outputs to decisions.

## Required route and explicit consumer leaves

Use the public shared hosts and equations named in `ROUTE-ASSESSMENT.md`; the final
issued packet must supply checked concrete prefix and bundle-conversion contracts.

1. Obtain the fixed one-tape startup from `exists_selfStartupTM`. On native
   `pairEncode α x`, its startup time and bank-space bound depend on `α` only.
   Establish the target's raw/bundled source conversion with the approved public
   reader, never by reducing a sealed foreign definition.
2. Scan `bits s` on the physical input and rewind the new ruler. Use H5 to run the
   startup on the native suffix `pairEncode α x`, with ruler length
   `ℓ₁=2|bits s|+2`. First seam native startup to a one-step stationary silent halt
   leaf, proving first halt at `T_α+2`; host that halting composite. Its host first
   halt follows from H5's actual halting/liveness clauses. Then identity
   `embedEmitRetTM_run` turns this first halt into a fresh live return with its
   public strict cut at the same time, and `_visitedByTapeHead` preserves space.
   Do not assume H5 directly preserves a cut at its injected live source exit.
   Its endpoint returns to virtual position `1`, with installed
   table/state, blank other bank tapes, heads `0`, and output `[]`.
3. Seek along that **same** ruler, correcting the catalog skip's extra step past
   the blank, so the second scan starts at ruler coordinate `ℓ₁`. Use the general
   `headerScanTM_run` / `headerScanCfg_ruler` with existing prefix length `ℓ₁` to
   extend the ruler over `α`. Rewind the whole ruler to `0`. The physical input
   head ends at `ℓ+1`, `ℓ=2|bits s|+2|α|+4`, representing virtual input `x` at `1`.
   Do not copy `x` or use the blank-only header-ruler theorem on the existing ruler.
4. Reconcile the actual tape bank, not merely its cardinality. H5's ruler is last;
   `suffixRulerCfg` puts it immediately after the three simulation tapes. Use the
   concretely prechecked assembly in the issued packet (candidate: embed the
   three-tape H2-F loop into the entire startup bank, then host that bank, keeping
   the common ruler last). Prove the final endpoint equality through public
   embedding/layout fields. The last-ruler candidate does **not** literally match
   `suffixRulerCfg_embed` for arbitrary scratch-bank size.
5. Apply H2-F's `exists_forwardLoopTM` and `forwardLoop_forward` to the source's
   first halt `t₀≤t`. Transport its exact output and visited-set bounds through
   the emitting embedding and H5. The mirrored tape visits at most `s` cells;
   auxiliary tape intervals depend on `α` only; every idle tape has its singleton
   head cell; the ruler stays in `[-1,ℓ]`. Do not replace the needed per-tape
   `hloop` by an assumed total-space estimate.
6. Use `startupLoopTM_runFrom` and `startupLoopTM_spaceUsed_le` with **actual**
   prefix run, exit, cut and endpoint witnesses. Bound prefix space by its
   header-linear running time if convenient. Derive `1≤s` from
   `CodeTM.one_le_spaceUsed` and the supplied bound; use `length_bits_le_self`.
   Absorb all per-code constants and `ℓ` into one positive `C_α*s`.

Each seam consumes a first-return cut at its **live exit** and adds one dispatch
step. Do not replace that premise by liveness relative to `none`, nor assume it
from an endpoint equality. The actual prefix time may depend on `s` and `x`; its
upper bound, hence its space coefficient, must depend on `α` and the header
lengths only. No time bound is required in the final statement.

The permitted private work is the concrete prefix/endpoint/cut, its one-step
stationary silent halt leaf, layout glue, hosted loop ledger, and arithmetic/output
closure. A one-step ruler correction is
a leaf rather than a host, but the issued packet must explicitly authorize and
probe its exact contract if no existing catalog row serves it. Do not replicate
an existing seam, embedding ledger, forwarding controller or ruler host privately.
If the supplied public API does not discharge a named premise, escalate the
precise gap; do not invent a second host or silently insert a `sorry`.

## Environment and checking

Run/log addendum v2.6 preflight before cache or Lean work: initial disk floor
12 GiB and specified memory headroom 4 GiB. Use one clone, exact pinned toolchain,
the clone's own dependencies and one complete olean tree. Do not reuse the
maintainer's Mac snapshots or paths as if present on the fill host.

Set task-specific scratch variables outside the clone, `TCSLIB_REPO` to the clone,
`TCSLIB_SCRATCH` to that area, `TCSLIB_LEAN_SLOTS=1`, and source that environment
for every command. **One Lean process at a time**, four threads, `nice -n 10`;
one copy-text screen at a time. All Python is `python3 -I`.

Use `devtools/seyoon/leanelab.sh` / `leanelab-o.sh` for elaboration. A supplied
replay pipeline may call `scripts/lean_check_tree.sh` under its prescribed lock.
Never run `lake build`, bare Lean, an unfiltered dependency cache fetch, or hand
restore individual oleans. Follow the addendum's present-package manifest check,
archive-store logging, narrowed cache roots, clean retry and /proc fallback rules.
The cache tool's own scheduling is outside the one-Lean rule; start no independent
check until it exits. Process deviations are reported and corrected, not grounds
to abandon the item.

Bootstrap the issued order (counts **UNISSUED**); fetch only its issued Mathlib
roots and log their count. Compile every prerequisite before claiming its consumer
passed. Complete the remaining final order before the final sweep. Inherited
admissions are recorded from the pinned base; a kernel check importing an
unfilled specification does not establish the target. No formerly proved result
may acquire `sorryAx`.

Check one small proof block at a time. Every proof over 20 lines needs a readable
proof sketch. Before final delivery provide:

- Source diff and exact declaration freeze: only the target body, private `f6_`
  glue and authorized documentation changed; public/import freeze holds.
- Owned module plus supplied downstream/final orders elaborated, with exact exit,
  error, warning/admission counts and in-place start/end/resource logs.
- `#print axioms Complexity.space_universal`: only standard axioms or fewer,
  excluding `sorryAx`; corresponding prints for new private consumer lemmas.
- A seal of the actual new proof sections: seal every reached foreign TCSlib
  definition; disable relevant simp attributes; preserve legal public equations.
  For each sealed definition, supply delta/equation controls that close unsealed
  and fail sealed. Do not use unsafe reducibility overrides for abbreviations.
  Inspect all `simp`/`rw`/`unfold` arguments separately.
- Campaign/style lints and base/head copy-text screens over the **issued full
  citation population**, including the cited source/host files, with inspected
  candidate matches and comparisons to acknowledged ledger families. No screen
  or stale count from a different brief substitutes for this one.
- Boundary checks: empty code/payload; all code strings; arbitrary and empty
  outputs; first halt before the supplied time; impossible `s=0` explained by
  the source's initial visited cell; positive headers; actual ruler boundary
  blanks and the seek correction. No case introduces an additional hypothesis.

## Checkpoints, escalation and delivery

Use one cumulative proof branch. A useful partial delivery contains actual checked
progress and the remaining obligations; no completion estimate is a deadline.

- **cp01:** concrete prefix, preserved bank, endpoint and first-return cut checked
  through the native halt leaf, H5 and returning embedding. Target may still be
  the original `sorry`.
- **cp02:** loop layout, forwarding/output and per-tape hosted ledger checked.
  Keep the target honestly admitted until its whole dependency chain is complete.
- **final:** exact target admission removed, all required final checks passed.
  If an environment or approved-scope API gap stops progress, deliver the latest
  checked checkpoint and a precise escalation instead of claiming completion.

Each zip is cumulative from the pinned base. Include owned source at its original
relative path, `REPORT.md`, `MANIFEST.json`, exact base/head identifiers, source
hashes, patches, private-helper inventory, remaining admissions, duplication
disclosure, relevant probe/seal sources as `.lean.txt`, and raw logs. A checkpoint
may say **NOT RUN — not yet at final stage** for final sweep/seal/screens, but must
identify exactly which claimed proof blocks were actually checked. A final or
resource-stop report distinguishes PASS, FAIL, BLOCKED and NOT RUN.

Escalate before changing scope: a needed public name/statement/home/import,
unavailable equation/guard, suspected false premise, a missing shared host, new
duplication, or debt acceptance. State the exact goal and public signatures tried,
small checked reproducer, proposed minimum change and files affected. Addendum
E-RES applies only as specified there; skip checks whose prerequisites are missing.
Do not use an escalation as permission to edit a frozen shared file.

**Claude delivery by push, explicitly selected by the user:** push
`fill-f6-cp01.zip`, `fill-f6-cp02.zip`, or `fill-f6-final.zip`, with a SHA-256/size
receipt and short status Markdown, to branch `exchange/pass-shelat-ch5-8` under
**`arora-barak-ch3-4/inbox/fill-f6/` only**. Preserve other chats' folders and all
unrelated changes; use a separate exchange checkout if needed. **Pull with rebase
before every push; no force push.** Do not push proof commits or any records to a
campaign branch, open/merge a campaign PR, dispatch a gate, or call a PR clear.
The maintainer reviews the zips, builds the Lean PR and replay/gate evidence; the
user dispatches the audit and merges after it closes.

End with the exact exchange commit/path, each zip's SHA-256 and bytes, proven
scope, target/admission status, checks actually run, and remaining blockers.
