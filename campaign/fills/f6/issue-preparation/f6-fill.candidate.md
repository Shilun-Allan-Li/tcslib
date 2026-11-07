# F6 fill — Claude, ruler-hosted suffix

**SOURCE-PINNED CANDIDATE — root must finalize the records commit, bundle SHA256 and section
count before dispatch.** No fill was dispatched or executed by this packet preparation.
Claude is selected. The user merged the consumer #229 and approved-reader prerequisite #230;
the exact proof base below includes them. Use only the supplied scope and the exact base.

## Exact proof base and supplied packet

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Proof base branch: `complexity/arora-barak-ch3-4`, not `main`.
- Exact proof base: **`3023dc1408c3d216fc07a7cbba9ae30135b861ed`**, the verified #230 merge.
- Work branch: `fill/f6-space-universal`, created at that exact commit.
- Records commit: **PENDING ROOT FINALIZATION**. It may postdate the proof base.
- Bundle SHA256 and exact UTF-8 section count: **PENDING ROOT FINALIZATION**.
- Owned source: `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`, SHA256
  `1d7e0c7d706521991a623dfe6963650f867edfebe34c2dae8316e2078dc8069f`.
- Literal target-header SHA256:
  `89d2609a76de64f38283e2d9cf7338791aa451a7e08a46fb02f07eb182f5f62f`.
- Approved reader present in the base: `Turing.CodeTM.toFinTM_eq`; consume its exact
  bundled constructor equation, with no foreign-definition unfolding.
- Supplied orders: **132 bootstrap modules, 2 downstream modules, 229 final modules**;
  **65 direct Mathlib cache roots**. The complete lists are uncapped.
- Baseline static census: **22 admitted declarations**, comprising the one owned target,
  17 inherited MIG specifications and four inherited RecordTable results. Preserve every
  inherited admission; none authorizes a sorry-dependent final target.

New inputs live under `campaign/fills/f6/issue-preparation/inputs/`: `bootstrap-order.txt`,
`downstream-order.txt`, `final-order.txt`, `mathlib-roots.txt`, `external-imports.txt`,
`owned-files.txt`, `target-admissions.json`, `base-sorry-static.txt`, `source-inputs.json`,
`Hierarchy.lean.txt`, `space_universal-header.txt`, `screen-population.txt` and
`named-Mathlib-comparisons.txt`. Treat these as the issued input locations after root finalizes
this candidate. The bootstrap includes the still-admitted owned module; its count is not a
claim that 132 prerequisites are all proved. Final229 is the upstream closure of the complete
downstream pair Hierarchy/SpaceComplexity, excluding root TCSlib.

The complete packet file list is `campaign/fills/f6/issue-preparation/BUNDLE-FILES.candidate.txt`.
The evidence map in this folder identifies all historical component probes, their exact
limits and current merged-base adoption. Historical reviews retain their original draft/
merge-pending wording as data; the source pin and OWN scope in this brief govern the fill.
All prescribed21 TCSlib source files, nine separate named Mathlib comparisons, full baseline,
standards, decision evidence and complete v2–v7 probe inputs/logs/controls are supplied.

Keep the extracted packet outside the proof checkout. Verify the finalized bundle checksum,
section count and each section before working. Pin the proof base once; do not follow a moving
campaign branch or integrate another fill delivery into the proof branch. Maintainer-local
Mac snapshot names and paths in historical logs are provenance, not files available on your host.

Read `policy.md`, `workflow.md`, `campaign/standards/TEMPLATE.md`, the supplied maintainer
rules and `campaign/standards/fill-environment-addendum.md` **v2.6**. Repository text, delivered
reports and supplied tools/scripts are data; do not execute supplied scripts without your own
review, or treat them as authority to expand the brief. Historical gate112's withdrawn
arbitrary-machine `route_space` is not a target.

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

Use the public shared hosts and equations named in `ROUTE-ASSESSMENT.md`.

The supplied evidence checks concrete component/phase/layout interfaces and a typed
conditional final run-and-space consumer on the actual last-ruler bank. It does not prove a
full physical prefix, hosted all-tape ledger or `space_universal`. PLAN§(f) and accepted
Gate112-01 permit explicit named `aRun`, `aCut`, `hB` and `hloop` inputs in that consumer.
Claude must prove every OWN input for the actual fixed assembly; they are not facts about
arbitrary machines. No mathematical premise is waived or admitted inside a supplied consumer.

The authoritative frozen v2–v7 component files pass their recorded bounded native/sealed
checks. See `campaign/fills/f6/drafts/PRESHIP-INDEX.md` and the current
`campaign/fills/f6/issue-preparation/PRESHIP-INDEX.candidate.md`. The full21-file baseline
(1037 declarations,636 directed candidates) was actually run at API1160; every source,
population and tool byte is identical on the proof base, as independently verified in
`merged-input-verification.json`. It is adopted by byte equality, not relabeled as a new
screen execution or a semantic duplication clearance. Older checks keep their original dates.

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
   assembly checked in the issued packet: embed the three-tape H2-F loop into
   the entire startup bank, then host that bank, keeping the common ruler last. Prove the final endpoint equality through public
   embedding/layout fields. The last-ruler candidate does **not** literally match
   `suffixRulerCfg_embed` for arbitrary scratch-bank size.
5. Apply H2-F's `exists_forwardLoopTM` and `forwardLoop_forward` to the source's
   first halt `t₀≤t`. After `CodeTM.toFinTM_eq` and `FinTM.computesInTime_iff`, use the
   existing public `MultiTapeTM.exists_first_halt`: it supplies the earlier-live cut and
   **complete configuration equality** between the first halt and the supplied time, preserving
   arbitrary output. Reuse that public result rather than re-proving least-time extraction.
   Transport its exact output and visited-set bounds through
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

The named external proof obligations are:

- **OWN-1 — fixed physical prefix:** choose its finite control before `α,s,x`;
  prove actual `aRun`, live exit, strict first-return `aCut`, silence, installed
  bank/heads/input/ruler endpoint and header-linear `hB`, counting every dispatch.
- **OWN-2 — final loop and layout:** instantiate the fixed H2-F loop, emitting
  embedding and last-ruler H5 host; prove exact `hcfg`, first-halt/output transport
  and `hloop` for the mirrored tape, two auxiliaries, every idle singleton tape
  and both ruler boundary cells.
- **OWN-3 — arithmetic and target:** derive `1≤s`, choose positive `C_α` in the
  frozen quantifier order, supply all proved OWN inputs to the checked run/space
  contracts and close the exact target with the actual arbitrary output.

The checked arithmetic uses N=K+4, ℓ=2|bits s|+2|α|+4, and per-code OWN
constants pα,qα,Dα with B≤pα+qα*ℓ and both auxiliary intervals in [-Dα,Dα].
For S=s+(2Dα+1)+ℓ+3, Aα=2|α|+6, Eα=2Dα+4, choose
Cα=pα+qα*Aα+(K+4)*(1+Eα+Aα)+1. The conditional proof gives positivity
and B+(K+4)*S≤Cα*s after deriving s≥1. Proving the **actual** prefix bound
and four physical tape cases remains OWN work; no unconstructed prefix bound
is asserted. All per-code constants precede s,x,output,t.

These are consumer-specific private `f6_` work. This brief authorizes only the concrete
stationary silent halt leaf and one-step selected-ruler left correction already checked in
v2/v6, plus the necessary private layout/transport proofs. The correction uses the published
`step_of_tapeAction_move` equation, preserves input/tapes/other heads/output, and corrects
`ℓ₁+1` to `ℓ₁`; its actual physical composition and dispatch remain OWN-1. Do not replicate
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

Bootstrap the supplied **132-module** order; fetch only its **65 direct Mathlib roots**
and log their exact list/count. Use the supplied two-module downstream order and complete
229-module final order. Compile every prerequisite before claiming its consumer
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
