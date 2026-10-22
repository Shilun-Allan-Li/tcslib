# Review — §13d G4, continuation 3, checkpoint 1 (`Build/ZoneRebalance.lean`), delivery `fill-s13d-g4-cont3-cp1.zip` (megafill B, item 3)

**Verdict: partial (0/2), checkpoint 1.1b complete and verified; landable as a partial.** Both
rows keep their original `sorry` bodies. The delivery characterizes continuation 2's composed
right pass:
- its exact endpoint (`zr_rightPass_post`);
- a stronger tape-0 envelope and the scratch envelope (`zr_rightPass_bounds`), and the supplied
  symmetric envelope (`zr_rightPass_envelope`);
- the bridge to the extended layout (`zr_rightPass_tape`);
- the singleton-exit re-wrap (`zr_rightPassRow`), through one factored adapter
  (`zr_singletonContract`) that now also serves the four inherited composites.

Both supplied statements are proved exactly as stated, with no correction: they are textually
equal to `G4C3Targets.lean.txt`'s, and the supplied examples close by the worker's lemmas.

What passes:
- every integrity, ownership, freeze and hygiene check;
- elaboration at the patched base, at the head and at the campaign tip `b7447492`;
- the axiom and admission walks (`sorryAx` only through the two targets' own bodies);
- my own rule-10 seal (57 definitions, four failing controls) and the rewrite-argument
  inspection; rule 11;
- the import probes (the brief's 439 checks, standalone and in-module; the worker's 445);
- gate 58's level-one values (cells 5–8, heads 7 and −7, time 48), in Lean;
- lint (0 FAIL) and widths;
- the v3 screen: no cross-file pair and nothing at 90% (see (e)).

Findings (none blocking):
- **F1 (record, minor): the citation inventory misses `Turing.two_le_zoneStart`.** The new
  `zr_rightPass_bounds` and `zr_rightPass_tape` cite it. It is in neither the brief's probe nor
  the worker's 445-check probe nor `external-citations.txt`. REPORT lists it among the citations
  "within the supplied inventory", which is not so. Cause: `audit-scope.py` collects only
  namespace-qualified names plus four literals. The lemma is a public theorem
  (`Build/ZoneTape.lean:184`) that resolves from the module (my probes, below), so nothing is
  wrong in the Lean. Only the record is.
- **F2 (record, minor): the shipped rule-10 evidence is weaker than it reads.**
  - `SealCp1.lean` has **no controls**: no `rfl` example that must fail inside the seal and pass
    outside it.
  - `rewrite-audit-cp1.txt` is five lines of fixed text, written by `audit-scope.py`, and lists
    no argument. The shipped script writes "The **49**-definition seal", while the shipped file
    says 57, so the script that produced the file is not the one shipped.

  My seal (with controls) and my argument inspection, in (c), replace both. Both checks pass.
- **F3 (cosmetic, record):**
  - `logs/g4/package-cp1.log` is empty (0 bytes; its hash is the empty-file hash).
  - `evidence/g4/Work.lean` is a stale development copy: its status paragraph and one line
    wrap differ from the delivered file.
  - REPORT counts the probe as "445 total". It is **445 checks of 434 distinct names**, and the
    supplied "439 checks" are 428 names (gate 58, row 15).
  - REPORT's item-start disk (25,530,646,528 B) differs by 4,096 B from the shipped log's
    (25,530,650,624 B).
- **N1 (carry-forward to 1.2): sequencing the re-wrapped pass needs a `DecidableEq` instance
  that default synthesis does not find.** `Contract.seq` takes `[DecidableEq S₁]`, and the pass's
  state type is a 12-leaf nested sum. With the default `synthInstance.maxSize` (128),
  `#synth DecidableEq …` fails. It succeeds with `maxSize 256`, or with an explicit
  `instDecidableEqSum` term. With that instance, `(zr_rightPassRow x).seq (skipTM_contract 0 x) …`
  elaborates, and the un-wrapped pass still does not (`out/deceq*.out`, `out/targets-1_1b.out`).
  Each later seam makes the state type larger.
- **N2 (duplication drift):** the new top pair, `zr_rightPass_bounds` against `zr_rightPass_time`
  at 85%, is two long `simp only` lists over the same composite. The left pass's time and bounds
  would add a third instance; see (e).

## Inputs

| Input | Identity |
|---|---|
| Item zip | `$S/inbox-megaB/zip/fill-s13d-g4-cont3-cp1.zip`, SHA-256 `fe1398e55eca7625fc437b1153326e8b286da16403999e876648f052c71315e9` (= the dispatch's `fe1398e5…c71315e9`), 254,992 B, 71 entries, CRC OK (`zip-sha256-check.txt`) |
| Extraction | `$S/inbox-megaB/fill-s13d-g4-cont3-cp1/`: byte-equal to a fresh unzip (`unzip-vs-delivered.txt`) |
| Session report, recovery JSON | `$S/inbox-megaB/zip/megafill-b-REPORT.md` (`433498…`), `recovery-verification.json` (`bb625c…`), both OK against the zip folder's `SHA256SUMS` |
| Brief | dispatch copy `a82d2399…36de2`: read at `exchange/outbox/fills/`, moved to `exchange/archive/fills/` during this review, same hash. Equal to `campaign/fills/s13d/briefs/s13d-fill-g4-cont3.md` with its three `@ANCESTOR@` replaced by the base (`brief-check.txt`). The worker's `attachment-verification.log` records the same five hashes and a match for each |
| Cover, addendum | `megafill-B.md` `4e2e5a93…` (`exchange/archive/fills/`; equal to the repository copy with `@ANCESTOR@` replaced); addendum v2.4 `42555a4f…`, the same in `campaign/standards/` and in the outbox |
| Inputs | `campaign/fills/s13d/inputs/s13d-fill-g4-cont3/` (the patches, the probe, `G4C3Targets.lean.txt`, the population), the order list and the logs. All unchanged from the base to the records head I read them at (`wt-hk` at `34af2e0f`) |
| Base | `6cfee54474e3d954e3395f9d9eab5d025452a8dd` (TCSlib `268944d6` = `2ff214c5`'s), plus PR #143's two commits by `git am`: `875d59d5` and `67966e55` (owned blob `e8353f20`) |
| Head | `refs/review/g4-cont3` = `01bcc6e08d977a7a33a181dd2b7ef72c0828cf12`, fetched from the bundle |
| Tip | `b7447492` (#143 merged; #139 merged as `3732776e`), fetched just now |
| Snapshot | `$S/oleans-lg4c2` (#143's tree for `Build/ZoneRebalance`'s upstream). None of the three files changed from `c60ed898` to the tip is upstream of the owned file (`closure-tip.txt`) |
| Worktrees | `wt-pbase` (`67966e55`), `wt-head` (`01bcc6e0`), `wt-tip` (`b7447492` with the worker's commit applied by `git apply`, uncommitted). Each has the `.lake/packages` link |

Every path below is relative to `$S/review/g4-cont3-fill/out/` unless it says otherwise.
- Lean ran only through `tools/leanelab.sh`, one elaboration at a time, every probe against
  `oleans-lg4c2`.
- The screens ran one at a time, each only when no other screen ran, under `nice -n 10`
  (`scripts/run-screens.sh`).
- No build or cache command was run.
- The shim `evidence/runtime/executable-path.c` (`985924ad…4fba7`) was neither compiled nor run.
- Every delivered Lean file was read first. The probes I ran are my own files (`../probes/`);
  the only delivered Lean text I elaborated is the module and the worker's import probe
  (`#check` lines only).

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | `SHA256SUMS` | PASS: 70/70 OK, covering every member except itself. The recovery JSON's claims hold: G4's sum, size, 71 entries, 70 verified and CRC; U2-S's 122/122 and F5's 92/92 | `internal-sha256-check.txt`, `recovery-claims-siblings.txt` |
| 2 | Bundle | PASS: `verify` okay; sole prerequisite `6cfee544…`; head `fill/s13d-g4-cont3` = `01bcc6e0…` | `bundle-verify.txt` |
| 3 | The applied commits | PASS: the bundle's first two commits `875d59d5` and `67966e55` have the patch-ids of #143's `4b76f0ff` and `c60ed898` (and of the input patches). Their blobs are `77c9119d` and then `e8353f20`, as the brief prescribes. Delivered patches 0001/0002 differ from the inputs only in their `From` hashes, the subject's `n/3` and the git version line | `patches-identity.txt` |
| 4 | Patch series = bundle = file | PASS: the three patches applied at the base give the head tree `39dd231a`, whose owned blob `1abbb871` is the delivered file's | `patch-series-check.txt` |
| 5 | Worker's commit | `01bcc6e0`, author "Codex", parent `67966e55`; touches only `Build/ZoneRebalance.lean` (+227/−25) | `head-commits.txt` |
| 6 | Owned regions | PASS, 0 lines outside. The home (a), read as 127–1149 per gate 58: the adapter inserted at 127, the four re-pointed adapters (base 690–694, 781–786, 906–910, 972–977), and 204 lines inserted before `/-! ### The rows -/`. The extension's status paragraph (c), base 1232–1234. Both `sorry` bodies untouched | `regions.txt`, `worker.diff` |
| 7 | Freeze (`declfreeze.py`) | PASS: 18 → 18 public, none added or removed, no `STATEMENT CHANGED`. Only `exists_zoneExtendTM`'s status paragraph changes (authorized). `exists_zoneRebalanceTM` is byte-identical | `declfreeze.txt` |
| 8 | Privates | 65 → 73: 8 added (all `zr_`), none removed. Changed: exactly the four re-pointed adapters (`privstmt.py`: no statement change). Their elaborated types are identical at the base and the head | `declfreeze.txt`, `privstmt.txt`, `types4-diff.txt` |
| 9 | Adapter (gate 58, row 17) | PASS: all four inherited instances (`zr_rightSeekBackContract`, `zr_rightRulerContract`, `zr_adjustedWalkContract`, `zr_adjustedBackContract`) and the new `zr_rightPassRow` call `zr_singletonContract`. The old `simpa only [Set.image_singleton, Option.map_some] using R.segment/exit_mem` pattern is gone. No new `copyMapTM_contract` instance: the half writes reuse `zr_halfCopyContract` | `adapter-repoint.txt` |
| 10 | Hygiene (added lines) | PASS: no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `change`, `set_option`, `open`, `section`, `variable`, attribute or `native_decide`. `decide` only on `Fin 2` disequalities. `rfl` only at 1199 (`split_ifs <;> first \| rfl \| omega`) and 1249 (after `subst j`), both sealed in (c). No host or trace word (`runFrom`, `Round`, `iterate`, `inPhase`, `Traj`, …) | `hygiene.txt` |
| 11 | Imports | PASS: unchanged (lines 6–9) | `hygiene.txt` |
| 12 | Admissions | PASS: `sorry` only at 1408 and 1449, the two targets' original bodies | `hygiene.txt` |
| 13 | Size | 1,370 → 1,572 lines; 18 public / 65 → 73 private (lint INFO line; REPORT agrees) | `lint-build-head.out` |

**The 12 new or changed privates** (head lines):
- new:
  - `zr_singletonContract` (130, `abbrev`, generic over `n Γ S I x`);
  - `zr_halfCopy_post` (1150);
  - `zr_writeHalves_post` (1172);
  - `zr_rightPass_post` (1214);
  - `zr_rightPass_bounds` (1265);
  - `zr_rightPass_envelope` (1303);
  - `zr_rightPass_tape` (1318);
  - `zr_rightPassRow` (1346, `abbrev`);
- re-pointed: `zr_rightSeekBackContract` (696), `zr_rightRulerContract` (786),
  `zr_adjustedWalkContract` (903), `zr_adjustedBackContract` (970).

REPORT's inventory matches, name by name and role by role.

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 14 | Head against `oleans-lg4c2` | PASS: exit 0, 0 errors; warnings only `:1396:8` and `:1439:8` `declaration uses 'sorry'` (the two targets); 10 s | `elab-head-lg4c2.out` |
| 15 | Patched base (baseline) | exit 0; `:1195:8`, `:1237:8` (the same two targets; the pre-ship log's lines) | `elab-pbase-lg4c2.out` |
| 16 | Tip `b7447492` + the worker's commit | PASS: identical to row 14. The seal in (c) gives the same result at the tip | `elab-tip-lg4c2.out`, `seal-tip.out` |
| 17 | Axioms (in-module copy; `#print axioms` for all 73 privates and both targets) | PASS (partial). The 12 new or changed privates: each `[propext, Classical.choice, Quot.sound]`, name for name the worker's `seal-axioms-cp1.log`. Both targets: `[propext, sorryAx, Classical.choice, Quot.sound]`. The tally over all 75: 55 / 9 / 8 / 1 within the three standard axioms, and the two targets | `axioms-summary.txt`, `axkinds-head.out` |
| 18 | Admission walk | PASS: `exists_zoneRebalanceTM: [Turing.exists_zoneRebalanceTM]`, `exists_zoneExtendTM: [Turing.exists_zoneExtendTM]`. All 73 privates: no `sorryAx` user in their closure | `axioms-summary.txt` |
| 19 | External privates, equation lemmas | none reached from any private (73/73 `EXT` lines clean); 106 TCSlib constants reached from the 12 | `axkinds-head.out`, `extlist-new12-tcslib.txt` |
| 20 | The brief's probe `G4C3ImportProbe.lean.txt` (439 checks of 428 names), **standalone**: `import …Build.ZoneRebalance` plus its 439 `#check`s | PASS: 439 outputs, 0 errors, 0 warnings. The import resolves to `oleans-lg4c2`'s module (#143's). Its public interface equals the delivered module's (row 7: the same 18 public statements; the delivery adds only privates) | `G4C3BriefProbeStandalone.out` |
| 21 | The same 439, **in-module** (appended to the delivered module), plus `#check @Turing.two_le_zoneStart` | PASS: 440 outputs, 0 errors, only the two target warnings (1396, 1439). This is the closest run to "standalone on the delivered module" that leanelab allows (it writes no olean) | `G4C3BriefProbeInModule.out` |
| 22 | The worker's `ImportProbe.lean` (445 checks of 434 names: the 428 plus six core or Mathlib lemmas), plus `two_le_zoneStart` | PASS: 446 outputs, 0 errors, 0 warnings. The worker ran it against its own olean of the delivered module (`probe-cp1.log`, exit 0) | `G4C3WorkerProbePlus.out` |
| 23 | Cited beyond the probes (F1) | Of the 106 TCSlib constants reached from the 12, the only one absent from the worker's probe is `Turing.two_le_zoneStart` (public theorem, `Build/ZoneTape.lean:184`; resolves, rows 21–22) | `extlist-new12-not-in-probe.txt` |

## (c) Correctness of checkpoint 1.1b, and rules 10 and 11

**What is proved.** For `D = ⟨n, z⟩` (so `ℓ = n + 1`), write `s = zoneStart ℓ`,
`m = zoneCapacity n = 2^ℓ` and `q = d.workTapePos 1`. From `(zr_rightPassContract x).pre D d`,
which is exactly `zoneRowPre ⟨ℓ, z⟩ d` (`zr_rightPass_pre`):
- **Endpoint** (`zr_rightPass_post`).
  - The state is `some (inr (inr (inr done)))`.
  - Tape 0 holds `inr (· ↦ some none)` on `[s, s + m)` and `inr (· ↦ none)` on `[s + m, s + 2m)`.
    Every other cell is unchanged.
  - Tape 1 holds `inl false` on `[q, q + m)` and is unchanged elsewhere.
  - The tape-0 head is at `s + m`. Every other head and field is unchanged.
- **Envelopes** (`zr_rightPass_bounds`).
  - Tape 0: `0 ≤ lo₀` and `hi₀ ≤ s + 2m`. The latter is `zoneStart (ℓ+1) − 1`, so it lies inside
    the row's box; `zr_rightPass_envelope` is exactly the supplied `±zoneStart (ℓ+1)`.
  - Tape 1: `q − 1 ≤ lo₁` and `hi₁ ≤ q + m + 1`, the brief's ruler cells. These are bounds
    stated in Lean, not hand estimates.
- **Bridge** (`zr_rightPass_tape`): tape 0 equals `zonedTape (fun t => (z t).extend)` at every
  `q ≥ 0` and `zonedTape z` at every `q ≤ 0`. It comes from `zonedTape_extend`, a published
  theorem, with `abs_of_nonneg`.
- **Re-wrap** (`zr_rightPassRow`): `zr_singletonContract` at `{some (inr (inr (inr done)))}`. It
  is `Contract.ofSegment R.pre R.time R.post R.lo R.hi`, with the segment and exit proofs
  transported along the exit-set equation.

**Against the supplied statements** (`stmt-compare-1_1b.txt`, `targets-1_1b.out`, probe
`../probes/G4C3Targets.lean`; 0 errors, only the two target warnings):

| Check | Result |
|---|---|
| Statements of `zr_rightPass_post` and `zr_rightPass_envelope` against `G4C3Targets.lean.txt`'s targets 1 and 2 | **textually equal** (whitespace-normalized); no correction was needed |
| The two supplied `example`s, verbatim, with `sorry` replaced by `exact zr_rightPass_post D d hp` and `exact zr_rightPass_envelope D d hp` | PASS |
| **Level one (gate 58, note 11):** `D = ⟨0, z⟩`, `q = −7` | PASS. State `inr (inr (inr done))`; cells 5, 6 `inr (· ↦ some none)`; 7, 8 `inr (· ↦ none)`; 4 and 9 unchanged; ruler cells −7, −6 `inl false`, with −8 and −5 unchanged; heads 7 and −7; time 48. Envelope: tape 0 in `[0, 9]`, inside `±10`; scratch in `[−8, −4]` |
| Bridge against the frozen specification | PASS. For `q ≥ 0`, tape 0 after the pass equals `(zoneExtendPost done ⟨ℓ, z⟩ d').workTapes 0 q`: on the nonnegative half-line the right pass already *is* the row's endpoint. For `q ≤ 0`, it equals `d.workTapes 0 q`, which gives the second seek's local agreement on `[−zoneStart ℓ, 0]` (gate 44, note 9) |
| Scratch frame for the left ruler (gate 58's carried point) | PASS: off `[q, q + m)` scratch is blank (`none`) after the pass |
| Re-wrap preserves the fields | PASS: `pre`, `time`, `post`, `lo`, `hi` of `zr_rightPassRow` equal the pass's, by `Contract.ofSegment_*` (published) only |
| Re-wrap composes | PASS, with an explicit `DecidableEq` (N1): `(zr_rightPassRow x).seq (skipTM_contract 0 x) …` elaborates, and the same with `zr_rightPassContract` fails (`fail_if_success`) |

**Proof route.** The endpoint is assembled from published pieces, with no hand trace:
- the seam endpoint equations (`Contract.seq_post`, `Contract.ofSegment_post`);
- the inherited sub-composite endpoints (`zr_rightRuler_post`, `zr_adjustedBack_post`);
- the constant-copy cell formula (`zr_constantCopy_cell`, via `zr_halfCopy_post`);
- the `Cfg.mapState_*` field equations.

The envelope unfolds only this file's composites, then reads the catalog rows' `lo`/`hi`/`post`
equations and `seekPost`/`sweepPost` fields, with `zr_right_offset`, `zoneStart_succ`,
`two_le_zoneStart` and `zoneCapacity_eq`. No row's trace is re-walked: no `runFrom`, `Traj` or
`Round` occurs in the added lines.

**Rule 10 (no unfolding of other files' definitions).**
- **Seal test** (`../probes/G4C3SealHead.lean`, `scripts/mkseal3.py`; result `seal-head.out`).
  - **Method.** The whole home, head 127–1350 (all 73 privates, the adapter included), runs
    inside a section with `attribute [local irreducible]` on 57 other-file definitions
    (`seal-list.txt`). That is my dependency walk's 53 semireducible, non-projection,
    non-matcher TCSlib definitions reached from the 73 privates (`sealcand-all.txt`), plus the
    worker's four extra (`Action.apply`, `Cfg.SameOutside`, `framedContract`,
    `sweepContract`). It equals the worker's 57.
  - **Controls.** Four `rfl` controls sit inside the section: a catalog field
    (`skipTM_contract … .time = w.length + 1`), `zoneStart 0 = 2`, the adapter's `post` read
    through `Contract.ofSegment`, and the pass's `time` read through `Contract.seq`. **All four
    fail inside and pass outside.**
  - **Result.** The only errors are the four controls; the two target warnings are the only
    warnings. Nothing in the home fails. This covers the two `rfl` closings (1199, 1249) and the
    `exact` at 1163: none closes by reducing a sealed definition.
- **Argument inspection** (`rwargs.txt`, `kinds.txt`). The added `rw`/`simp`/`simpa` lists hold
  95 identifiers, each resolved in-module.
  - Every TCSlib name among them is a **theorem**. So are the other external citations I added to
    the list (`Cfg.ext`, `Contract.segment`, `Contract.exit_mem`, `zoneStart_succ`,
    `two_le_zoneStart`). By module: 6 from `Contract/Basic`, 20 from `Contract/Catalog`, 4 from
    `Contract/Seam`, 5 from `StateRenaming`, 1 from `Configuration`, 4 from `ZoneTape` and 1 from
    `Zone`.
  - Every definition passed is this file's own: the `zr_` contracts, words and `zr_cellPost`.
  - The rest are locals, or core and Mathlib lemmas.
  - There is no `unfold`, `delta`, `change` or `show` on another file's definition. The three
    other-file definitions in my `#kinds` list (`Contract.ofSegment`, `zonedTape`,
    `ZoneContents.extend`) are my additions. They occur only as a constructor application and in
    statements.
- **Design note (not a finding).** `zr_singletonContract` and `zr_rightPassRow` are `abbrev`s,
  so `simp`/`rw` with `Contract.ofSegment_*` match through them at reducible transparency. This
  unfolds only this file's definitions. If the adapter is promoted, it should become a `def`
  with non-`simp` `simps` field lemmas, the contract layer's convention.
- **Rule 11.** No R3 row in the diff (`hygiene.txt`); no external private reached (row 19); all
  new names `zr_`.

## (d) Escalations and promotion candidates

**Escalations: none, and I agree.** Nothing in 1.1b needed a missing lemma. N1 is an instance
limit, not an obstruction: it has two tested remedies.

**Promotion candidates** (REPORT's list; my assessment):
- **`zr_singletonContract`: the strongest new candidate.** It is generic (any contract whose exit
  set equals a singleton), and every composite needs it. It belongs in `Build/Contract/Basic`
  beside `Contract.ofSegment`, or as a `Contract.seq` corollary in `Build/Contract/Seam` that
  returns `{some (Sum.inr e)}` directly. Promote it as a `def` with `simps` (see (c)), through an
  API PR.
- `zr_halfCopy_post` is zone-specific: a constant-merge instance of `zr_constantCopy_cell`, which
  remains the generic candidate.
- `zr_rightPass_post`/`_bounds`/`_tape`, `zr_rightPassRow`: zone-specific. They stay private
  until the row is filled (ruling 5).
- Inherited, unchanged: the one-cell leaf, the layout bridges, the ruler builder, the mirror,
  and the adjusted walk. The adjusted walk is still to be parametrized by direction (1.3).

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 24 | Screen v3 script | SHA-256 `f4feac91…d878f181`, the same at the patched base, the head, the tip and in the main repo | `screen-script-sha.txt` |
| 25 | Before (patched base, the brief's 10-file population) | `838; 478; 137,237 chars` (exit 0, 315 s). Byte-equal to the worker's `screen-before.txt` and to `campaign/fills/s13d/logs/s13d-fill-g4-cont3-screen-base.txt` minus its comments | `screen-before.txt`, `.status` |
| 26 | After (head) | `846; 477; 136,473 chars` (exit 0, 316 s). Byte-equal to the worker's `screen-cp1.txt`. The tip with the worker's commit has the same population text, since `StepClock` is not in the population | `screen-after.txt`, `.status` |
| 27 | New pairs (`pairdiff.py`, by name) | **5 new, all in-file; no cross-file pair with a `ZoneRebalance` side; nothing at 90% or above: "new copies: none" holds.** 6 pairs gone (the old adapter pairs, 51–66%). The 5 are line for line REPORT's table. The accepted `zr_pair_pass`/`zr_inPass_out` pair (72%/62%) is unchanged. `zr_singletonContract` and `zr_rightPassRow` pair with nothing | `screen-compare.txt` |

On the pairs:
- **The top pair, 85%** (N2): `zr_rightPass_bounds` reproduces `zr_rightPass_time`
  (`top-pair-shared.txt`). The shared text is:
  - the declaration header;
  - the composite-unfolding `simp only` prefix: 23 of `zr_rightPass_time`'s 30 arguments. These
    are the 14 own sub-contract names (`zr_rightPassContract` … `zr_cellContract`),
    `zr_rightFields`/`zr_rightWord`/`zr_rulerWord`, four `List.length_*`, `zoneCells_length` and
    `zr_right_offset …`;
  - the `Contract.seq_`/`ofSegment_`/`…TM_contract_` stems.

  The arguments differ only in the field suffix (`_time` against `_lo`/`_hi`/`_post`). No proof
  idea is copied: REPORT's justification is accurate. It is the closest new pair to 90%, though,
  and a left-pass `time`/`lo`/`hi` written the same way would make a third. Hence the
  carry-forward: per-stage field lemmas, combined.
- **The others (53–61%)** share the seam-precondition projections (`Contract.seq_pre`,
  `Cfg.mapState_*`) with `zr_rightPass_pre`/`zr_rightRuler_pre`. They are as REPORT says.
- **The adapter (gate 58, row 17).**
  - The former 81% top pair (`zr_rightRulerContract`/`zr_rightSeekBackContract`) is now 63%.
  - The 80% pair `zr_halfCopyContract`/`zr_rulerCopyContract` is unchanged: two
    `copyMapTM_contract` instances, no third added.
  - The helper itself pairs with nothing, so no re-pointed instance drifted toward it.
- **Known hazards:**
  - no pair with `Build/RecordTable` (`rt_copyMachine`/`exists_fieldsCopyTM`);
  - none with `Build/Zone`'s cascade family;
  - no mirrored direction yet;
  - no contiguous layout copy (nothing to reconcile with F3's clock writer).

| # | Check | Result | Evidence |
|---|---|---|---|
| 28 | Lint, `TuringMachine/Build` (the brief's scope) | PASS: `0 FAIL, 31 WARN over 39 files`, the patched base's count. The only changed lines are the size WARN and INFO (1370 → 1572; 65 → 73 private). Line-equal to the worker's `lint-cp1.txt` | `lint-build-pbase.out`, `lint-build-head.out` |
| 29 | Widths | PASS: added lines at most 97 characters, file at most 99; no double blank line, no trailing whitespace | `widths.txt` |
| 30 | Docstrings | All 8 new declarations have one. Seven carry a literal "Proof sketch". The exception is `zr_rightPassRow`, a one-line `abbrev` | `public-text.txt` |
| 31 | Public-facing text | PASS: the 30 added docstring lines and the 4-line status-paragraph change carry no campaign label (G4, §13d, checkpoint, 1.1b, brief, gate, finding, round, escalation, rule), path, date or session narrative | `public-text.txt` |

**The status paragraph** is true and mathematical. Optional landing rewording, for precision (it
names the ruler left on scratch and where the head stops):

> **Implementation status.** A positive-level right-pass contract composes the seek, skip,
> ruler copy, half-zone writes, adjusted walk and scratch rewind, with its exact precondition and
> time (the right-layout extent plus ten half-capacities and twenty-three control steps). Its
> endpoint is proved: the new right zone holds virtual blanks in its inner half and empty slots
> in its outer half, every other cell of tape `0` is unchanged, a ruler of the half-capacity is
> left on scratch, and the zoned head stops at the new zone's midpoint with the scratch head
> restored; both head envelopes are bounded. The left displacement, an unadjusted walk followed
> by an adjusted walk across the separating blank, is proved as arithmetic. The return-home
> rounds, the left pass, the zero-level branch, ruler cleanup and the assembly of the complete
> extension remain open. Only this target's body is admitted.

Optional docstring touch: `zr_rightPassRow`'s "The characterized right pass with its nested image
exit normalized to one live exit." can read "The right pass with its nested-image exit set
normalized to a single exit." The rebalance paragraph stays as it is.

## (f) Environment and the interruption

**Setup (shared, verified from the shipped logs):**
- **Preflight** (05:10:08Z): `nproc` 9; overlay filesystem; 23,909,351,424 B free (floor 12 GiB);
  `memory.max` 8,589,934,592; anon + kernel + shmem 294,219,776, so the headroom is
  8,295,714,816 (floor 4 GiB); OOM 0/0. **PASS.**
- **Lean**: the pinned 4.25.0 failed with `failed to locate application`; the Part 2 shim (hash
  as authorized) then gave `Lean (version 4.25.0, … cdd38ac5…)`.
- **Cache**: one filtered fetch for the queue. The roots are **40, identical to my own extraction**
  from the 95-module union of the three order lists (`mathlib-roots-check.txt`). 35 new
  downloads, 1,002 files, exit 0; the cache executable's own 17 jobs are not a `lake build`.
- **Item 3's bootstrap** (07:00:34–07:09:39Z): **95/95 runs, exactly the order list in order**,
  all exit 0, 0 error lines. 33 sorry warnings in 14 modules, name for name the campaign's base
  set. Summed wall 547.333 s, peak RSS 2,967,624 KiB (`bootstrap-check.txt`).
- **The checkpoint's checks** (07:21–07:30Z): owned file and facade exit 0; seal, axioms and probe
  exit 0. Then commit 07:31:07Z and zip 07:31:14Z (`cp1-*.log`, `seal-axioms-cp1.log`,
  `probe-cp1.log`; zip entry times 09:31 +02:00).

**The interruption.** The workspace was found gone at 16:29:20Z (`recovery-verification.json`:
clone, toolchain and runtime absent). The cause is unknown, and the shipped logs, which all end by
07:31:14Z, hold no evidence of one:
- no OOM: `oom`/`oom_kill` were 0 at the preflight, and the peak RSS was 2.97 GB of 8 GB;
- no disk floor reached.

One observation, not a cause: the overlay's "Used" counter is not the session's alone
(`environment-disk-trend.txt`).
- It went 8.13 GB at the preflight, 12.38 GB before the cache, 14.48 GB at F5's start (06:15),
  then **6.50 GB** at G4's start (07:00).
- G4's bootstrap at 07:00–07:09 still found the toolchain and the Mathlib cache.
- The cgroup's `memory.events` `max` was already 85,641 at the preflight, before any of this
  session's work, with `memory.current` 7.09 GB, mostly file cache. These are limit-reached
  (reclaim) events, not an OOM.

Both fit a host-managed scratch that can be reclaimed. The session report's account (an
environment loss, not a resource-floor failure or OOM) is consistent with the records.

**Is the checkpoint complete and self-consistent?** **Yes.** It has everything the brief's
checkpoint zip asks for:
- REPORT and source;
- the three-patch series starting with the two applied commits, and the bundle on the base;
- the bootstrap log, and the final check (the owned file and the facade, which the brief permits);
- the axiom log, both screens and `SHA256SUMS`.

The source, patches, bundle and evidence agree with one another, and with my re-runs (rows 4,
14, 17, 20–22). Its gaps are records only (F1–F3). Checkpoint 1.2 was in progress and did not
survive. Nothing of it is claimed, and nothing of it is in the archive (no stray declaration, no
draft).

**The sweep (check 7).** No full 95-module final sweep ran after the checkpoint, only the owned
file and the facade. What that leaves unchecked:
- The change touches only `Build/ZoneRebalance`. Its downstream closure is exactly
  `{Build/ZoneRebalance, TuringMachine}` (the root `TCSlib` is excluded), and both were checked
  at the head.
- The other 93 modules of the order list are not downstream of the change. Their elaboration
  cannot differ from the bootstrap's, which ran on the same sources, all exit 0, with the base's
  33 sorries.
- So the omitted sweep could only have re-confirmed the sorry count. That count is 33 by
  construction, since the head has the same two target sorries (row 14).

The landing replay re-runs both downstream modules at the merged tip, so it covers the sweep.

## (g) Landability at the tip `b7447492`

- **The worker's commit applies at the tip.** The tip's owned blob is `e8353f20`, the worker's
  parent's, because #143's merged commits are patch-id-equal to the two `git am` commits.
  `git apply` of patch 0003 at `b7447492` is clean, and the result is byte-equal to the delivered
  file, blob `1abbb871` (`patch-at-tip.txt`).
- **Cherry-pick only `01bcc6e0`.** Do not cherry-pick or push the bundle's first two commits:
  they are #143's patches under new hashes, already merged.
- **Elaboration at the tip:** identical to the head (row 16). The tip differs from `lg4c2`'s
  tree in `Build/InputWindow`, `Build/StepClock` and the facade, and none of them is upstream of
  the owned file.
- **Replay closure** (`closure-tip.txt`, `replay-merged-closure.txt`).
  - **Minimal: `Build/ZoneRebalance`, then the facade `TCSlib/Complexity/TuringMachine`** (2
    modules), chained from a snapshot of #143's merged tree, as gate 58 says. None exists yet.
    The first is the pending **`lsk2`**: #144 at the merged state after #139 and #143,
    `fills/replay/replay-lsk2.sh`, prepared and not yet run. Its list is exactly my merged-tree
    closure below, and its pins differ from this landing's only in `ExhaustiveReplay`
    (#144's docstrings) and `ZoneRebalance` (`replay-pins.txt`). `ExhaustiveReplay` is upstream
    of neither module.
  - **Not yet usable: `oleans-lsl`.** The existing snapshot is the 14-module replay at
    `7cd01f84`, taken before #139 and #143. Its re-preparation is half done:
    `fills/replay/down-lsl.txt` now lists 17 modules (with `SeamLayout`, and `ZoneRebalance` at
    `e8353f20`), while `replay-lsl.sh` still checks for 14. Once re-run on the merged tree, it
    would serve equally, if #145 lands first.
  - **Merged-tree method, from `oleans-l132b`:** the downstream closure of every `.lean` file
    changed since `e9e97970` (11 files, with `ZoneRebalance` pinned at `1abbb871`). That is
    **16 modules**: `StepClock`, `ExhaustiveReplay`, `ClassNP`, `NTimeHierarchy`,
    `Diagonalization`, `WindowRun`, `WindowClock`, `SpaceComplexity`, `BufferWords`,
    `InputDevice`, `InputWindow`, `Rewind`, `ZoneRebalance`, `UniversalK`, `SelfUniversal` and
    `TuringMachine`. The root is excluded.
  - **Why not chain from `lg4c2`.** Of the 11 changed files, six are upstream of the facade:
    `BufferWords`, `InputDevice`, `InputWindow`, `Rewind`, `StepClock` and `ZoneRebalance`
    (`facade-vs-changed.txt`). `lg4c2` predates #137's `InputWindow` and #139's `StepClock`, so
    a facade replay from it would read stale oleans. `lsk2`'s list, and the re-prepared
    17-module `lsl` list, rebuild all six.
  - The facade could not be elaborated here: there is no olean of the delivered module.
- **Overlap with open work** (`closure-overlap.txt`, `open-prs.txt`, `sibling-items-files.txt`):
  - **#145** (the seam layout's landing: `Build/SeamLayout` and the facade's line), **U2-S
    cont1** (`UniversalK` only) and **F5 cont1** (`Build/InputDevice` only, upstream of
    `UniversalK`) meet this landing only at the facade, the last module of every replay. That is
    the standing facade-only rule: no re-replay.
  - **#144** (`ExhaustiveReplay`, docstrings) shares nothing.
  - None of them touches `Build/ZoneRebalance`.
  - #135 (chapter 7 into `main`) is on another base.
- **Sorry count after landing:** unchanged (the same two targets; the campaign total is
  unchanged).

## (h) Recommendation and continuation 4

**Not yet clear to merge**: the landing PR is still to be opened, replayed and gated.

**Land checkpoint 1 as a partial: yes** (a new PR, e.g. `lean/g4-cont3-partial`, based on the
campaign branch at `b7447492`, not stacked).
- It is the characterization every later checkpoint (1.2, 1.3, 1.6) needs.
- It is private, sealed, admission-free and verified at the tip.
- Holding it for continuation 4 would gain nothing, and continuation 4 needs a new environment
  anyway.

PR body points:
- **Commit.** Cherry-pick `01bcc6e08d977a7a33a181dd2b7ef72c0828cf12` (from `refs/review/g4-cont3`,
  bundle prerequisite `6cfee544`). Only that commit; its diff applies cleanly at `b7447492`.
- **What it adds:**
  - 8 private `zr_` declarations: the adapter, the half-write and right-pass endpoints, the
    envelopes, the bridge, the re-wrapped row;
  - 4 adapters re-pointed;
  - the extension status paragraph updated.

  No public declaration and no admission; 1,370 → 1,572 lines, 18 public / 73 private.
- **Optional maintainer commit:** the status-paragraph rewording and the `zr_rightPassRow`
  docstring in (e). After it, re-elaborate (expect `:1396`/`:1439` only, unless the line count
  moves), re-lint, and re-screen the population (docstring-only: expect the same pair set).
- **Review table:**
  - integrity 70/70 with the bundle and the patch series;
  - owned regions only;
  - tip elaboration;
  - axiom and admission walks;
  - seal 57 with 4 controls;
  - probes 439 standalone and in-module, and the worker's 445;
  - level one in Lean;
  - lint 0 FAIL / 31 WARN;
  - screen (e).
- **Replay:** `Build/ZoneRebalance`, then the facade, into a copy of the current merged-tree
  snapshot: `oleans-lsk2` once it passes, or a re-run `oleans-lsl`, but not today's
  `oleans-lsl`, which predates #139 and #143. The precheck pins `ZoneRebalance` at `1abbb871`
  and the snapshot's other ten pins. **Fallback:** the 16-module merged-tree replay
  from `oleans-l132b` (`replay-merged-closure.txt`, `replay-pins.txt`). The replay worktree needs
  the `.lake/packages` link.

**Continuation 4 should carry forward:**
1. **1.2, the return home** (it was in progress; nothing survived).
   - **The route:**
     - `skipTM` over the outer half: from `s + m`, over `m` non-blank cells, to
       `s + 2m + 1 = zoneStart (ℓ+1)`. Its premise should follow from `zr_rightPass_post` and
       `zonedTape_blank_outside`: cell `s + 2m` lies beyond the old layout. This is unchecked
       route guidance;
     - then `Round.iterate` over `skipBackTM` rounds built by `round_iff`, each with a one-cell
       home test (the unique one-cell field), and an anchor distinct from `skipBackTM`'s run
       state.
   - **N1:** give `Contract.seq` the `DecidableEq` of the pass's state type explicitly. Two forms
     work: a private term built from `instDecidableEqSum`, or `set_option synthInstance.maxSize
     256 in` on the one declaration. Every later seam grows the type.
2. **1.3, the left pass** (amended), with the pieces 1.1b now supplies:
   - the second seek's precondition: local agreement on `[−zoneStart ℓ, 0]` from
     `zr_rightPass_tape.2`, after the return home;
   - the left ruler's delimiters: scratch blank off `[q, q + m)`, from `zr_rightPass_post`;
   - the direction-parametrized `zr_rulerStepContract`/`zr_adjustedWalkContract`/
     `zr_adjustedBackContract`; the displacement `2·2^ℓ + 1` (`zr_left_two_walks`); outer half,
     then inner;
   - the `ℓ = 1` instance (−8) in Lean.
3. **1.4–1.6:**
   - the `ℓ = 0` branch by the leaf (cells `±2`, `±3`);
   - `clearTM_contract` on the ruler `[q, q + m)`, and the return home;
   - assembly by `Contract.ofSegment` in the `HeadBox` of `zoneRowLo`/`zoneRowHi`, with
     `zoneExtendPost_frames`. The tape-0 endpoint combines `zr_rightPass_tape.1` with the left
     pass's mirror statement.
4. **Phase 2 unchanged** (the scan, guarded column moves, the passes and home move, the mirror,
   cleanup).
5. **Duplication (N2, and gate 58's points):**
   - name each top pair's shared text exactly;
   - prove per-stage `time`/`lo`/`hi` lemmas for the sub-composites (as the endpoints already
     are) and combine them, rather than a third whole-composite `simp only` list for the left
     pass;
   - keep constant copies on `zr_halfCopyContract`/`zr_rulerCopyContract`.
6. **The probe (gate 58's carry-forward):**
   - start from the worker's 445 checks plus `two_le_zoneStart`: 446 checks of 435 names, to
     which add continuation 4's own;
   - build it as a standalone import of the landed module, with the expected warnings stated;
   - derive the citation inventory from the elaborated constants (an `#ext_list`-style walk), not
     a regex (F1).
7. **Rule 10 evidence:** require the seal's failing controls (inside fails, outside passes) and an
   argument-by-argument inspection table in the brief (F2).
8. **Regions re-derived from the landed file** (if landed unchanged):
   - (a) the home, 127–1350 (1351 is `/-! ### The rows -/`);
   - (b) the rebalance status paragraph 1391–1395, its `sorry` at 1408;
   - (c) the extension status paragraph 1431–1438, its `sorry` at 1449;
   - the targets at 1396 and 1439;
   - base counts 1,572 lines, 18 public / 73 private.

   Shift them by any maintainer commit.
9. **1.1b remainder: none.** Every 1.1b item is proved. The gate 58 items are now checked: the
   level-one instance, the scratch envelope, the bridge, the re-wrap, and the adapter's four
   instances.

**Decisions for the user:**
- (1) Land checkpoint 1 now as a new partial PR (recommended), or hold it for continuation 4.
- (2) The replay: 2 modules from the first merged-tree snapshot (`lsk2`, or a re-run `lsl`;
  recommended), or the 16-module merged-tree replay from `oleans-l132b`.
- (3) Whether to apply the optional status-paragraph and docstring rewording at landing.
- (4) Continuation 4: dispatch it alone or in the next megafill (it needs a fresh environment),
  asking for 1.2 and 1.3 as separately landable checkpoints. Also whether its brief adds the
  `DecidableEq` note (N1) and the seal-control requirement (F2).
