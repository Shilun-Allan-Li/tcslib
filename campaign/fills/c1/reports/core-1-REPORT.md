# C1-R partial delivery — interpreter core

**Not proved. Not a verified Lean fill.** `Turing.exists_ndInterpreterCore` remains exactly
`by sorry`. No new declaration or proof body lands. The delivery contains the two authorized
imports and a flagged appendix documenting the obstruction. Four unverified helper drafts are
preserved below as continuation notes, not as source to integrate.

Phase reached: **phase 1 preparation only; no complete assembly phase**. The header, capture and
clean-call interfaces were inspected; replay/locality was drafted independently. The startup,
window, loop/verdict, and final ledger are not assembled into one machine.

## Pin and input verification

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Initial branch: `complexity/arora-barak-ch3-4`; initial HEAD:
  `2cce48048b5875fae75d69ef70ee9032b6b5e744`.
- `git merge-base --is-ancestor 83ec6348b325f060cec2a917b45a4eda6e301d84 HEAD`: passed
  before creating the fill branch.
- Branch: `fill/c1-core`, created at the exact base
  `83ec6348b325f060cec2a917b45a4eda6e301d84`.
- Delivery commit: `4061f2821c59982584f5f36fca5dd1090c92ec93`; its sole parent is that base.
- Brief SHA-256: `15a09e9ce83fff66d5d39398c5c62ca731820a91a466e234a5cb674f7c839268`.
- Addendum SHA-256: `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928`.
- Both uploaded hashes matched. The base's brief matches the attachment byte for byte after
  replacing `@ANCESTOR@` with the base; its addendum matches the attachment exactly.
- No rebase, merge, cherry-pick, push, PR, or sub-agent. No `lake build` command was invoked.
  `lake exe cache get` was invoked as prescribed; Lake attempted to prepare its cache executable
  and failed, as recorded below.

## Source scope and declarations

The first source edit added exactly these imports, immediately after the original third import:

```lean
import TCSlib.Complexity.TuringMachine.Build.InputWindow
import TCSlib.Complexity.TuringMachine.UniversalStartup
```

The only later retained change is region (d)'s **Fill appendix (C1-R)**, with the docstring closer
on its own line. Regions (b) and (c) have no retained change. The replay canonizer's statement,
docstring and `sorry`, the bridge, module header, and target statement are unchanged.

`evidence/freeze.log` checks that removing comments and exactly the two imports makes the final
source token-identical to the base. No declaration was added, removed, renamed or restated.
Final size: **163 lines, 3 public declarations, 0 private declarations**; base: 147 lines.
No added line exceeds 100 characters.

New declarations and roles: **none**. The four draft names at the end of this report are not in
the delivered Lean module and were never claimed to have passed Lean.

## Escalations

### E1 — the named counter-value route needs a public equation

Ground rules 4, 5, 6 and 10 apply. At the pin, `Build/CounterLoop.lean` defines:

```lean
def counterValue (w : List Bool) : ℕ :=
  Nat.ofDigits 2 (w.map Bool.toNat)

theorem counterValue_bits (t : ℕ) : counterValue t.bits = t
```

`StepBlock.hostedLoopTM_run` instead takes

```lean
(ht : Nat.ofDigits 2 (w.map Bool.toNat) = t)
```

The requested missing shared lemma is:

```lean
theorem counterValue_eq (w : List Bool) :
    counterValue w = Nat.ofDigits 2 (w.map Bool.toNat)
```

No such equation, or direct published bridge from `counterValue` to that expression, was found
in the pinned import closure. `counterValue` is a `def`, not an `abbrev`. Supplying
`counterValue_bits t` directly at the loop's hypothesis would rely on definitional unfolding,
even if the proof text used `exact` instead of an explicit `unfold`.

The public `foldr_bit_eq_ofDigits` does not mention `counterValue`.
`codeBitsNat_bits` introduces another definition, `codeBitsNat`, for which this route likewise
has no published equation exposing the fold. Re-proving binary reconstruction would duplicate
already proved material. The standard `Nat.digits_two_eq_bits` is in `Digits.Lemmas`, whereas
this source's syntactic import closure contains only `Digits.Defs`; adding an import is forbidden.
These are source-level inventory findings; a negative elaboration probe could not run because
bootstrap failed. This is an API obstruction to the brief's named route, **not a refutation of
the target theorem**. The loop item was stopped without unfolding or building a replacement.

Requested action: publish the equation in the shared module and issue a continuation at a pin
that contains it. This delivery does not consume the in-flight follow-up API PR.

### E2 — dependency preparation and fresh verification blocked

The unmodified pinned Lean emitted `error: failed to locate application`. The addendum's exact
shim was compiled and successfully produced:

```text
Lean (version 4.25.0, x86_64-unknown-linux-gnu,
commit cdd38ac5115bdeec5f609e9126cce00f51ae88b3, Release)
```

The authorized `lake exe cache get` retry failed while preparing `Cache.Hashing`, because
`Cache/IO.olean` had an invalid header (the file was empty when inspected). Bootstrap retries
reported missing Mathlib and Batteries object files. Both the root filesystem and the shared
memory filesystem repeatedly reached capacity; the shared cgroup reached its 8 GiB memory cap.

Only this checkout's temporary storage was moved, and a sparse checkout was used to omit
unneeded files without changing their index contents. Immutable Git objects were reused through
an alternate object store to reduce memory use; the target branch and its commit ancestry were
not changed. Existing dependency caches were tried only at the exact revisions in the pinned
manifest, including mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. No TCSlib olean from
another fill was used. The attempted bootstrap still produced no fresh `Zone.olean`.

A small `True`/`Nat` runtime probe did pass through `scripts/lean_check_tree.sh`, so the shim
worked; the remaining failure is dependency/resource availability. The remaining stalled
bootstrap retry was terminated. A final sweep attempt had a documented 60-second diagnostic
limit and exited 124 on module 1. Owned-source, import and axiom checks each had a 20-second
limit; all returned an actual missing-prerequisite error (exit 1), not a timeout.

The first cache/bootstrap logs were moved while open during disk exhaustion, so their later
output was lost. They are retained with this limitation; complete retry diagnostics are separate.
No successful bootstrap or fresh warning count is claimed.

## Runtime addendum record

Shim source SHA-256:
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
It was extracted verbatim from the verified addendum and hash-checked before compilation.
`evidence/runtime/executable-path.c` is included; the compiled shared object is not.

The process-scoped settings were:

```text
PATH=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux/bin:<original PATH>
LEAN_SYSROOT=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/45e6e7dccd1a/runtime/executable-path.so
TCSLIB_OLEANS=/dev/shm/c1-core-45e6e7dccd1a/oleans
TMPDIR=/dev/shm/c1-core-45e6e7dccd1a/tmp
```

`TCSLIB_OLEANS` was set for check-script invocations. `TMPDIR` was added on retries after disk
exhaustion. The shim was scoped to Lean/Lake and the authorized check scripts; it was not used
for Git, Python, screens or lint. No toolchain patch, permission change or sandbox escalation.

## Ledger and constant — conditional, not discharged

One header pass is bounded by

\[
3|\langle\mathrm{bits}(t),\alpha\rangle|+4
 +5(|\langle\mathrm{bits}(t),\alpha\rangle|+1)
 =16|\mathrm{bits}(t)|+8|\alpha|+25.
\]

Its suffix position is `4|bits t| + 2|α| + 7`. The intervening native rewind costs at most
`4|bits t| + 2|α| + 9`. Thus the two raw passes and that rewind cost at most
`36|bits t| + 18|α| + 59`, before the remaining installation/copy/dispatch costs.
The clean install call's cost depends only on `α`, through the canonizer's time, argument
length and serialization length. These interfaces have not been assembled into the start
configuration required by the target.

For a continuation, suppose the **fully assembled** startup and fixed dispatch costs are at most
`a + b|bits t|`, and the window coefficient is `w`. Write `L` for the replay table's length.
A sufficient per-code choice would be

\[
C=a+b+w+50(L+1)+10.
\]

Using the published bit-length bound and `min(t,|x|) ≤ t`, the full ledger would be

\[
\begin{aligned}
T&\le a+(b+4)|\mathrm{bits}(t)|+w(\min(t,|x|)+1)
       +(50(L+1)+4)t+2\\
 &\le (b+w+50(L+1)+8)t+a+w+2\\
 &\le C(t+1).
\end{aligned}
\]

For a branch already halted at `t' ≤ t`, the escape bound would give

\[
\begin{aligned}
T&\le a+(b+4)|\mathrm{bits}(t)|+w(\min(t,|x|)+1)
       +(50(L+1)+4)t'+2\\
 &\le a+w+2+(b+4)|\mathrm{bits}(t)|+w|x|+(50(L+1)+4)t'\\
 &\le C(t'+|x|+|\mathrm{bits}(t)|+1).
\end{aligned}
\]

The extra `+2` is a harmless relaxation of the escape ledger. Every coefficient and the
constant term are at most the displayed `C`. **No actual `a`, `b`, `w`, or final machine has
been constructed; this is a conditional ledger, not a proof of either target clause.**

## Continuation and open declarations

- `Turing.exists_ndInterpreterCore` — **Proof sketch:** compose two fresh-bank returning
  captures of the prefix extractors, with a native rewind between them. Install the per-code
  replay serialization, retain the deadline counter and install the unary initial state.
  Copy the bounded input window with a separate counter copy; rewind that window. Establish
  the replay start's `Rep` and virtual-input fields through their public equations, then use
  the published hosted loop and its verdict-reading theorem. After E1 is repaired, instantiate
  its counter hypothesis without unfolding. Replay and input locality identify every prefix;
  combine the two loop bounds with the assembled startup/window bounds above. All four
  assembly phases remain open.
- `Turing.exists_replayCanonizer` — out of scope, unchanged. **Proof sketch:** its frozen
  docstring gives canonization, primitive-recursive replay reserialization and composition.
  This delivery neither fills nor changes it.
- `Turing.exists_inputWindowCopyTM` — external cited stub, unchanged. **Proof sketch:** its
  own frozen contract uses the counter loop with a one-step copy body and early input-end exit.

Source-level target axiom walk: the target body is still a direct `sorry`; its admission has
not been removed or relocated. It does not call either cited stub or any draft helper.
**Exact transitive axiom printing was unavailable**: `evidence/axioms.log` records failure to
import the unbuilt owned module. No new private declarations require axiom prints.

Promotion candidates (notes only): the combined two-pass header split, and a bounded
native-input computation with silent capture and first live return. Neither is promoted here.

## Rule 10 and verification

New proof citations outside the owned file: **none**, since no new proof body lands. The
unchanged bridge retains its original uses of `tableBitsK_two`, `CodeNDTM.serialize`,
`codeTable2Bits`, `NDTM.fixChoice`, and `actionBits₂_eq_actionBitsK`. The appendix cites only
names already present at the base. Draft-only references are visible in the preserved code below;
they are not dependencies of the delivered target.

The original 77-check import probe was copied unchanged and attempted through the required
check script. It failed to import the unbuilt `NDCodes.olean`; no successful probe is claimed.
Rule 11's diff grep found none of the six forbidden R3 rows and no foreign private name
(4,992 private names scanned).

The base warning set, recorded before proof work, is:

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Build/NDHost: 1: ndWriterTM_run_block
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

No sorry body changes in the delivered source, so the expected set remains all 35 entries.
A fresh comparison could not be measured because the bootstrap did not complete.

| Check | Result |
|---|---|
| Attachment hashes; repository copies; ancestor; exact base | PASS |
| Statement/region freeze; first edit; added line width | PASS |
| Final source size | 163 lines; 3 public / 0 private |
| Bootstrap order | attempted; dependency failures, then stalled retry stopped |
| Final 80-module sweep | incomplete, exit 124 on module 1 |
| Owned module | exit 1, missing `NDCodes.olean` |
| 77-name import probe | exit 1, missing `NDCodes.olean` |
| Axiom probe | exit 1, missing `NDCodeSimulator.olean` |
| Style lint | `style_lint: 0 FAIL, 63 WARN over 79 files` |
| Rule 11 diff grep | PASS |
| Copy screens | identical; no new pairs |
| Patch and bundle | verified; see evidence logs |

Final sweep tail:

```text
Final sweep attempt; 60-second diagnostic limit after cache failure.
MODULE 1 TCSlib/Complexity/TuringMachine/Build/Zone
FINAL_SWEEP_EXIT=124
```

## Duplication ledger

Both required v3 screens were run sequentially, each under `nice -n 10`, over the seven pinned
population files. They are byte-identical: **171 declarations, 19 pairs, 5,115 characters**.
No new in-file or cross-file pair; no justification is needed. **new copies: none**.
Draft helper bodies were removed before the final screen and are preserved only as unverified
continuation notes in this report.

Before:

```text
declarations screened: 171; copy pairs (target reproduces >= half of source): 19; reproduced text: 5,115 chars
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   CodeSimulator.lean::exists_canonOffsetTM  reproduces  CodeSimulator.lean::exists_canonCountTM: 270/397 = 68%
   CodeSimulator.lean::exists_canonReadySeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   CodeSimulator.lean::exists_canonHeaderCountSeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   CodeSimulator.lean::binaryGuard_escape  reproduces  CodeSimulator.lean::binaryGuard_done: 922/1434 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   CodeSimulator.lean::canonStrictInstall  reproduces  CodeSimulator.lean::exists_canonHeaderSeam: 382/648 = 59%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   CodeSimulator.lean::exists_canonHeaderSeam  reproduces  CodeSimulator.lean::canonStrictInstall: 382/671 = 57%
   CodeSimulator.lean::canonHeader_length  reproduces  CodeSimulator.lean::canonHeaderOK_iff: 82/146 = 56%
   CodeSimulator.lean::scan_grammar_guard  reproduces  CodeSimulator.lean::canonScan_all: 152/278 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
```

After:

```text
declarations screened: 171; copy pairs (target reproduces >= half of source): 19; reproduced text: 5,115 chars
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   CodeSimulator.lean::exists_canonOffsetTM  reproduces  CodeSimulator.lean::exists_canonCountTM: 270/397 = 68%
   CodeSimulator.lean::exists_canonReadySeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   CodeSimulator.lean::exists_canonHeaderCountSeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   CodeSimulator.lean::binaryGuard_escape  reproduces  CodeSimulator.lean::binaryGuard_done: 922/1434 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   CodeSimulator.lean::canonStrictInstall  reproduces  CodeSimulator.lean::exists_canonHeaderSeam: 382/648 = 59%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   CodeSimulator.lean::exists_canonHeaderSeam  reproduces  CodeSimulator.lean::canonStrictInstall: 382/671 = 57%
   CodeSimulator.lean::canonHeader_length  reproduces  CodeSimulator.lean::canonHeaderOK_iff: 82/146 = 56%
   CodeSimulator.lean::scan_grammar_guard  reproduces  CodeSimulator.lean::canonScan_all: 152/278 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
```

## REPORT checklist

- [x] Target outcome/phase, base hash and ancestor check recorded — partial, theorem unproved.
- [x] Exactly the two imports as the first edit; only regions (a) and (d) retained.
- [x] Every new declaration and role recorded — none; flagged appendix included.
- [x] Constant and both ledgers recorded — conditional, missing assembly stated explicitly.
- [x] Promotion candidates and escalations recorded.
- [ ] Rule 10 import probe passed — attempted, blocked by missing prerequisites.
- [x] External citations recorded; Rule 11 diff grep passed.
- [x] Both screens quoted; no new pairs; **new copies: none**.
- [x] File counts and lint line recorded.
- [ ] Final sweep and axiom prints passed — attempted, unavailable as detailed above.

## Patch and bundle

The single patch is against the exact base and applies to that base's full source. A temporary
application reproduced the delivered source byte for byte. The bundle has exactly one
prerequisite, `83ec6348b325f060cec2a917b45a4eda6e301d84`, and one advertised head,
`refs/heads/fill/c1-core` at `4061f2821c59982584f5f36fca5dd1090c92ec93`.
It was verified and unpacked in a separate bare verifier with only a local base ref; source
extraction matched the delivered source. Alternate-ref enumeration was restricted to the base
ref to exclude unrelated stale refs from the reused object stores. No compiled artifacts ship.
`SHA256SUMS` covers every other archive member.

## Preserved helper drafts — not checked, not part of the source patch

Roles: `ic_header_result` computes either header projection's endpoint;
`ic_capture_return` combines first halt with the returning silent embedding;
`ic_replay_window` compares every bounded replay prefix to the original-input branch;
`ic_table_call` specializes the clean call to the admitted replay canonizer.
These drafts may need elaboration repairs. The generic first-halt/capture draft also uses the
published `Cfg.Halted` abbreviation through a theorem hypothesis; a continuation should review
this against the brief's no-unfolding discipline before landing it.

```lean
/-- Either header projection halts at the suffix with its selected component. The common
time is `16 |bits t| + 8 |α| + 25`; in particular it is independent of the suffix.

**Proof sketch.** Apply the published prefix contract to the first or second pair extractor.
Decode the inner pair with its round-trip lemma and expand only its published length formula. -/
private theorem ic_header_result (first : Bool) (α x : List Bool) (t : ℕ) :
    let F := if first then FinTM.pairExtractTM true false else FinTM.pairExtractTM false true
    let M := prefixCanonTM F
    let z := pairEncode (pairEncode (Nat.bits t) α) x
    let d := M.tm.runFrom (M.tm.initCfg z)
      (16 * (Nat.bits t).length + 8 * α.length + 25)
    d.state = none ∧ d.output = (if first then Nat.bits t else α) ∧
      d.inputPos.val = 4 * (Nat.bits t).length + 2 * α.length + 7 := by
  have duration : 3 * (pairEncode (Nat.bits t) α).length + 4 +
      5 * ((pairEncode (Nat.bits t) α).length + 1) =
      16 * (Nat.bits t).length + 8 * α.length + 25 := by
    rw [length_pairEncode]
    omega
  have position : 2 * (pairEncode (Nat.bits t) α).length + 3 =
      4 * (Nat.bits t).length + 2 * α.length + 7 := by
    rw [length_pairEncode]
    omega
  cases first
  · have h := prefixCanon_complete _ _ _ FinTM.pairExtractTM_snd
      (pairEncode (Nat.bits t) α) x
    simpa only [duration, position, pairDecode_pairEncode, Option.map_some,
      Option.getD_some, Bool.false_eq_true, ↓reduceIte] using h
  · have h := prefixCanon_complete _ _ _ FinTM.pairExtractTM_fst
      (pairEncode (Nat.bits t) α) x
    simpa only [duration, position, pairDecode_pairEncode, Option.map_some,
      Option.getD_some, ↓reduceIte] using h

/-- A bounded native-input computation can be silently captured with a first live return.
The completed transport contains the source's final output, even if it halted before the bound.

**Proof sketch.** Choose the first halt using the public first-halt lemma. The returning
embedding reaches its live anchor there, with exactly the configuration at the supplied bound. -/
private theorem ic_capture_return {k : ℕ} (M : FinTM Bool) (x : List Bool)
    (ι : Fin M.k ↪ Fin k) (cap : Fin k) (hcap : cap ∉ Set.range ι)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (out : List Bool)
    (T : ℕ) (halt : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    ∃ u ≤ T,
      (embedSilentRetTM ι cap M.tm).runFrom
          ((embedSilentCfg ι cap tapes heads [] out (M.tm.initCfg x)).mapState Sum.inl) u =
        { embedSilentCfg ι cap tapes heads [] out (M.tm.runFrom (M.tm.initCfg x) T) with
          state := some (Sum.inr ()) } ∧
      ∀ v < u,
        ((embedSilentRetTM ι cap M.tm).runFrom
          ((embedSilentCfg ι cap tapes heads [] out (M.tm.initCfg x)).mapState Sum.inl)
          v).state ≠ some (Sum.inr ()) := by
  obtain ⟨u, hu, before, same⟩ := M.tm.exists_first_halt (M.tm.initCfg x) halt
  have live : (M.tm.initCfg x).state ≠ none := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  obtain ⟨_, result, cut⟩ := embedSilentRetTM_run ι cap hcap M.tm tapes heads [] out
    (M.tm.initCfg x) u live before (by rw [same]; exact halt)
  exact ⟨u, hu, by simpa only [same] using result, cut⟩

/-- Replaying any prefix of the stream on the bounded window gives the original branch's
control and output. The stream may be longer than the deadline.

**Proof sketch.** The replay theorem removes the extra choice tape. Input locality then
identifies the run on `x.take t` with the run on `x`, since the prefix has at most `t` bits. -/
private theorem ic_replay_window {k : ℕ} {S : Type} (N : NDTM k Bool S)
    (x s : List Bool) (t r : ℕ) (hs : t ≤ s.length) (hr : r ≤ t) :
    let d := N.replayTM.runFrom
      (NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0) r
    let e := N.runWith (s.take r) (N.initCfg x)
    d.state = e.state ∧ d.output = e.output := by
  obtain ⟨p, _, _, replay⟩ := N.replayTM_runFrom (N.initCfg (x.take t)) s r
    (hr.trans hs)
  have locality := N.runWith_initCfg_take x t (s.take r) (by
    rw [List.length_take]
    omega)
  dsimp only
  rw [replay, NDTM.withChoiceTape_state, NDTM.withChoiceTape_output]
  exact ⟨locality.1, locality.2.2.2.2⟩

/-- The replay canonizer can be called through the clean installation interface, with a
cost depending on the code alone. The installed word is the entire replay serialization.

**Proof sketch.** Take the canonizer from its gated statement and feed its computation contract
to the public install-call theorem. Both the argument and its result depend only on the code. -/
private theorem ic_table_call (c : EffectiveNDMachineCode) :
    ∃ (M : FinTM Bool) (entry done : M.State) (cost : List Bool → ℕ), 0 < M.k ∧
      ∀ x α : List Bool, ∃ T ≤ cost α, 0 < T ∧
        (∀ u, 0 < u → u < T →
          (M.tm.runFrom
            (Cfg.ofWords (input := x) entry (stateWord M.k α)) u).state ≠ some done) ∧
        M.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord M.k α)) T =
          Cfg.ofWords done (stateWord M.k (serializeK (c.decode α).tm.replayTM)) := by
  obtain ⟨F, τ, computes⟩ := exists_replayCanonizer c
  obtain ⟨M, entry, done, a, positive, installs⟩ :=
    FinTM.exists_installCallTM F _ τ computes
  exact ⟨M, entry, done,
    fun α => a * (τ α.length + α.length + (serializeK (c.decode α).tm.replayTM).length + 1),
    positive, installs⟩
```

Glossary for the conditional ledger: `a` is the per-code fixed startup cost; `b` is its
counter-width coefficient; `w` is the window copier's coefficient; `L` is replay-table length.
All other mathematical notation is from the brief.
