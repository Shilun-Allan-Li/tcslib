# Ch3–4 fill campaign — B5a, H1: the uniform simulator (`Turing.MachineFormat.exists_uniformSimulator`, `TuringMachine/CodeSimulator.lean`)

<!-- DRAFT (drafting agent), 2026-10-24, for megafill C.
**Rewritten against the interpreter startup (maintainer, 2026-10-27).** A+ is PR #169
(`Turing.exists_interpreterStartup`, gate 79 closed); B5a cites it at `p = F.k`. The junction
into the hosted verdict is proved in the owned file's overlay
(`campaign/fills/b5a/drafts/b5a-fill-unisim/preship-junction/`: `b5a_bank`, `b5a_junction`,
`b5a_tail`, `b5a_start`, `b5a_run`). The route's steps 1–4 are therefore one citation of the
startup and the probe's lemmas; the imports drop to two (`Nondeterministic` and the startup's
module, whose closure has the other four). **Issue after #169 merges**, with the pre-ship
re-run there on the two-import overlay: the overlay and its lines, the import and clash
probes, the route, start, verdict and junction probes with their controls, the lists, the
screen base and the lint base. The paragraphs below this one are the earlier history.
**Deferred from megafill C (user, 2026-10-25):** megafill C was issued with U2 only; this item goes
in a later queue once the A+ harvest lands. Drafting base: the campaign tip
`77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` (TCSlib as after #155; #156 open). Pre-ship measured
there, against a fresh bootstrap of the order list:
`campaign/fills/b5a/drafts/b5a-fill-unisim/preship-77f1eb4f/`.
**Q-B1, ruled (user, 2026-10-24): option A**, the startup kit published first (PR #162,
`Build/InterpreterStartup`); this text keeps option A, and option B's paragraphs are removed.
Issue-time items: @ANCESTOR@, ⟨BASE⟩, ⟨IN-FLIGHT⟩, the megafill banner, the semantic-duplication
requirement (gates 69 and 72; megafill D's drafting brief §5), and re-running the pre-ship at the
issue commit.
**Issue base (review, 2026-10-24):** after #156 (merged; its round-2 head `0e5f210b` edits this
file's `canonEmitVerdict`, 4593–4603), the follow-up phase-host API PR #159 (merged; it edits
`canonEmitVerdict` again) and the startup kit's PR #162. Regenerate the overlay (six imports, the
kit's module the sixth) and every line number, count, blob and screen figure there; the numbers
below are the drafting base's, measured with the first five imports.
**Pre-ship re-run at the issue base (maintainer, 2026-10-25):** the campaign tip `a524c36f`, Lean
equal to #162's merge `5a258cc2` (the snapshot `oleans-lkit2`), with the six imports:
`campaign/fills/b5a/drafts/b5a-fill-unisim/preship-a524c36f/`. The line numbers, counts and blob
below are that base's; ⟨BASE⟩ and ⟨IN-FLIGHT⟩ are filled at issue.
**Rulings (user, 2026-10-25):** D-3 = **A+**: the startup assembly that this target shares with the
interpreter core (`exists_ndInterpreterCore`) is harvested into a published contract before B5a
issues, and the brief's route and hazards are rewritten against it then; **B5a is not issuable
until that harvest PR lands with its gate** (and the pre-ship is re-run on it). Each of B5a's
screens runs with no Lean process beside it (its peak memory is 7.8 GB). Q-M2 (the cover):
sequential. -->

> **⟨Megafill …, item N⟩** (cover brief ⟨…⟩; addendum v2.5, Part 3). The preflight, the toolchain,
> the clone and the cache are done once for the whole queue. For this item: create its branch from
> the shared base (below), make your first edit, **re-bootstrap your order list**, then follow this
> brief. **Budget:** ⟨the cover's⟩ from your branch's creation. Deliver a
> checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement**: `Turing.MachineFormat.exists_uniformSimulator`, B5a's
    statement (wave-1 statement gate, `campaign/gates/wave1-statements/`, round 2; its note 34:
    "preserve the uniform quantifier order; per-code constants would not suffice for EXPCOM");
  - **the canonizer, proved** (PR #152, gate 67): `Turing.MachineFormat.exists_polyCanonizer`, in
    your file, with no admission. Your target is the module's last admitted stub, behind targets
    3–8 (`Turing.exists_uniformMachineCode2`, `Turing.exists_uniformMachineCode`,
    `Complexity.EXP_subset_POracle_EXPCOM`, `Complexity.POracle_EXPCOM_eq_EXP`,
    `Complexity.NPOracle_EXPCOM_eq_EXP`, `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`) and
    `Complexity.baker_gill_solovay`;
  - **H1's hosted clock and verdict, proved** in your file: the generic step block
    (`Build/StepBlock`, H2), its hosted counter loop `Turing.StepBlock.hostedLoopTM_run`
    (`Build/StepBlockLoop`), and your file's private verdict `h1HostedVerdictTM`,
    `h1HostedVerdict_effect`, `h1HostedVerdict_accepts`, from the prepared round seam;
  - **the interpreter startup, published** (PR #169, gate 79):
    `Turing.exists_interpreterStartup` (`Build/InterpreterStartup`). From the blank start on
    `⟨⟨bits t, α⟩, x⟩`, a uniform machine first reaches its `done` state with `bits t` on a
    counter, the window `x.take t` on a buffer, an installed table and its initial-state
    summary on two more tapes, and `p` passive tapes as they started. Every role and passive
    head is at `0`, the input head at `1`, and the output is empty. Its time is the
    installer's cost plus `A · (|α| + |serialization| + 1) + B · (|bits t| + min t |x| + 1)`.
    It composes the header passes, the counter copy, the window, the install call and the seam
    layout, with their rewinds; you cite it, never its phases. The design note
    `campaign/items/b5a/A-plus-startup-design.md` ("As built") records its interface and the
    reservation `p = F.k`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.5**: Part 1, the resources and the cache for the Mathlib roots only, with the cache
    store logged first; **Part 3, the megafill**, under which this session runs), and the
    copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/b5a/inputs/b5a-fill-unisim/`): the overlay
    `CodeSimulatorOverlay.lean.txt` (your file with the two imports of region (a)), the import
    probe, the route, start, verdict and junction probes with their seal controls, and the
    screen population; the
    order list `campaign/fills/b5a/orders/b5a-fill-unisim.txt`, the base sorry set, the screen
    base and the pre-ship log (`campaign/fills/b5a/logs/b5a-fill-unisim-*`).
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of
  `campaign/standards/fill-environment-addendum.md` and its Part 3): the preflight, the
  toolchain, the clone and the cache for the whole queue's Mathlib roots. If Lean cannot start,
  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b5a-unisim @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/TuringMachine/CodeSimulator.lean
  # must print 733a9a463e6bac937ef16ff95a8cb4d287bda725
  # (the base's blob, from git rev-parse)
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-unisim.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - **the session's shared environment logs** (`evidence/logs/` at the clone's root: preflight,
    cache store, roots, cache fetch, manifest check), this item's bootstrap and final sweep logs
    with **each module's time and maximum memory**, and the axiom log;
  - the seal test's source, its controls and both outputs; both screen outputs; and
    `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write `fill-b5a-unisim-cp<N>.zip`
  with the same contents as of that commit (the final sweep may be your module's check only), so
  that a lost workspace loses at most one checkpoint. Deliver the latest if the session ends
  early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip ⟨BASE⟩** (after #169). Lines in this brief are
  those of your base's tree, where `CodeSimulator.lean` is ⟨8,666⟩ lines (⟨12⟩ public, ⟨185⟩
  private): #152's landing with #156's and #159's edits to `canonEmitVerdict`.
- **Your first edit makes your file equal to the overlay** (`CodeSimulatorOverlay.lean.txt`): the
  two imports of region (a) after line 15. **Line numbers below are the base's, and the overlay's
  are 2 more** (the stub at ⟨8654⟩, overlay ⟨8656⟩). Every probe and measurement below was run on
  the overlay or at the base, as marked.
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩. Cite nothing they add.

## Parallel batches this round

None in `CodeSimulator.lean`. ⟨The queue's other items, if any, on their own branches.⟩

## What this is

**B5a's H1: the uniform bounded-acceptance simulator.** One target, frozen:
**`Turing.MachineFormat.exists_uniformSimulator`** (line 8654): for each machine format `F`, one
finite binary machine `S` and one degree `d` such that on `⟨⟨bits t, α⟩, x⟩` it answers `[true]`
if the machine `α` denotes halts on `x` with output exactly `[true]` within `t` steps, and
`[false]` otherwise, within `d · (|α| + |x| + t + 1)^d` steps. **`S` and `d` are uniform in the
code**: no per-code constant (note 34).

**The statement and the docstring's statement and sketch, frozen verbatim** (lines 8552–8580 and
8654–8662; the fill appendices 8582–8651 and the `-/` alone on 8653 are frozen byte for byte too):

```lean
/-- **The uniform bounded-acceptance simulator** (spec, fill pending — batch
B5a): one finite binary machine and one degree such that, on
`⟨⟨bits t, α⟩, x⟩`, the machine answers `[true]` if the machine `α` denotes
halts on `x` with output exactly `[true]` within `t` steps, and `[false]`
otherwise, within `d · (|α| + |x| + t + 1)^d` steps. [AB09, §1.4.1, Theorem 1.9,
time-bounded form; Example 3.6(3)'s uniformity]

**Proof sketch.** Parse the nested input onto tapes: the deadline word
`bits t` on a counter tape, `α` on a table tape, `x` on a buffer tape. Canonize
`α` in place by `Turing.MachineFormat.exists_polyCanonizer` through
`Turing.FinTM.exists_installCallTM`; by `F.serialize_eq` the table is
`serializeK (F.machine (F.decode α))`, of length at most
`max |α| |F.serialize F.fallback|` (`Turing.CodeFormat.serialize_decode_length_le`).
The body is **one step block**: for the current simulated state (unary on a
state tape), input read and `k` work reads, seek the record at index
`q · 3^(k+1) + rank(inp, w)`, read it by the `Turing.codeReadActionK` grammar
(`Turing.codeReadActionK_append`), apply it to `k` mirrored work tapes and the
simulated input head, and update a finite output summary (empty, exactly
`[true]`, other) instead of emitting. Its cost is at most `B · (|table| + 1)`,
independent of `t`, `x` and the tape contents. The block reads the simulated
input through its own input head and is hosted on the buffer by
`Turing.vhostEmitTM` (`Turing.vhostEmitTM_runFrom`); the clock is
`Turing.counterLoopTM` over `bits t` (`Turing.counterLoopTM_run_done`,
`Turing.counterLoopTM_run_escape`), a simulated halt being the live exit. At
`done` the simulated machine is live after `t` steps, so the answer is `false`;
at `escape` it has halted within `t`, and the answer is the summary's
`[true]` test. The ledger: polynomial startup, `t` rounds of at most
`B · (|table| + 1)` (`Turing.counterLoop_time_le`), and the verdict, all at most
`d · (|α| + |x| + t + 1)^d`.
…
-/
theorem exists_uniformSimulator :
    ∃ (S : FinTM Bool) (d : ℕ), ∀ (α x : List Bool) (t : ℕ),
      ((F.toFinTM (F.decode α)).ComputesInTime x [true] t →
        S.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (d * (α.length + x.length + t + 1) ^ d)) ∧
      (¬(F.toFinTM (F.decode α)).ComputesInTime x [true] t →
        S.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (d * (α.length + x.length + t + 1) ^ d)) := by
  sorry
```

**Where it stands** (the module's status text, lines 56–63, and the fill appendices): the step
block, its hosted counter loop and the one-bit verdict from the prepared round seam are proved
(`h1HostedVerdict_accepts`: from a represented start `d` of the decoded machine on a buffered
input, with `bits t` on the counter, the hosted verdict halts within
`t · (50 (|table| + 1)) + 4t + 2|bits t| + 3` steps, emitting one bit that is `true` exactly when
the decoded machine accepts that input within `t`). **Open:** the nested-input startup, the
canonizer's installation, the assembly and the joint polynomial ledger.

**Proved modulo, exactly:** none. Every row the route composes is admission-free (the import
probe's eight axiom prints). **A complete delivery has no `sorryAx` in your target**, and then
targets 3–8 and `Complexity.baker_gill_solovay` have none from your file.

**Read first:**
- the target's docstring, whose sketch is binding where this brief does not refine it. Three
  refinements:
  - the header, the counter copy, the window, the installation and the layout are **one
    citation of the interpreter startup** at `p = F.k`;
  - the buffer holds the **window `x.take t`**, not all of `x`; bounded acceptance on the window
    is bounded acceptance on `x` by input locality;
  - the clock and verdict are the landed `h1HostedVerdict_accepts`, not a second loop;
- `Turing.exists_interpreterStartup`'s statement and docstring, and the design note's "As built";
- `h1HostedVerdict_accepts`: its entry configuration is
  `vhostCfg (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape t.bits) 0) true p []`, with
  `d` representing the decoded machine's initial configuration on the window (`StepBlock.Rep`);
- **the junction probe** (`B5aJunctionProbe.append.lean.txt`): the tape map, the junction, the
  start and the run, proved in your file's overlay. Its proofs, and the other pre-ship probes',
  may be copied into your home as `us_` privates.

**Pre-ship check** (the maintainer, at your base; its log is
`campaign/fills/b5a/logs/b5a-fill-unisim-preship.log`):
- **The overlay** elaborates with exactly one sorry warning, the target's (overlay line ⟨8656⟩).
  The two imports create no cycle (neither closure contains your file). Together with every
  module downstream of your file they import without a clash (`ImportClashProbe.lean.txt`:
  ⟨0⟩ diagnostics).
- **The import probe** (`B5aUSImportProbe.lean.txt`, a standalone import of your module and the
  two, **⟨N⟩ checks of ⟨N⟩ names**, with axiom prints): 0 errors, 0 warnings, every print within
  the standard three. **Re-run it after your delivery**, extended by every further name you cite.
- **The route probe** (`B5aUSRouteProbe.lean.txt`, sealed): `b5a_install` (the polynomial
  canonizer through the install call: one module `C`, uniform in the code, with a first positive
  return at `t ≤ a · ((|α| + 1)^d + |α| + max |α| |F.serialize F.fallback| + 1)` and
  `serializeK (F.machine (F.decode α))` installed), `b5a_locality` and `b5a_accepts_take` (input
  locality), `b5a_verdict` (a halt with output `[answer]` gives both clauses) and
  `b5a_table_le` (`|tableBitsK| ≤ max |α| |F.serialize F.fallback|`): ⟨0⟩ diagnostics.
- **The junction probe** (`B5aJunctionProbe.append.lean.txt`, appended to the overlay, after the
  verdict probe's block `b5a_window_verdict`; sealed over 20 definitions): only the target's
  sorry warning; every lemma within the standard three:
  - `b5a_bank`: from the startup's role and passive indices and its ten separation facts, the
    hosted verdict's tape map `g : Fin (1 + (F.k + 2 + 1)) ↪ Fin K`: the window at `jwin`,
    mirrored tape `i` at `ιP i`, then the table, the summary and the counter;
  - `b5a_junction`: the startup's threshold, relabelled to `(.dec .run, true)`, is
    `embedEmitCfg g … [] (vhostCfg (counterLoopCfg (some (.dec .run)) d (bufferTape t.bits) 0)
    true c.inputPos [])`, for a `d` at the live exit that represents the initial configuration
    on the window;
  - `b5a_tail`: the seam `seamCompTM U done (embedEmitTM g (h1HostedVerdictTM F.k))
    (.dec .run, true)` halts at `T₁ + 1 + T₂` with output `[answer]`, `T₂` within the verdict's
    bound and `answer` deciding acceptance on `x`;
  - `b5a_start`, `b5a_run`: the binary machine `S`, the seam restarted at `Sum.inl entry`, halts
    from `S.tm.initCfg ⟨⟨bits t, α⟩, x⟩` with output `[answer]`, which is `b5a_verdict`'s
    hypothesis.
- **The seal controls** (`B5aUSSealControl.lean.txt` and `B5aJunctionSealControl.lean.txt`, one
  `rfl` goal per sealed definition): every one closes unsealed and fails sealed, each at its own
  goal.

## Owned regions and targets (modify these and nothing else)

| # | File:line (base) | Target |
|---|---|---|
| 1 | `CodeSimulator.lean:8654` | `Turing.MachineFormat.exists_uniformSimulator` (frozen statement) |

Your regions:
- **(a) the imports**, as your first edit: exactly these two, after line 15 (the overlay):

  ```lean
  import TCSlib.Complexity.TuringMachine.Nondeterministic
  import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup
  ```

  No other import.
- **(b) the home**, the blank line 8549, inside `section StepBlockClients` (where `open StepBlock`
  is in force, line 8422), between `h1HostedVerdict_accepts`'s last line (8548) and
  `end StepBlockClients` (8550), inside `namespace MachineFormat` with `F` the section variable:
  your `private` declarations. `private` only, and no `section`, `open` or `variable` that leaks
  past one (`open … in` on one declaration is fine).
- **(c) the body**, the `sorry` on line 8662.
- **(d) for a partial only, a paragraph headed `**Implementation status.**`** at the end of the
  target's docstring, before its `-/` (alone on 8653). It is public-facing library text: what
  is proved and what is open, in mathematical terms, with no campaign labels (brief, gate, finding,
  continuation or escalation names), no dates and no session narrative. The same holds for the
  docstrings of your new declarations; provenance goes in `REPORT.md`. **Every new declaration has a
  docstring, and every proof over 20 lines a literal `**Proof sketch.**` paragraph** (`policy.md`
  §3; the canonizer's and the seam layout's landings each needed a follow-up PR for missing ones).

**Not yours:** every other line, including the target's docstring before (d) (its fill
appendices too: the maintainer rewrites the status text, the module's lines 56–63, the target's
appendices, and `Codes2Tape`/`EXPCOM`'s, at integration; report any text that reads wrong),
every existing declaration (the canonizer and H1's privates included: cite them, adjust none),
and every other file.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The startup:** cite `Turing.exists_interpreterStartup` at `p = F.k`, with the installer of
  `us_install`. **Never write a header pass, counter copy, window copy, install phase, layout or
  their rewinds**, and never re-walk the startup's eleven phases.
- **The loop and the verdict:** cite `h1HostedVerdict_accepts` (your file), through
  `us_window_verdict`. **Never write a second step block, counter loop, virtual-input host or
  verdict.**
- **Compose by the public combinators:** the seam `seamCompTM` (`seamCompTM_runFrom_right`), the
  forwarding embedding `embedEmitTM` (`embedEmitTM_runFrom`, `embedEmitCfg_eq`), and the restart
  `{ W with q₀ := q }` (`MultiTapeTM.initCfg_with_q₀`, `MultiTapeTM.runFrom_with_q₀`).
- **Leaves you may write:** none is expected. A further leaf is an escalation.
- **Promotion candidates** (notes only, in `REPORT.md`): the deterministic input-locality lemma
  (`us_locality`; a candidate beside `MultiTapeTM.toNDTM_runWith`), and the tape-map lemma
  `us_bank` (generic in `k`).

### The route (binding where it names a row)

Write `M := F.machine (F.decode α)`, `u := pairEncode (bits t) α`, `z := pairEncode u x`. The
machine `S` and the degree `d` are chosen before `α`, `x`, `t`.

0. **The first edit**: the two imports (region (a)).
1. **The installer and the startup** (checkpoint 1):
   - `us_install` (the route probe's `b5a_install`; copy it): one module `C` with `entry`,
     `exit`, constants `a`, `d₀` and `0 < C.k`, uniform in the code;
   - **the startup at `p = F.k`**: `exists_interpreterStartup (fun α => F.numStates (F.decode α))
     (fun α => F.machine (F.decode α)) C entry exit cost hk (fun x α => by rw [← serializeK_eq];
     exact inst x α) F.k`, as gate 79's consumer probe does (`b5aP_startup`,
     `campaign/gates/79-interpreter-startup-api/evidence/round2/B5aConsumerProbe2.lean.txt`). It
     gives `K`, `Q`, `U`, `entry`, `done`, `ιP`, the four roles, `A`, `B` and the ten
     separation facts;
   - `us_bank` (the junction probe's `b5a_bank`) on the roles: the tape map `g` and its five
     value equations.
2. **The machine** (checkpoint 2): `S : FinTM Bool` with `k := K`, the state type
   `Q ⊕ (CounterLoopState (Σ key, StepBlock.Ph F.k key) × Bool)`, and
   `tm := { seamCompTM U done (embedEmitTM g (h1HostedVerdictTM F.k)) (.dec .run, true) with
   q₀ := Sum.inl entry }` (structure-instance syntax: `FinTM`'s instance fields are found, not
   passed). Then `d`, from `a`, `d₀`, `A`, `B` and `F`'s constants (step 4).
3. **The run** (checkpoint 3): the startup at `α`, `x`, `t` from the all-blank start
   (`tapes₀ := fun _ _ => none`; its hypothesis holds by `rfl`) gives `T₁`, the first arrival at
   `done` and the threshold fields (destructure the conclusion's `let` by `dsimp only`). Then
   `us_run` (the junction probe's `b5a_run`; copy it with `us_junction`, `us_tail`, `us_start`
   and `us_window_verdict`): `S` halts from `S.tm.initCfg z` at `T₁ + 1 + T₂` with output
   `[answer]`, `answer = true` exactly when `M` accepts `x` within `t`.
4. **The ledger** (checkpoint 4), uniform: with `N = |α| + |x| + t + 1` and
   `L₀ = |F.serialize F.fallback|` (a constant of `F`):
   - `T₁ ≤ a · ((|α| + 1)^d₀ + |α| + max |α| L₀ + 1) + A · (|α| + |serializeK M| + 1) +
     B · (|bits t| + min t |x| + 1)`, with `|serializeK M| ≤ max |α| L₀` (`F.serialize_eq`,
     `serialize_decode_length_le`), `|bits t| ≤ t` (`length_bits_le_self`) and
     `min t |x| ≤ |x|`;
   - `T₂ ≤ t · 50 (|tableBitsK M.tr| + 1) + 4t + 2 |bits t| + 3`, with
     `|tableBitsK M.tr| ≤ max |α| L₀` (`b5a_table_le`): `O(N^2)`;
   - so `T₁ + 1 + T₂ ≤ c · N^e` with `c`, `e` depending on `F` only. Take `d ≥ c` and `d ≥ e`,
     and close with `ComputesInTime.mono`.
5. **The target** (checkpoint 5): `us_verdict` (the route probe's `b5a_verdict`) at
   `P := (F.toFinTM (F.decode α)).ComputesInTime x [true] t` turns the halt with output
   `[answer]` into both clauses at the bound.
6. **Edge cases that must stay true of your proof:**
   - `t = 0`: `bits 0 = []`, the window and the counter empty; the loop runs no round, and `S`
     answers `[false]`, since an initial configuration is live (`summaryClock_zero`);
   - `|x| < t`: the window is all of `x`;
   - a code `α` whose decoding is `F`'s fallback (which need not reject): `F.decode` is total, and
     the simulation runs the fallback (note 34);
   - `α = []`, `x = []`: the startup's bound holds at every length, `0` included.

**Do not run the canonizer through `prefixCanonTM`'s time bound**; it runs inside the install
call, whose bound is polynomial (`b5a_install`). **Do not copy** the startup's phases,
`NDCodeSimulator`'s core junction, `UniversalK`'s startup or `Diagonalization/NTimeHierarchy`'s
`un_` setup: cite the startup and copy the junction probe.

## Gate guidance (binding)

- **The wave-1 statement gate**, note 34: the quantifier order is binding (`S` and `d` before
  `α`, `x`, `t`); per-code constants would not suffice for `EXPCOM`. The deadline is inclusive: a
  halt at step `t` is accepted at deadline `t` (`summaryClock_accepts`).
- **The H1 harvest gate** (`campaign/gates/20-h1-harvest-statements/`): cite the hosted loop and
  its reading lemma as stated.
- **The startup's API gate** (gate 79, `campaign/gates/79-interpreter-startup-api/`, rounds 1
  and 2): cite the startup as stated, at `p = F.k`. Its endpoint states the role and passive
  tapes only; the startup's other tapes are scratch, which the embedding leaves aside.

## Cited infrastructure (public and proved at the issue commit; all in `B5aUSImportProbe.lean.txt`)

The probe's ⟨N⟩ names: the target, the format and the canonizer; the install call; the
interpreter startup and `serializeK_eq`; input locality; the loop's entry and the hosted loop with
`vhostCfg`'s and `counterLoopCfg`'s equations; the seam, the forwarding embedding and the
restart; the model's run algebra and field equations. In your file you also cite the canonizer,
`h1HostedVerdictTM`, `h1HostedVerdict_effect`, `h1HostedVerdict_accepts` and `summaryClock_*`.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `TuringMachine/CodeSimulator.lean`.
   List every new declaration with its role.
2. **Statement freeze** over every landed declaration and the target: no renames,
   re-signatures, restatements or attribution edits.
3. **No new public declaration.** No status text outside (d).
4. **Escalation, item by item:** on anything unprovable as stated, including a cited row that
   does not compose as the route says, stop **on that item only**, record the obstruction
   mathematically, and continue with every item that does not depend on it.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the two of region (a). A Mathlib import only if a needed lemma requires
   it; flag it.
7. **One proof per shared argument.** Never re-walk a landed contract (the canonizer's, H1's, the
   startup's, the core's). Never write a second host, loop, seam, embedding, input rewind,
   prefix parser, layout machine or startup phase.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 8,666 lines; 12 public, 185 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch"), and the target's axiom walk. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and **no definitional closure either**: a
      `rfl`, `exact`, `show`, `decide`, `simp` or `simpa` step that closes only because another
      file's definition reduces counts as unfolding. Read `vhostCfg` and `counterLoopCfg` only
      through their field equations and `counter_cfg_eq`; `embedEmitCfg` through its field equations
      and `embedEmitCfg_eq`; `Cfg.init` and `Cfg.mapState` through theirs; `Cfg.ofWords` and
      `stateWord` through theirs; `serializeK` through `serializeK_eq`; `MultiTapeTM.toNDTM` through
      `toNDTM_runWith` and `toNDTM_initCfg`; `StepBlock.Rep` through `StepBlock.Rep_iff`.
    - **Scope (user, 2026-10-23):** this binds TCSlib's own definitions. Core and Mathlib
      definitions may reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`,
      `rw` or `unfold`; use their equation lemmas (`Bool.toNat_true`, not `simp [Bool.toNat]`;
      `List.nil_append`, not `simp [List.append]`).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their lemmas. Unfold `step` and `Action.apply` only for a
      leaf defined in your own file. `phaseHostTM`'s table is read through `phaseHostTM_run`.
    - Your own file's definitions may be unfolded (`MachineFormat.toFinTM`, H1's privates, your
      `us_` declarations).
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check by both methods** (neither alone is complete):
      - a **seal test**: a scratch copy of your module with `attribute [local irreducible]` on every
        other-file TCSlib definition your new proofs mention (start from the union of the pre-ship
        probes' seals and extend by every one you reach), and `attribute [-simp]` on the `@[simp]`
        definitions among them (`MultiTapeTM.initCfg`, `NDTM.initCfg`, `Cfg.init`, `Action.apply` if
        reached), which must still elaborate, **with controls**: for each sealed definition, a goal
        that closes by `rfl` with nothing sealed and fails under the seal;
      - an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
        argument in your diff, each other-file name classified (a theorem, or a definition: a
        finding).
      - **Ship the raw outputs** of the seal and its controls, with their commands and exit
        statuses. **A seal not run, or a seal without controls that fail sealed and close
        unsealed, is a checklist failure** (megafill A's interpreter core ran none, and six steps
        closed only by unfolding).
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Keep `canonPreserveInstall` byte-identical. Cite none of the six R3
    rows anew (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`,
    `incrementTM_run_succ`, `incrementTM_run_overflow`); use their framed `_ofCfg` forms. Cite no
    private declaration of another file. Keep your new privates under the `us_` prefix (unused in
    the tree at the drafting base).

### Checkpoints (for a partial; ground rule 9)

The route's checkpoints 1–5. Each may land alone. **Add no new admission:** a component you state
for yourself goes in only once proved. The freeze check for a partial is the **axiom walk**:
`sorryAx` reaches the headline only through its own body.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). Run the before
screen after your first edit: it must equal the screen base (the overlay changes only imports).
- **The population** is 57 files
  (`campaign/fills/b5a/inputs/b5a-fill-unisim/screen-population.txt`): continuation 7's 45, the
  route's new imports (`Build/InputRewind`, `Build/Rewind`, `Build/InputWindow`,
  `Build/SeamLayout`, `BufferWords`, `Nondeterministic`), the two model files whose lemmas the
  route reads (`Configuration`, `StateRenaming`), the kit's module, and the remaining
  hazards: `Diagonalization/NTimeHierarchy` (UN's setup), `UniversalK` (U2-S's startup) and
  `ClassNP/ExhaustiveReplay` (IR-1's remaining input rewind). It contains `Simulation` and
  `Build/InputRewind` (the megafill A lesson for any item near an input rewind).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/b5a/logs/b5a-fill-unisim-screen-base.txt`: **2,800
  declarations, 3,026 pairs, 977,536 characters** (MEASURED at your base, on the 57 files; 53
  minutes under `nice -n 10`, **peak memory 7.8 GB**). 99 pairs have a declaration of your file on
  one side: 58 within it (four at 90% or more, all CC7-1's: the cut-leg pair and two leg-template
  pairs), 41 across files (one at 90% or more, `canonOffset_spec` of `Encoding`'s
  `length_bits_le_self`, 65 characters).
- **The screen is long:** run the before run right after your first edit, before the bootstrap, and
  the after run as soon as the owned file is final. **Run each with no Lean process beside it** (its
  peak memory at your base was 7.8 GB), and never beside another screen. Run each on a frozen copy
  of its commit (`git worktree add <dir> HEAD`, the screen's root `<dir>`), so that later edits
  cannot race its reads. Expect the after run to be longer than the before run: your target's body,
  `sorry` at the base and so not screened, becomes one of the largest screened declarations.

```sh
P=campaign/fills/b5a/inputs/b5a-fill-unisim
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side.
- **Recorded, add nothing to them:** CC7-1 (the canonizer's cut-leg, leg-template and per-record
  families), the earlier canonizer in-file pairs, and the uniform-code mirror pair.
- **Known hazards** (a proof reproducing one at 90% or more must be factored if both sides are
  yours; if the other side is another file's, stop on that item and escalate):
  - **the startup's proof** (`Build/InterpreterStartup`) and **the core's junction**
    (`NDCodeSimulator`'s `exists_ndInterpreterCore`, after its call of the startup: the
    tape map, the threshold-to-loop identity and the seam): the same shape as the junction
    probe. Cite the startup, copy the probe; never re-walk either;
  - UN's setup (`un_step'`, `un_canon_halt`, `un_setup`) and U2-S's startup
    (`ss_capturedPrefix_run`, `ss_capture_run`, `ss_serialized_layout`), the other header passes;
  - the start identity: `UniversalK`'s `ss_captureInitial` and `ExhaustiveReplay`'s `xr_E_initCfg`
    (the `initCfg_with_q₀` idiom);
  - the input rewinds of IR-1 (`xr_inRewindTM`, `ss_inputRewind`): cite `Turing.inputRewindTM`;
  - the first-halt captures (`Build/CertShell`'s `certCore_run`); the R1 reconstruction family
    (cite `embedEmitCfg_eq`); the field-equation idioms of `Cfg.mapState_mapState` and
    `SeamLayout`'s `sl_rewrap` (accepted idiom pairs: say so if yours is another).
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for the queue's Mathlib roots only** (addendum v2.5,
  fetched once at the session's start; your order list's modules import ⟨41⟩ roots directly, at the
  overlay as at the base); **never `lake build`**, and never the unfiltered `lake exe cache get`.
  Use `scripts/lean_check_tree.sh` for every check, one Lean process at a time.
- **Re-bootstrap** (addendum Part 3, item 3.2) from `campaign/fills/b5a/orders/b5a-fill-unisim.txt`
  (**⟨120⟩ modules**, computed on the overlay), **after your first edit**, logging each module's
  start and end time and maximum memory. **The base sorry-warning set has ⟨N⟩ entries in ⟨N⟩
  modules** (`campaign/fills/b5a/logs/b5a-fill-unisim-base-sorries.txt`). Yours is `CodeSimulator`'s
  only one. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, **no sorry warning** (for a partial, exactly the target's), and
     no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (⟨N⟩ for a complete delivery).
  3. Re-run `B5aUSImportProbe.lean.txt` (extended by your citations) and the inherited probes:
     continuation 7's import probe
     (`campaign/fills/b5a/inputs/b5a-fill-canon-cont7/CanonCont7ImportProbe.lean.txt`), the
     statements probe (`campaign/gates/wave1-statements/evidence/B5aStatementsProbe.lean.txt`)
     and the note-50 file (`campaign/fills/b5a/evidence/b5a-canon-cont4/CanonNote50.lean.txt`,
     whose `note50_cases` is admission-free since the canonizer's landing): 0 errors.
- **Axiom prints**, within `[propext, Classical.choice, Quot.sound]`, for the target, every new
  private (in an in-module probe), `exists_polyCanonizer`, targets 3–8 and
  `Complexity.baker_gill_solovay`. At the base the target is the only admission of targets 3–8
  and Baker–Gill–Solovay (the review's admission walk), so for a complete delivery all of them
  print within the standard three.
- **Lint:** `python3 -I scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine`
  (base: ⟨0 FAIL, 68 WARN over 84 files⟩; `CodeSimulator`'s are its size and three public
  definitions without a lemma, `MachineFormat.toFinTM`, `codeSkipTableK`, `oneTapeMachineFormat`)
  and `TCSlib/Complexity/Diagonalization` (base: 0 FAIL, 2 WARN over 5 files), 0 FAIL. Add no
  line over 100 characters and no Lean linter warning in your region.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target: ⟨the set at issue: MIG-1 stage S's sorried
specs (`Simulation`, `Composition`, `Encoding`, `ClassP/TimeConstructible`, `Build/Wrappers`,
`Build/Loop`, `Build/Primitives`); `Build/RecordTable`'s rows; `ClassNP/NDNormalForm`'s,
`Diagonalization/NTimeHierarchy`'s and `Diagonalization/NTimeDiagonalizer`'s⟩. If a proof seems to
*need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] The session's shared preflight and cache numbers (quoted from its logs, the cache store's
      log included), **the shared logs copied into this zip**, this item's bootstrap with
      per-module time and memory, and the base blob check.
- [ ] The overlay as the first edit, byte for byte; nothing else outside regions (b)–(d).
- [ ] The checkpoints reached (1–5); the base hash and the ancestor check; the checkpoint zips.
- [ ] Every new declaration with its role; the tapes chosen for each phase; the status paragraph,
      if a partial; for a complete delivery, a proposed `**Implementation.**` paragraph for the
      target's docstring (public-facing; the maintainer edits it in at integration).
- [ ] The ledger, phase by phase, and the final `d`.
- [ ] Promotion candidates, requested shared lemmas and escalations (each stated
      mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file (from an elaborated-constant walk), the
      probe re-run as "N checks of M names", **the seal test with its controls and both raw
      outputs**, and the inspection table. Rule 11: `canonPreserveInstall` unchanged; a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none" otherwise.
- [ ] File size; the final sweep tail; the re-run probes; every axiom print; the lint lines. The
      diff touches only your owned regions.

## Known pitfalls at this pin (hard-won)

- **The startup's conclusion ends in a `let`** (`let c := U.runFrom … T`): destructure it after
  `dsimp only at h`, and keep the start configuration's type ascription
  (`Cfg K Bool Q (pairEncode (pairEncode (Nat.bits t) α) x)`), or the input is not found.
- **The hosted verdict's tapes** are `1 + (F.k + 2 + 1)`: the virtual-input buffer first, then the
  loop's `F.k + 2` body tapes and the counter last (`vhostBank`, `Fin.castSucc`); the summary's
  bank tape is `vhostBank (summaryTape F.k).castSucc`. `us_bank`'s value equations are stated at
  exactly these indices (`Fin.castAdd`, `Fin.natAdd`, `Fin.castSucc`, `Fin.last`).
- **The loop's entry control** is `StepBlock.exit F.k true` (a sigma: rewrite it with `exit_true`
  and `exit_false`), and the counter starts at `counterLoopCfg (some (.dec .run))`.
- **The simps field equations are pointwise and fully applied** (`Cfg.mapState_*`, `vhostCfg_*`,
  `embedEmitCfg_*`, `Cfg.init_*`): `funext` before `rw`, and do not `rw` under a binder that
  the rewritten term mentions; the junction probe shows the pattern.
- **`MultiTapeTM.initCfg` and `NDTM.initCfg` are `@[simp]` definitions:** an unrestricted `simp`
  unfolds them; erase them in the seal and use `MultiTapeTM.initCfg_eq` and
  `MultiTapeTM.toNDTM_initCfg`.
- **Locality is for the run, not the machine**: `NDTM.runWith_initCfg_take` is stated with
  `let`s; `simp only [MultiTapeTM.toNDTM_runWith, MultiTapeTM.toNDTM_initCfg,
  List.length_replicate] at h` exposes the two runs (the route probe).
- **`S` starts from `S.tm.initCfg`**, not from the startup's explicit start: `us_start`
  (`initCfg_with_q₀`) relates them; the composite's `q₀` has no other published equation.
- **`FinTM`'s instance fields are instance-implicit:** build `S` with structure-instance syntax
  (`{ k := …, State := …, tm := … }`); the anonymous constructor does not take them.
- **H1's proofs predate rule 10**: `h1HostedVerdict_effect` passes `MultiTapeTM.initCfg`,
  `Cfg.init`, `FinTM.VirtualTag`, `Action.apply` and `vhostCfg` to `simp` and unfolds
  `MultiTapeTM.step`. Cite it; do not imitate its proof text.
- **`prefix` is a reserved keyword**; do not name a hypothesis `prefix`.
- **`counterLoopOrbit` is an `abbrev`:** `rw` may not fire on it; `exact` and `simp only` do.
- `omega` with products and powers as atoms (`ring` first). The linter needs a literal "Proof
  sketch" before every `sorry` (partial only).
