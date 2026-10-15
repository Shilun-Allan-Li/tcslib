# C1 design note: the nondeterministic time hierarchy ([AB09] Theorem 3.2)

Read-only design note on the campaign tip checkout `wt-c1`. Every path below is relative to
that checkout unless it names the scratchpad. Conventions:

- **VERIFIED** means read in the code or the records at the cited `file:line`.
- **INFERRED** means a conclusion from what was read, not checked by elaboration.
- **ESTIMATE** marks every size figure (lines of landed Lean, including docstrings).

Companion artifacts, in the scratchpad's `c1/` folder:

- `C1HostsDraft.lean` (521 lines): statements of the proposed contracts. It elaborates with
  **0 errors and 5 `sorry` warnings** against `oleans-f7` (`c1/elaboration.log`). Ten of its
  declarations are **proved**, among them the nondeterministic agreement transfer, the replay
  lemma and the derivation of the exponential decider. Appendix A lists them.

---

## 0. Summary

1. **`exists_effectiveNDMachineCode` is already proved** (VERIFIED). It is
   `TuringMachine/NDCodes.lean:258-268`, with no `sorry` in the file. It was proved as the
   third `CodeFormat` instance, the private `ndFormat` (`NDCodes.lean:169-226`), and was
   integrated with fills-4 (`audits/fills-4-integration.md:12,37-39`). CH34-D2 was discharged
   by 12.2c item 8 (plan `AroraBarakChapters3-4Plan.md:684`). Plan §4e's C1 row (`:844`) is
   stale on this point. **C1 is the six sorried statements of `NTimeHierarchy.lean`.**
2. **The route recommendation: guess first, then run deterministically.** The universal NDTM
   and the diagonalizer each guess their whole choice word up front, at linear cost, using
   one small nondeterministic leaf, the *choice writer*. They then run a deterministic
   interpreter that reads the word from a tape. With this route:
   - SC-3's "nondeterministic lifting of the §12.7 counter loop" is no longer needed. No
     nondeterministic loop host is built, and every multi-step host stays deterministic.
   - The only nondeterministic infrastructure is a **slice-wise agreement transfer**, the
     "nondeterministic contract variant", together with an ND phase host. Both are
     **proved** in the draft (§1 of the draft, about 170 lines with docstrings). They are the same lemmas that stage 2's
     nondeterministic form asks for (`audits/evidence/stage2/NOTES.md:155-161`).
3. **The exponential decider `BF` is derived, not built.** `BF := E(UN)`, where `E` is a
   generic exhaustive replay of a *fixed* NDTM by iterative deepening. The derivation of
   `exists_ndAcceptsWithin_decider`'s statement from the universal's statement plus `E` is
   **proved** in the draft (`ndAcceptsWithin_decider_of_universal`).
4. **The H2 step block needs no change.** The ND code is turned per code into the code of its
   *replay machine*. That is a deterministic three-work-tape table, with the choice tape
   last, read once and moved right each step. The interpreter is then H2 at `k = 3`,
   unchanged. The bridge
   `CodeNDTM.serialize = header ++ tableBitsK(false slice) ++ tableBitsK(true slice)` is
   **proved** in the draft. No third parse layer and no ND `MachineFormat` are needed.
5. **The gate's prefix-bound obligation becomes a contract clause.** The interpreter core's
   contract states its time as a function of the *simulated halting time*. This comes free
   from the exact escape time of `counterLoopTMVia_run_escape`
   (`Build/CounterLoop.lean:1306`).
6. **New hosts, by the host-first rule:**
   - the **step-clocked runner**, H3's clock. Its consumers are the diagonalizer, `E`, B6's
     window runner, and a re-derivation of Hydroxyi's `clockTM`;
   - the **ND contract variant**, consumed by C1 and stage 2;
   - the **choice writer**, a member of H5's device family, consumed by the universal, the
     diagonalizer and the normal form;
   - **H2's loop form**, the clocked interpreter loop, which C1 shares with B5a's H1;
   - `E`.

   Each has at least two named consumers, except `E`. Its C1 consumer is `BF`; a second use,
   retiring the private `choiceCore` replay in `Nondeterminism.lean`, is INFERRED (§3.5).
7. **Machine level is confirmed for all of C1** (§3.7). Stage 2's compile bound charges
   `(t + 1)·(… + n + 1)`, which is super-linear in `t` and has a per-step `n` term, so it
   cannot carry CH34-Q8's linear overhead, the `O(n)` locator, or the `|x|`-free exponential
   decider.
8. **Size: about 13k–26k lines in all (ESTIMATE),** including about 1.1k–2.3k for two shared
   hosts (H3's clock and H2's loop form). The largest pieces are the linear normal
   form, the locator with its arithmetic rows, the diagonalizer assembly and `E`. §5 gives
   the per-piece table.
9. **Record corrections** (§7):
   - `clockTM` is recorded as "quadratic" in design §12.7 (`machine-library-design.md:987`)
     and in plan item 12 (`AroraBarakChapters3-4Plan.md:591-595`), but it is a *linear*,
     fused runner (`TimeHierarchy/ClockLoop.lean:345-347`).
   - It cannot be re-derived on the round-based counter loop, only on the step-clocked runner.

---

## 1. The seven statements, their sketches, and what the P3.3 gate settled

### 1.1 Statements (VERIFIED, `TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean` and `TuringMachine/NDCodes.lean`)

| # | Declaration (line) | What it says | What its sketch commits to |
|---|---|---|---|
| 1 | `Turing.exists_timed_universal_NDTM` (121-126) | For every effective ND scheme `c` there is one `UN : FinNDTM Bool` such that for every code `α` there is `C` with, on `⟨⟨bits t, α⟩, x⟩`: every branch halts within `C·(t+1)`, and `UN` accepts within `C·(t+1)` iff `(c.decode α)` accepts `x` within `t`. No `\|x\|` term. | Direct interpretation of the two-tape coded machine; virtual input read in place; **choice bits passed through one per simulated step**; a countdown **fused** into the loop with **amortized** linear cost (`Σ ν₂(j) ≤ t`); a `C`-ledger per code (90-120) |
| 2 | `Turing.exists_ndAcceptsWithin_decider` (146-154) | One deterministic `BF` such that for every `α` there is `C` with `BF` outputting `[true]` or `[false]` for bounded acceptance within `C·2^{C(t+1)}`, on the same input format | Enumerate the `2^t` words on a counter; replay each through the universal's deterministic core with the choices read from the counter; clean up between replays (128-145) |
| 3 | `Turing.FinNDTM.exists_codeNDTM_accepts_linear` (191-197) | Every `N : FinNDTM Bool` has a `CodeNDTM` `M` and a `C` with forward transfer `N` acc. `t` → `M` acc. `C·(t+1)`, and backward transfer **unbounded** (`M` acc. → `∃ t'`, `N` acc. `t'`) | [BGW70] guess-then-verify into **two** work tapes: guess the display on tape A, check control locally on the fly, then `k + 1` verification sweeps replaying each tape on B; `O_N((k+1)(t+1))`; relabel into `Fin` states (158-190) |
| 4 | `Complexity.ntime_hierarchy` (287-291) | `TimeConstructible f`, `TimeConstructible g`, `∀ A, eventually A·(f(n+1) + f n + n + 1) ≤ g n` ⟹ `NTIME f ⊂ NTIME (g + 1)` | Inclusion by finite absorption. Strictness by lazy diagonalization: (i) the fixed-code schedule `i = pair(j, r)`; (ii) the ladder `a = ℓᵢ + 1`, `T*ᵢ = (f a + a + 1)²`, `ℓᵢ₊₁ = 2^{(T*ᵢ)²}`, `ℓ₀ = 2`, located by capped witness runs; (iii) the mid-rung runs the interpreter core on `⟨αⱼ, 1^{n+1}⟩` at nominal budget `g n` under `D`'s own countdown `K·(g n + 1)` with the allowance split and the **prefix-bound obligation**; (iv) the top rung runs `BF` on `⟨bits T*ᵢ, αⱼ, 1^a⟩` and flips; the chain (3.3)/(3.4) (207-286) |
| 5 | `Complexity.ntime_hierarchy_of_pos` (301-305) | The same, with `NTIME g` when `g` is positive | `c(g n + 1) ≤ 2c·g n` and `NTIME.mono` (293-300) |
| 6 | `Complexity.NTIME_linear_ssubset_square` (326-328) | `NTIME (n + 1) ⊂ NTIME ((n + 1)²)` | `ntime_hierarchy_of_pos` at `f = n + 1`, `g = (n + 1)²`; two constructibility witnesses (307-325) |
| 7 | `Turing.exists_effectiveNDMachineCode` (`NDCodes.lean:258-268`) | `Nonempty EffectiveNDMachineCode` | **Proved**: `ndFormat` with `CodeFormat.decode_serialize_pad` and `CodeFormat.exists_canonizer` (arbitrary-time canonizer) |

The module's declared deviations are at `NTimeHierarchy.lean:33-62`:

- the universal is packaged as an iff with an unconditional clock, and cut branches reject;
- the overhead is a linear `C·(t+1)` with a per-code `C`;
- the domination hypothesis has an extra `f n` addend;
- the larger class is `NTIME (g + 1)`.

The relevant semantics, VERIFIED:

- `FinNDTM.AcceptsWithin` (`ClassNP/NTIME.lean:93-96`): some word of length exactly `t`
  halts with output `[true]`.
- `NDTM.HaltsWithin` (`TuringMachine/Nondeterministic.lean:190-191`): every word of length
  `t` halts.
- `NTIME` (`NTIME.lean:174-175`): `∃ c N, N.DecidesInTime L (c·T)`.
- `TimeConstructible` (`ClassP/TimeConstructible.lean:68-71`): `n ≤ T n`, and a machine
  outputs `bits (T n)` within `c(T n + 1)`.

### 1.2 What the gate settled

The gate's records are `audits/ch3-p33-findings.md`, `audits/ch3-p33-r2-findings.md` and
`audits/ch3-p33-resolutions.md`.

- **Round 1** was a FAIL with 0 blockers, 2 majors, 7 minors and 2 notes. Both majors were in
  `ntime_hierarchy`'s sketch, and no statement was refuted.
  - **Major 1:** a per-code universal constant cannot be absorbed by picking a padded large
    index, because padding preserves `decode` but no law preserves cost
    (`ch3-p33-findings.md:19`, with the quantifier argument at `:157-172`).
  - **Major 2:** existential coefficients are not an executable stage locator (`:20`).
  - **The minors:**
    - 2·27 records per state and the `702(n+1)` guard;
    - an arbitrary-time canonizer;
    - an *amortized* rather than pointwise decrement;
    - `(k+1)(t+1)` for the normal form;
    - the true reason timeout-rejection is sound;
    - the `g 0 = 0` pack erratum;
    - "every positive A".
- **Round 2** was a **PASS** with 0 blockers, 0 majors, 2 minors and 2 notes. Two
  constructions close the majors.
  - **Major 1** closes by the fixed-code schedule: one literal code recurs at unbounded stage
    indices, so all thresholds precede stage selection (`ch3-p33-r2-findings.md:24,36-46`).
  - **Major 2** closes by a concrete capped locator. Its total time is `O(n + log³ n)`, with no
    monotonicity of `f` or `g`; a timed-out witness certifies `ℓᵢ₊₁ > n`
    (`:48-115`).
  - **Two clock-ledger points:**
    - for a prefix of `s` decrements from `B`, the additive clock term is
      `s + ⌊log₂ B⌋` (`:128-140`);
    - "interpret the fused outer clock as counting transitions of the controlled
      computation", with a uniform reserve `P(g n + 1)` and `K ≥ P + 2` (`:143-151`).
  - **The construction's arithmetic:** the middle comparison holds at the fixed
    `A* = C_α(C₁c₀ + C₁ + 1) + 1`, and the top uses `C_BF·2^{C_BF(T*+1)} ≤ 2^{(T*)²}`
    (`:153-247`).
- **The two minors were swept:**
  - the ladder is pinned (`ℓ₀ = 2`, with the source formula authoritative);
  - the clock-allowance split is stated, and the interpreter carries a **prefix-bound
    obligation** (`ch3-p33-resolutions.md:32-37`).
- **Carried into the fill briefs** (`ch3-p33-resolutions.md:50-60`):
  - the schedule and unranking;
  - the seeded ladder with the capped locator and its amortized ledger;
  - the self-clocked interpreter core at a fixed `K` with the prefix bound;
  - the two transfer instantiations, `f(n+1)` mid-rung and `f a` at the bottom;
  - the chain induction;
  - the amortized countdown;
  - the `(k+1)(t+1)` ledger;
  - the auditor's sanity lemmas: zero-step non-acceptance, accept-at-any-time iff
    accept-at-`T` under halting, `workPair` injectivity, and the round trip.

**What this note changes, and what it keeps.** All six statements are kept verbatim. Three
sketch-level routes change, and each is a declared deviation for the next gate:

- **Universal, items 1 and 4(iii):** the choice word is guessed up front instead of passed
  through per step.
- **Item 2:** `BF := E(UN)` instead of a dedicated replay loop.
- **Item 4(iii):** the prefix bound is a clause of the interpreter-core contract, so the
  sketch's obligation is discharged by the contract rather than by a separate argument.

Everything else the gate carried is kept, in particular the schedule, the ladder, the capped
locator and its ledger, the fused physical clock, the transfers and the chain. One point is
unchanged but left open: the docstring's `pair(j, r)` names no pairing
(`NTimeHierarchy.lean:225-229`). The
2-adic pairing `i + 1 = 2^j·(2r + 1)` is a valid choice and is cheap on machines (§2.5).

---

## 2. The route, step by step

Status markers:

- **[pub]** exists and is public (file:line);
- **[priv]** exists privately (where);
- **[draft]** is stated in `C1HostsDraft.lean`, with "proved" or "sorry";
- **[missing]**.

### 2.1 Overview

```
UN  (exists_timed_universal_NDTM), an NDTM assembled by the ND phase host:
    parse ⟨⟨bits t, α⟩, x⟩ ─▶ install replay table + unary q₀ + counter (per-code setup)
    ─▶ expand t to a unary block on the stream tape ─▶ GUESS: choice writer overwrites it (t+1 steps)
    ─▶ rewind ─▶ copy the input window x.take (t+1) to a buffer
    ─▶ Z1( clocked interpreter loop: counterLoopTMVia over H2 rounds at k = 3 ) ─▶ verdict, halt
        (everything after GUESS is deterministic: R, the ND interpreter core, §3.6)

BF  (exists_ndAcceptsWithin_decider) := E(UN)       (derivation proved in the draft)

NF  (exists_codeNDTM_accepts_linear), a per-N NDTM with two work tapes A, B:
    GUESS display records on A (choice writer, controller flavor: stop after the end-flagged record)
    ─▶ sweep 0: control-local consistency + output = [true]
    ─▶ sweep 1: input claims vs native input ─▶ sweeps 2..k+1: tape j claims replayed on B
    ─▶ relabel states into Fin (n+1)

D   (the diagonalizer of ntime_hierarchy), an NDTM:
    unary check ─▶ bits (g n) by g's witness ─▶ GUESS g n stream bits ─▶ locator (stage, j, αⱼ, a, T*, rung)
    ─▶ mid:  step-clock( Z1( R on ⟨⟨bits g n, αⱼ⟩, 1^{n+1}⟩ with the stream ) ), accept iff R accepts in time
    ─▶ top:  step-clock( Z1( BF on ⟨⟨bits T*, αⱼ⟩, 1^a⟩ ) ), output the flipped verdict, default reject
```

### 2.2 The universal NDTM (statement 1)

| Step | Pieces | Status |
|---|---|---|
| U1. Parse the nested header (`bits t`, `α`), leaving the input head at `x` | Hydroxyi's `preTM` (code-prefix duplication); B5a's native-input binary-header loader; `UniversalStartup`'s pair-suffix pieces | [pub] `TimeHierarchy/CodePrefix.lean:113`; [priv] in `CodeSimulator.lean` (canonizer front end, 283-1945); [pub] `UniversalStartup.lean:338,373`. A clean public "split a `pairEncode` header onto tapes" row is [missing] (INFERRED; none found) |
| U2. Per-code setup: canonize `α`, then re-serialize to the **replay code** `serializeK (decode α).tm.replayTM` and the unary `q₀` | `c.canonizer` (the scheme's field, `NDCodes.lean:154-160`); `codePrim_machine` (any `Primrec` string function, arbitrary time) [pub] `MathlibBridge.lean:1102`; `FinTM.computesFunInTime_comp` [pub] `Composition.lean:391`; `FinTM.exists_installCallTM` [pub] `Build/Loop.lean:4912`; the re-serialization `g` with `Primrec g` and `g M.serialize = serializeK M.tm.replayTM` | [missing]; [draft] `exists_replayCanonizer` (sorry). The bridge `CodeNDTM.serialize_eq_tableBitsK` is [draft, proved] |
| U3. Counter word `bits t` (and a saved copy) | `copyTM` [pub] `Build/Catalog.lean:209,1098` | exists |
| U4. Expand `t` to a unary block on the stream tape | `expandTM` [pub] `Build/CounterLoop.lean:1524,1545` | exists |
| U5. Guess the stream (`t + 1` steps, branch-independent timing) | the choice writer, bounded flavor | [missing]; [draft] `ndWriterTM` and `ndWriterTM_run_block` (sorry). Private precedent: `contGuessTM`, `ClassNP/Nondeterminism.lean:1125` |
| U6. Rewind the stream head | `skipBackTM` [pub] `Catalog.lean:11805,11829` | exists |
| U7. Copy the input window `x.take (t + 1)` to a buffer (no `\|x\|` term), with **input locality** (a run of at most `t` steps cannot read past position `t + 1`) | a bounded input copy, as a `counterLoopTMVia` instance with a one-cell native-copy body; an NDTM input-locality lemma | both [missing]. `inputCopyTM` copies the whole input ([pub] `Build/Scan.lean:375,499`). No public input-locality lemma was found |
| U8. The simulation: one round = one simulated step of the replay machine | H2 `h1RoundTM k` / `h1Round_effect` (one transition of any `k`-tape table, `0 < T ≤ 50·(\|table\|+1)`, silent, head envelope); its loop form (`counterLoopTMVia` over H2 rounds, verdict exits, config-generic); Z1 `vhostEmitTM_runFrom` [pub] `Build/VirtualInput.lean:243`; the replay lemma | H2 [priv] `CodeSimulator.lean:3979,4722,4780` (about 2.9k lines of `h1*` privates, 2040-4936; promotion is F7-1(a), `backlog.md:549-557`). Loop form [missing]: it is B5a's open "hosted, clocked assembly" (`CodeSimulator.lean:44-56`). Replay lemma [draft, **proved**] `NDTM.replayTM_runFrom` |
| U9. Verdict: on `escape`, accept iff the summary says exactly `[true]`; on `done`, reject; then emit and halt | H2's summary convention (`outputSummary`/`summaryEmit`, [priv] `CodeSimulator.lean:1959,1965`) | part of the loop form |
| U10. ND assembly: the iff and all-branch halting | the ND agreement transfer + `phaseHostND` + the writer contract; `AcceptsWithin.mono` [pub] `NTIME.lean:106`; `runWith_of_halt` [pub] `Nondeterministic.lean:178` | transfer, phase host and phase lemma [draft, **proved**]; a generic "guess-then-run" assembly lemma (§3.1) [missing] |
| U11. Ledger `C_α(t + 1)` | `counterOverhead_le_of_le` / `counterOverhead_le` [pub] `CounterLoop.lean:511,541`; H2's `50·(\|table\|+1)` | exists ([priv] for H2) |

This is linear: the guess, expansion, rewind and window copy are each `O(t)`, and the loop
costs `t·(50(|table| + 1) + O(1)) + 4t + 2|bits t|`. Per-code setup is a constant per `α`.
CH34-Q8 is preserved (INFERRED from the cited bounds).

### 2.3 The exponential decider (statement 2)

`BF := E(UN)`, where `E = FinNDTM.exists_exhaustiveDecider UN` ([draft], sorry). The
statement's derivation, `ndAcceptsWithin_decider_of_universal`, is [draft, **proved**], with
constant `C_E·(C_α + 1)`. `E` itself:

| Step | Pieces | Status |
|---|---|---|
| E1. Outer loop over `L = 0, 1, …` until every branch of length `L` has halted (at most `T` rounds) | a repeat-until loop. The phase host with a self-redirect plus the consumer's own induction suffices | [pub] `phaseHostTM_run`, `Build/Seam.lean:813,830` |
| E2. Inner loop over the `2^L` words of length `L` | counter `L` falses then `true`; `counterLoopTMVia` [pub] `CounterLoop.lean:1220,1306`; `incrementTM` [pub] `Catalog.lean:1184,1241` | exists |
| E3. Replay the fixed `N` under the word for `L` steps | `N.replayTM` (a fixed deterministic machine); the step-clocked runner with budget `L` | replay [draft, proved]; runner [missing], [draft] `exists_stepClockTM` (sorry). Private precedent: `choiceCore`, `Nondeterminism.lean:247-420` |
| E4. Capture the replayed output | `embedSilentTM` / `vhostSilentTM` [pub] `VirtualInput.lean:160,434` | exists |
| E5. Reset: clear work tapes within radius `L` (the replay may write inner blanks, so `clearTM` cannot find the extent); rewind the native input head | a counter-driven **window clear** row; the input rewind rows | window clear [missing]; rewind exists ([pub] `Simulation.lean:446`, `timed_rewind`; INFERRED usable) |
| E6. Ledger `Σ_{L≤T} 2^L·O_N(L + 1) ≤ C·2^{C(T+1)}` | arithmetic | [missing] (pure) |

### 2.4 The linear normal form (statement 3)

| Step | Pieces | Status |
|---|---|---|
| N1. Guess fixed-width records `(bᵣ, σᵣ, endᵣ)` on tape A: choice bit, the `k + 1` claimed reads in 2-bit blocks, an end flag; stop after the first end-flagged record | the choice writer, controller flavor (a finite automaton counts the record width and reads the flag) | [missing]; [draft] `ndWriterTM` (definition only) |
| N2. Sweep 0: track `N`'s state in finite control, recompute `aᵣ = N.tr bᵣ qᵣ σᵣ`, check that the end flag is set iff `aᵣ` halts, and that the summarized output is `[true]` | a fixed-width record reader (the generalization of B5a's private `h1RecordTM`, [priv] `CodeSimulator.lean:2096`, backlog F7-1(c)); `skipBackTM`; the phase host | reader [missing] (public form) |
| N3. Sweep 1: the input claims, checked by moving the native input head per `aᵣ.inputTape` | the native input head; the input rewind | [missing] (per-`N` control) |
| N4. Sweeps 2..k+1: replay tape `j` on B as 2-bit blocks `(visited, symbol)`, so the visited region is contiguous and marker-cleared; check `σᵣ[j]` against B; apply `aᵣ`'s write and move | a block-encoded replay sweep; a marker-guided clear | [missing] |
| N5. Package into `CodeNDTM`: binary alphabet, exactly 2 work tapes, finite states relabelled to `Fin (n+1)` | `NDTM.relabelState` / `relabelState_runWith` | [draft, **proved**]. Deterministic mirror: [pub] `StateRenaming.lean:90,116` |
| N6. Forward: realize an accepting run's display as a choice word, `C(t + 1)` with `k + 2` sweeps. Backward: a verified display is a genuine run, by induction on `r`: if the claimed reads up to `r - 1` are genuine, so are the recomputed actions, so each replayed tape at `r` is genuine, so the sweep checks make `σᵣ` genuine | pure induction plus the sweep contracts | [missing] |
| N7. ND assembly (guess, then deterministic sweeps) | the ND transfer + `phaseHostND` | [draft, proved] |

Two remarks on this design (INFERRED):

- The per-step actions are *recomputed* by finite control in every sweep rather than guessed.
  The guess is therefore a dumb writer, and all checks are deterministic.
- The end flag makes guess termination local.

### 2.5 The diagonalizer and the theorem (statements 4–6)

| Step | Pieces | Status |
|---|---|---|
| H0. Inclusion `NTIME f ⊆ NTIME (g + 1)` by finite absorption, using `F = 1 + Σ_{j<N} f j` | the mirror of `Complexity.time_hierarchy`'s inclusion [pub] `TimeHierarchy/Diagonal.lean:268-291` | [missing] (pure, small) |
| D1. Reject non-unary input; reject `n ≤ 2` (the seed) | `inputFoldTM` [pub] `Build/Scan.lean:535,645` | exists |
| D2. `bits (g n)` by `g`'s witness on the native input | `FinTM.exists_inputCallTM` [pub] `Build/InputCall.lean:82` | exists |
| D3. Guess `g n` stream bits | `expandTM` + the choice writer + `skipBackTM` | writer [missing] |
| D4. **Locator** (audit round 2 §2): iterate stages from `ℓ₀ = 2`. At each stage prepare `1^a` (Z1 buffer), run `f`'s witness **capped** at `c_f(n + 1)` (step-clocked runner), and compare `f a` with `n` (binary `≤`). If small, form `u = f a + a + 1` in unary (geometric cost) and compare `u⁴` with `⌊log₂ n⌋` (capped unary arithmetic, `O(log² n)`), testing whether `n` is a power of two in the equal case; otherwise write `ℓᵢ₊₁` in binary, increment and advance. At the end, schedule `j = ν₂(i + 1)` (the 2-adic pairing) and unrank `αⱼ` (`bits (j + 1)` without its top bit) | `exists_inputLengthTM` [pub] `Build/InputLength.lean:473`; `expandTM`; `incrementTM`; `compareTM` is **equality only** [pub] `Catalog.lean:258-266`; a numeric `≤` row, capped unary multiply, a power-of-two test, `ν₂` and unranking rows, and the amortized `O(n)` ledger | [missing] (the arithmetic rows overlap stage 2's planned rows, design §15a "New rows needed", `machine-library-design.md` §15a) |
| D5. Materialize `⟨⟨bits t, αⱼ⟩, 1^m⟩` on a buffer | a `pairEncode` writer (bit doubling and separator) | [missing] (a candidate instance of §13d G2's mapped sweeps) |
| D6. Mid-rung: run `R` (§3.6) hosted by Z1 on the materialized word, with the guessed stream, under the step-clocked runner at `K'(g n + 1)` | Z1 [pub]; the step-clocked runner [missing]; `R` [missing] | |
| D7. Top rung: run `BF` hosted by `vhostSilentTM` on `⟨⟨bits T*, αⱼ⟩, 1^a⟩` under the same runner, and emit the negated completed verdict (default reject) | `vhostSilentTM_runFrom` [pub] `VirtualInput.lean:434`; `BF` from `E` | |
| D8. `D ∈ NTIME (g + 1)` by construction: every phase is code-independent or clocked. Characterize `L(D)` per rung (mid: `∃ s`, the clocked `R` accepts; top: the clocked `BF` completes with `[false]`) | the ND assembly lemma; the clock contract | [missing] |
| D9. The chain: fix `N` and `c₀`; take `M'`, `C₁` from statement 3, `α = c.encode M'` (recovered by `NDMachineCode.decode_encode`, `NDCodes.lean:142`), `j₀ = rank α`, and `C_α`, `C_BF`. Choose a stage with `ν₂(i + 1) = j₀` past all thresholds. The mid equivalences (forward transfer + the prefix clause; backward transfer + truncation by `NTIME.mono`'s argument) and the top flip contradict | the contracts of statements 1 and 3, `R`, `E`; `AcceptsWithin.mono`; `run_take_of_halted` [pub] `ChoiceWords.lean` | [missing] (pure) |
| P. `ntime_hierarchy_of_pos` | the mirror of `time_hierarchy_of_pos` [pub] `Diagonal.lean:299-311` | [missing] (pure; can be proved now, modulo statement 4) |
| S. Showcase: the arithmetic `A(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`; `TimeConstructible (n + 1)` and `TimeConstructible ((n + 1)²)` | `timeConstructible_id` [pub] `TimeConstructible.lean:422` as precedent; unary square via `expandTM`, then binary counting with amortized `incrementTM` | witnesses [missing] (independent of everything else) |

---

## 3. Hosts and contracts to design (design §14 vocabulary)

### 3.1 The nondeterministic contract variant (shared with stage 2)

**What a nondeterministic run satisfies.** For `N : NDTM`, a choice word `w` determines one
branch, `N.runWith w` (`Nondeterministic.lean:131-133`), and halting absorbs (`:178-182`). The
variant needs no new structure for C1. What it needs is one **transfer theorem**: every
deterministic phase contract becomes a statement about every branch. Here it is, proved
(`C1HostsDraft.lean`, §1).

```lean
theorem NDTM.runWith_mapState_of_agreeOn (src : NDTM k Γ S) (host : NDTM k Γ H) (emb : S ↪ H)
    (good : S → Prop)
    (hagree : ∀ b q, good q → ∀ inp work,
      host.tr b (emb q) inp work = (src.tr b q inp work).mapState emb)
    (c : Cfg k Γ S x) (w : List Bool)
    (hguard : ∀ u < w.length, ∀ q, (src.runWith (w.take u) c).state = some q → good q) :
    host.runWith w (c.mapState emb) = (src.runWith w c).mapState emb
```

Two corollaries, both proved:

- **The deterministic-source form** `runWith_mapState_of_agreeOn_det`, with
  `src : MultiTapeTM`. Every branch of `host` runs the renamed `src.runFrom c |w|` while
  `src` stays in good states. It is the ND mirror of
  `MultiTapeTM.runFrom_mapState_of_agreeOn` ([pub] `Build/Embed.lean:1010`). A MIG-0a
  `Contract` of `src` (`audits/evidence/mig0/Contract-draft.lean.txt:84-101`) thereby holds
  for every word of length `time` (endpoint, cut and envelope).
- **The slice lemma** `runWith_eq_fixChoice_runFrom`. On a segment whose live states have
  coinciding transitions, every word drives `tm.fixChoice b₀`'s run. This is exactly what
  stage 2's ND form asks for (`audits/evidence/stage2/NOTES.md:158-161`), and it generalizes
  `MultiTapeTM.toNDTM_runWith` (`Nondeterministic.lean:251-258`).

**The ND phase host** `NDTM.phaseHostND`. This is `phaseHostTM` over ND phases, with
deterministic phases entering as `toNDTM`. Two facts about it are proved:

- `phaseHostND_fixChoice` holds by `rfl`: each slice is the deterministic phase host of the
  slices.
- `phaseHostND_run` is the ND `phaseHostTM_run`.

`NDTM.relabelState` with `relabelState_runWith` is also proved; it is needed for N5.

**The proposed contract-level lift (for MIG-0b, not drafted).** `Contract.toND`: given a
`Contract src entry exits ι x` and slice-wise agreement of `host` with `src` (renamed) on the
non-exit states, then for every word `w` with `|w| = time`, `host.runWith w` reaches the
renamed endpoint, and no shorter word reaches a renamed exit. It is a direct consequence of
the deterministic-source form, so it is a thin wrapper, as MIG-0a's compositions are. §16
lists exactly this variant as "later" (`machine-library-design.md:3589`).

**The principle that decides what is lifted, and what is not** (INFERRED, and the reason
SC-3 dissolves):

- A deterministic host whose correctness is a **per-step lockstep** lifts to NDTMs at no cost,
  by applying it slice by slice and the one-step identity. Examples are Z1
  (`vhostEmitTM_step` is public, `VirtualInput.lean:188`), the R1 embedding, state renaming
  and the phase host.
- A host whose contract composes **multi-step rounds** does *not* lift: a branch mixes slices
  across rounds, so the whole-run contract of a single slice never applies. Examples are
  `counterLoopTMVia` and the step-clocked runner.
- **The rule:** never put a choice inside a round body. Guess first, then run
  deterministically (UN, D); or keep the choices in phases dispatched step by step by a phase
  host (stage 2's per-instruction coin phases).

**The assembly lemma (proposed, not drafted): "guess, then run".** Consider an NDTM built by
`phaseHostND` as follows: a deterministic prefix up to a block of length `m`, the bounded
choice writer, then a deterministic suffix `Q`. The lemma states:

- **all-branch halting:** if `Q` halts from every written configuration;
- **acceptance:** the NDTM accepts iff `∃ s, |s| = m`, and `Q` accepts from the configuration
  with `s` written.

Consumers are UN and D, and possibly a re-derivation of `NP ⊆ ⋃ NTIME`'s private `b2Host`
(`Nondeterminism.lean:1466`). ESTIMATE 200–400 lines.

### 3.2 H2 with choices: generalize the block, use a separate host, or neither?

H2 (`h1RoundTM k`, `h1RoundRep`, `h1Round_effect`, [priv] `CodeSimulator.lean:3979-4936`) is
one finite machine per `k`. It interprets one transition of a table `tableBitsK tr`, which sits
on its table tape with the head at 0 (`h1RoundRep`, `:4722-4733`). Three options:

| Option | What changes | Cost and risk |
|---|---|---|
| (a) **Choice-bit-indexed H2.** Generalize the lookup to the ND order (choice outermost) or a table offset | Change H2's private lookup (`h1SeekTM`, `:3012`), which follows `tableBitsK`'s exact read order; the representation pins the table head at 0 | Edits the block under promotion; reopens its proof |
| (b) **Separate host.** A dispatcher reads the choice bit and enters one of two R1-embedded H2 copies, with tables on two tapes (`tableBitsK` of each slice) | No H2 change; a C1-specific round body, its own loop and verdict, and a per-code split of the two tables | Duplicates B5a's loop and verdict assembly with a different body |
| (c) **Neither: interpret the replay machine.** Per code, compute the code of `N.replayTM` (`C1HostsDraft.lean` §2: a deterministic `(k + 1)`-tape machine that reads its choice word from the last tape and moves it right); run H2 at `k = 3` with the stream preloaded on the mirrored choice tape | No machine change at all. The ND content is *data*: a primitive recursive re-serialization (`exists_replayCanonizer`) and the **proved** replay lemma | One per-code transformer (ESTIMATE 400–900 lines); the H2 table is about 1.5× larger (81 rather than 54 records per state), a per-code constant |

**Recommendation: (c).**

- H2 and its loop form are reused byte for byte, shared with B5a's H1, U-1 and B6's `U₀`.
- No choice-indexed variant of a host is ever built, which is what the host-first rule asks
  for.
- The bridge between the ND format and the deterministic layout is
  `CodeNDTM.serialize_eq_tableBitsK` (proved). It is needed for (b) as well; for (c) it
  anchors the transformer's correctness proof.

### 3.3 The nondeterministic counter loop and clock (SC-3)

SC-3 (`machine-library-design.md:1108-1111`) asked for "a choice-stream lifting contract …
with branch alignment through the bookkeeping pauses". With the route of §2, **no
nondeterministic counter loop is needed**:

- **The universal.** The choice word is on a tape before the deterministic interpreter
  starts. "Branch alignment" reduces to the bounded writer's contract (branch-independent
  timing; the word written is `w.take m`) plus the replay lemma.
- **The diagonalizer.** Same pattern: the stream is guessed before the locator.
- **The other SC-3 consumer listed in the design**, `PATH_mem_NL` (`:1424`, `:1934`), moved to
  programs with read-once coins (§16b item 4). Stage 2 needs §3.1's transfer and phase host,
  not a loop.

**Recommendation:** close SC-3 as "dissolved by the guess-first route", with §3.1 as its
recorded replacement.

**What D does need is a *physical-step* clock**, not a round counter. The audit is explicit
(`ch3-p33-r2-findings.md:143`): the countdown must cut canonization and every code-dependent
operation uniformly. `counterLoopTMVia` cannot be that clock. Its rounds return to one anchor,
so a body's state does not survive between rounds (`CounterLoop.lean:593-627`). The proposal
is the **step-clocked runner**, H3's clock layer ([draft] `exists_stepClockTM`, sorry):

- **The machine.** One decrement is fused with every body transition. The counter is the last
  tape, and two exit families carry the body state:
  - `finish s`: the body reached a stop configuration, halted or a live `stopAt` state;
  - `timeout s`: the counter is exhausted.
- **The contract.** It is config-level and exact up to the amortized term:
  - if the body first stops at `τ ≤ d`, the host reaches `finish` with the body's endpoint
    within `5τ + 2|w| + 2`;
  - otherwise it reaches `timeout` with the body's configuration at `d` within
    `5d + 2|w| + 2`;
  - no earlier exit in either case.

  The bound comes from the per-step decrement cost `2ν₂ + 2` and the potential argument
  already proved for `counterOverhead` (`CounterLoop.lean:482-516`). The landed form should
  state an exact time and use MIG-0b's round layer.
- **Consumers:**
  - D's mid rung, top rung and locator caps;
  - `E`'s replays;
  - B6's three-exit windowed runner, whose design is still open (`backlog.md:699-705`);
  - a 12.2c re-derivation of Hydroxyi's `clockTM` (`TimeHierarchy/ClockMachine.lean:275`).
- **The precedent.** That `clockTM` is a public, *linear* fused runner at the `FinTM` level
  (`ClockLoop.lean:345-347`: `tK + 4|s| + |x| + 4·val(s) + 6`). It is not composable: it runs
  from `W`'s initial configuration on the native input and emits only a negated
  `[true]`-test.

### 3.4 Input devices (H5)

- **Computed input is not needed by C1** (INFERRED from the ledgers). Every computed input of
  the diagonalizer has length `O(n)`: `⟨⟨bits g n, αⱼ⟩, 1^{n+1}⟩`, `⟨⟨bits T*, αⱼ⟩, 1^a⟩`
  with `a ≤ n`, and the witness inputs `1^a`. Since `n ≤ g n` (`TimeConstructible`), it can be
  materialized and hosted by Z1 within the fixed allowance.
- **The universal's `x` must not be copied whole**, because the statement has no `|x|` term.
  Two devices work:
  - **(i) the bounded window copy.** Copy `x.take (t + 1)` in `O(t)`, using a
    `counterLoopTMVia` instance with a one-cell native-copy body, then use Z1 and an NDTM
    input-locality lemma. Branches of at most `t` steps never read past position `t + 1`
    (round-1 audit, `ch3-p33-findings.md:105`; test A5 at `:202`).
  - **(ii) the in-place suffix device.** Read `x` inside the native input behind a marker,
    composing the public `universalInput_read`/`universalInput_move`
    (`UniversalStartup.lean:338,373`). This is the "suffix-input host" that backlog's H2 entry
    and U-1 need (`backlog.md:1354-1368`, `:424-457`).

  **Recommendation:** (i) for C1, with no new device (ESTIMATE 300–650 lines). (ii) stays with
  U-1, whose `universal` has no deadline and so cannot truncate.
- **New device: the choice writer** ([draft] `ndWriterTM`, `ndWriterTM_run_block`, sorry). It
  is the guessed flavor of a *choice source*, alongside two others:
  - the buffered stream on a tape, which is `R`'s view;
  - the enumerated stream, which is `E`'s counter.

  It has two flavors:
  - **bounded:** overwrite a nonblank block, `m + 1` steps for every word, with no shorter
    word reaching `done`;
  - **controller-stopped:** a finite automaton over the written bits, for the normal form.

  It is H5-family by §14's definition of an input device. Its consumers are UN, D and NF.

### 3.5 `E`, the exhaustive replay of a fixed NDTM

```lean
theorem FinNDTM.exists_exhaustiveDecider (N : FinNDTM Bool) :
    ∃ (E : FinTM Bool) (C : ℕ), ∀ z T, N.tm.HaltsWithin z T →
      (N.AcceptsWithin z T → E.ComputesInTime z [true] (C * 2 ^ (C * (T + 1)))) ∧
      (¬N.AcceptsWithin z T → E.ComputesInTime z [false] (C * 2 ^ (C * (T + 1))))
```

- `T` is per input and need not be computable: iterative deepening finds the first all-halting
  `L ≤ T`.
- It is TM-intrinsic ("this trivial exponential simulation"), and it is the generic machine
  core of `NTIME(T) ⊆ DTIME(2^{O(T)})`.
- Its only C1 consumer is `BF`. **INFERRED:** it can later retire the private `choiceCore`
  replay of `Nondeterminism.lean` (`:247-420`), which replays a fixed `N` on a choice word.
- ESTIMATE 1.2k–2.5k lines, with the window-clear row (150–300).

### 3.6 The ND interpreter core `R` (shared by UN and D)

[draft] `exists_ndInterpreterCore` (sorry). `R` is one deterministic module, uniform over
codes, with a designated stream tape `j`.

- **Entry configuration:** native input `⟨⟨bits t, α⟩, x⟩`; stream `s`, with `t ≤ |s|`, on
  tape `j`; every other tape blank.
- **Exit:** it reaches `accept` or `reject` according to whether the decoded machine's branch
  along `s.take t` halts with output `[true]`, and no exit earlier.
- **Time, with a per-code `C`:**
  - **the prefix form:** at most `C·(t' + 1) + 2|bits t|` when that branch first halts at
    `t' ≤ t`;
  - at most `C·(t + 1)` in every case.

The prefix clause is the gate's prefix-bound obligation (`ch3-p33-resolutions.md:37`). It is
free from the exact escape time of `counterLoopTMVia_run_escape` and from
`counterOverhead_le_of_le` (`4r + 2|w|`). If the gate prefers it, D can avoid the clause by
guessing a nominal budget `t' ≤ g n` (a fallback, INFERRED sound by re-running the mid-rung
chain of `ch3-p33-r2-findings.md:153-192` with `t'` in place of `g n`).

### 3.7 Machine level: confirmed

Design §16 decision 3 (`machine-library-design.md:3555`) keeps "the hierarchy constructions,
and the universal machine" as machines. Each C1 piece was checked against stage 2's drafted
bound, `A·(t + 1)·(f·(W + 1) + W² + n + 1)`, with an `n` term in every step (design §15d):

- **The universal and the normal form** need overhead *linear* in `t` with a per-code
  constant. A compiled program cannot give it, since its overhead is at least `t·W²`.
- **The locator** must run in `O(n)`. Note that `hfg` forces `g n = ω(n)`, but `g` can be as
  slow as `n·log log n`. The program form costs `Θ(n)` per step, hence `n·polylog n`, which is
  too slow.
- **`E` and `BF`** must have no `|x|` term. The program form pays `n` per step, so it fails.

**Confirmed.** One caveat, a challenge only to stage 2's bound and not to this decision: if
PROG-4 charged the input seek only on `rdIn` steps, the locator's pure arithmetic could be a
program. This is not recommended for C1.

---

## 4. The ND code scheme (`exists_effectiveNDMachineCode`)

- **Status: proved** (§0 item 1). The CH34-D2 question (a third format-specific parse layer
  against `MachineFormat`) was settled by building the third format as a **`CodeFormat`
  instance**: `ndFormat` is two `CodeTable2` tables, false choice first, with guard 702. The
  parser, round trip and arbitrary-time canonizer came from the shared layer. No ND copy of
  the parser exists (VERIFIED, `NDCodes.lean:79-87,162-268`).
- **What C1 still needs from the code layer:**
  1. The bridge `CodeNDTM.serialize_eq_tableBitsK` (**proved** in the draft, 4 lines, from
     `tableBitsK_two`, `CodeSimulator.lean:125-130`). Its home is a C1 module that imports
     both `NDCodes` and `CodeSimulator`, since neither imports the other (VERIFIED from their
     import lines).
  2. The per-code replay canonizer (`exists_replayCanonizer`):
     - **the function:** a list-level `g` with `Primrec g` and
       `g M.serialize = serializeK M.tm.replayTM`;
     - **the records:** split by `codeSkipActionK` (`Primrec₂`, `MathlibBridge.lean:246`) and
       re-emitted in the `workReadsK 3` order with the choice-tape field `(none, +1)`;
     - **the machine:** compiled by `codePrim_machine` and composed with `c.canonizer` by
       `computesFunInTime_comp`.

     It needs no public `ndFormat`, because `g` is defined on lists.
- **`MachineFormat` (`CodeSimulator.lean:150-159`).** Design §12.11 says "NDCodes is not an
  instance: ND codes denote NDTMs and need no interpreter" (`machine-library-design.md:2470`).
  That holds for B5a. C1 *does* interpret ND codes, but through the replay code, which is a
  deterministic `serializeK` table, so the H1/H2 machinery applies to raw tables without any
  format instance. **Recommendation: no `NDMachineFormat`, no third parse layer, and no change
  to `NDCodes`.** Add the bridge lemma and the replay canonizer to the C1 host module.

---

## 5. Order of work, waits, and sizes (all sizes ESTIMATE, in landed lines)

The pieces, in proposed batches. The first column says what each can start on.

| Batch | Piece | Waits on | Size |
|---|---|---|---|
| **C1-0, now** | `ntime_hierarchy_of_pos` (proved modulo statement 4) and the inclusion lemma H0 | nothing | 150–300 |
| **C1-0, now** | The showcase: arithmetic, `TimeConstructible (n + 1)`, `TimeConstructible ((n + 1)²)`. These are new public statements, so a small statement gate is needed if they land in `ClassP/TimeConstructible.lean` | nothing | 500–1,200 |
| **C1-A, statement phase now** | §3.1's ND transfer, corollaries, `phaseHostND`, relabel; §2's `replayTM` and replay lemma. All proved in the draft; homes: run-level lemmas in `TuringMachine/Nondeterministic.lean` (or a new `NondeterministicTransfer.lean`), and `phaseHostND` beside `phaseHostTM` | a statement gate | 300–500 (mostly written) |
| **C1-A** | The choice writer (both flavors) and the "guess, then run" assembly lemma | MIG-0a, if stated as a `Contract`; otherwise nothing | 400–850 |
| **C1-A** | `E`'s statement, with the BF derivation (proved) | a statement gate | 50 |
| **C1-A** | The bridge (proved) and the replay canonizer | nothing | 450–1,000 |
| **H3-clock, a joint statement phase with B6** | The step-clocked runner | MIG-0b's round layer (or the current counter-loop calculus); joint design with RD-3's three-exit runner | 700–1,400 |
| **C1-B** | `E`'s fill (iterative deepening, enumeration, window clear) | H3-clock | 1,200–2,500 |
| **C1-C** | `R`: setup, window copy and input locality, Z1-hosted loop, verdict, prefix ledger | **H2 promotion (F7-1(a)), with its loop form made public**. The loop is B5a's open assembly, so it should be built once, public, then cited by B5a H1 and C1. Also MIG-0a for `R`'s statement form | 1,500–3,000 (plus H2's loop form, 400–900, shared) |
| **C1-C** | UN assembly (statement 1) | `R`, C1-A | 500–1,000 |
| **C1-D** | The normal form (statement 3) | C1-A (writer, transfer). A public fixed-width record reader would serve here and in F7-1(c) | 2,500–5,000 |
| **C1-E** | The locator, its arithmetic rows, the materialization writer, the D assembly, `D ∈ NTIME (g + 1)`, the chain, statement 4 | H3-clock, C1-C, C1-B (`BF`), C1-D. Coordinate the arithmetic rows with stage 2's planned rows | 4,000–8,000 |

**Total: about 13k–26k lines (ESTIMATE; the table's sum),** including the two shared hosts
(H3's clock and H2's loop form, about 1.1k–2.3k). The estimates rest on the measured sizes of
analogous delivered pieces:

- H2's private region, about 2.9k lines;
- Hydroxyi's clocked runner, 908 lines (`ClockMachine` 539 + `ClockLoop` 369);
- `Nondeterminism.lean`'s two nondeterminism constructions, about 0.9k and 1.3k lines (MEASURED
  by line ranges: `NTIME ⊆ NP`, 132–1035; `NP ⊆ ⋃ NTIME`, 1044–2330).

**What can start now:** C1-0, C1-A, and the replay canonizer.

**What waits:**

- **H2 promotion and the loop form** gate C1-C.
- **MIG-0a** gates the `Contract`-form statements of the new devices. The run-level transfer
  does not wait for it.
- **MIG-0b** gates the step clock's round-layer form, and `Contract.toND` lands with it.
- **B5a's completion** is coupled through the shared loop form, which should be built once and
  public.

**The critical path:** H2 promotion and the loop form, then `R` and UN, then (with
H3-clock and `E`) the diagonalizer. The normal form runs in parallel.

---

## 6. Open questions for the user

1. **Adopt the guess-first route for UN and D?** It changes the sketch route of statements 1
   and 4(iii), not their statements.
   - Under it, SC-3 closes with no nondeterministic loop host, and the only ND
     infrastructure is §3.1's proved transfer and phase host, which stage 2 needs anyway.
   - Linear overhead (CH34-Q8) is unaffected: guessing costs `O(t)`.
   - *Recommendation: yes.* Record it as a declared sketch deviation, and audit it in the
     statement gate of the C1 host contracts.
2. **Derive `BF` as `E(UN)`,** with `E` a public generic theorem
   (`FinNDTM.exists_exhaustiveDecider`), instead of building the sketch's replay loop over the
   interpreter core? *Recommendation: yes.* The derivation is proved; `E` is TM-intrinsic and
   reusable; it removes `BF`'s per-replay reset of an interpreter with per-code setup.
3. **Interpret ND codes through their replay machine** (option (c) of §3.2, H2 unchanged at
   `k = 3`, with a per-code primitive recursive re-serialization)? The alternatives are a
   choice-indexed H2 or a dispatcher over two embedded H2 copies. *Recommendation: (c).*
4. **The step-clocked runner as H3's clock, designed once with B6's three-exit runner** (one
   statement phase)? And correct the "quadratic `clockTM`" records (§7)? *Recommendation:
   yes to both.* Also move `clockTM`'s 12.2c re-derivation target from §12.7's counter loop to
   this runner.
5. **UN's input: the bounded window copy plus an input-locality lemma** (no new device), or the
   in-place suffix device now? *Recommendation: the window copy for C1.* The suffix device
   stays with U-1, which needs it for the deadline-free `universal`.

---

## 7. Record corrections found while reading (VERIFIED)

1. **Plan §4e's C1 row** (`AroraBarakChapters3-4Plan.md:844`) and the "consequences" line
   (`:928-929`) still list `exists_effectiveNDMachineCode` as blocked. It is proved
   (`NDCodes.lean:258-268`; fills-4, `audits/fills-4-integration.md:12,37-39`). Group C's C1
   count is 6, not 7.
2. **Design §12.7** (`machine-library-design.md:987`) and **plan item 12**
   (`AroraBarakChapters3-4Plan.md:591-595`) call `TimeHierarchy/ClockMachine.lean`'s `clockTM`
   "quadratic". Its specification is linear: `tK + 4|s| + |x| + 4·val(s) + 6`
   (`ClockLoop.lean:345-347`). The quadratic bound belongs to `Turing.timed_universal`,
   `C·(t + 1)²` (`Universal.lean:2794-2802`). Two consequences:
   - **The re-derivation target.** `clockTM` fuses one decrement per *step* of an arbitrary
     machine, so it re-derives on the step-clocked runner (§3.3), not on the round-based
     counter loop.
   - **A docstring error.** `NTimeHierarchy.lean` attributes the quadratic to `clockTM`: "not
     the deterministic `clockTM` re-scan, whose `C·(t+1)²` is exactly what decision CH34-Q8
     forbids" (`:110`, also `:51`). That bound is `timed_universal`'s. This is a comment-only
     fix.
3. **SC-3 has no `backlog.md` entry.** It lives only in design §12.7 (`:1108-1111`) and plan
   §4e. If question 1 is accepted, close it there with a pointer to §3.1.
4. **Design §12.8's consumer tables still route `PATH_mem_NL` through SC-3** (`:1424`,
   `:1934`). C2 moved to programs (§16b item 4), so the reference is stale.

---

## Appendix A. `C1HostsDraft.lean` inventory

Elaborated with `tools/leanelab.sh wt-c1 oleans-f7`: **0 errors, 5 `sorry` warnings**
(`c1/elaboration.log`). Names were checked for clashes against the tip by `grep` (none).

| § | Declaration | Status |
|---|---|---|
| 1 | `NDTM.stepWith_mapState_of_agreeOn`, `NDTM.runWith_mapState_of_agreeOn` | proved |
| 1 | `NDTM.runWith_mapState_of_agreeOn_det`, `NDTM.runWith_eq_fixChoice_runFrom` | proved |
| 1 | `NDTM.phaseHostND` (def), `NDTM.phaseHostND_fixChoice` (`rfl`), `NDTM.phaseHostND_run` | proved |
| 1 | `NDTM.relabelState` (def), `NDTM.relabelState_runWith` | proved |
| 2 | `NDTM.replayTM`, `NDTM.withChoiceTape` (defs), `NDTM.replayTM_runFrom` | proved |
| 3 | `NDWriterState`, `ndWriterTM` (defs) | — |
| 3 | `ndWriterTM_run_block` | sorry |
| 4 | `clockCfg` (def), `exists_stepClockTM` (existential in the draft; the landed row names the machine) | sorry |
| 5 | `FinNDTM.exists_exhaustiveDecider` | sorry |
| 5 | `ndAcceptsWithin_decider_of_universal` (statement 2 from statement 1 and `E`) | proved |
| 6 | `CodeNDTM.serialize_eq_tableBitsK` | proved |
| 6 | `exists_replayCanonizer` | sorry |
| 7 | `exists_ndInterpreterCore` (`R`, with the prefix-form time clause) | sorry |
