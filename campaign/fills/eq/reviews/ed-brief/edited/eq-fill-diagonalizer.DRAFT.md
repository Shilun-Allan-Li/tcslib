# Ch3–4 fill campaign — E-D, the lazy diagonalizer (`Turing.NTimeDiag.exists_diagonalizer`, `Diagonalization/NTimeDiagonalizer.lean`)

> **DRAFT** (maintainer, 2026-11-04), drafted against PR #176 (E-Q cont1's landing; gate 87
> passed, 2026-11-04; it merges with the campaign merged in, after `replay-leqc2`). Its owned blob
> `852931eb9347377fcd2e4e3c1e754462b236c1ad` is the same at `cecd76a0`, at `029f3aa9` (the
> pre-ship's tree) and at `f69b86b9`. Issues after #176 merges; ⟨…⟩ marks what the pre-ship fills
> in at the issue commit (line numbers, counts, probes). **Agent: Claude** (user, 2026-11-04).
>
> **Maintainer's landing item (not the fill's):** gate 87's finding 2, ruled 2026-11-04: in E-D's
> landing PR, `qy_call_bound`'s local `hb` becomes `have hb := Turing.length_bits_le_self (f a)`
> (ledger NB-1). E-D's fill gate covers it. The brief keeps `qy_call_bound` frozen for the fill.

> **A single fill** (addendum v2.6, Parts 1 and 2; Part 3, the megafill, does not apply, except
> its one-Lean rule and its no-stop rule, items 5 and 7, which "Environment and verification"
> restates). Deliver a checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement**: the C1-E statement gate (gate 39, round 2,
    `campaign/gates/39-ntime-diag-statements/`);
  - **E-Q, landed and proved** (PR #173, gate 83; PR #176, gate 87): `exists_queryTM` and its
    private leaves in your file, among them the framed length comparison `qyCmpTM` (`qy_cmp_run`),
    the repeating emitter `qyEmitTM` (`qy_emit_run`), the writer word `qy_writer_word`, the clocked
    install call (`QyClockSpec`, `qy_clocked_call`), the hosted-phase segments (`qy_hosted*`) and
    the normal-form wrappers of the rows, calls, expansion and embedding that E-Q's machine is
    built from (listed under "Cited infrastructure"). Same-file privates are citable;
  - **the guess-then-run host** `Turing.guessRunTM` (`Build/NDHost`) with `guessRunTM_haltsWithin`
    and `guessRunTM_accepts_iff`; **the interpreter core** `Turing.exists_ndInterpreterCore`
    (`NDCodeSimulator`); **the step clock** `Turing.exists_stepClockTMVia` (`Build/StepClock`);
    **the virtual-input host** `Turing.vhostSilentTM` and **the capture wrapper**
    `Turing.embedSilentTM` (`Build/VirtualInput`, `Build/Embed`); the input call
    `Turing.FinTM.exists_inputCallTM`; `Turing.expandTM_run_ofCfg`; the pair extractors;
    `Complexity.timeConstructible_iff` (A1);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**), and the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/eq/inputs/eq-fill-diagonalizer/`): the import probe
    `EDImportProbe.lean.txt`, the route probe `EDRouteProbe.lean.txt` with its seal controls
    `EDSealControl_{unsealed,sealed}.lean.txt`, the duplication probe `EDDupProbe.lean.txt`, the
    import overlay `NTimeDiagonalizerOverlay.lean.txt` and the screen population; the order list `campaign/fills/eq/orders/eq-fill-diagonalizer.txt`, the base sorry
    set, the screen base and the pre-ship log (`campaign/fills/eq/logs/eq-fill-diagonalizer-*`). The
    route's design note is `campaign/items/c1/c1e/ED-route-design.md`, **with its revision of
    2026-11-04** (after E-Q cont1).
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule
  (E-RES). Fetch the cache for your roots only (34 Mathlib roots, `campaign/fills/eq/orders/eq-fill-diagonalizer-roots.txt`); never run the unfiltered
  `lake exe cache get`. If Lean cannot start, follow Part 2 exactly. **If Lean never runs, do not
  draft proofs blind**: deliver the environment report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/eq-diagonalizer @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
  # must print ⟨the blob at the issue commit⟩
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-eq-diagonalizer.zip`, with
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle whose only prerequisite is your base, the environment logs (`evidence/logs/`), the
  bootstrap and final sweep logs with **each module's time and maximum memory**, the axiom log, the
  seal test's source, its controls and both outputs, both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-eq-diagonalizer-cp<N>.zip` (`N` 1 to 8). Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign's tree after #176** (E-Q cont1). Lines in this brief
  are those of your base's tree, where `NTimeDiagonalizer.lean` is 5,432 lines (22 public, 214 private
  declarations).
- **The overlay is your first edit** (region (a)): add, after the `Build/WordTests` import, exactly
  `import TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `import TCSlib.Complexity.TuringMachine.NDCodeSimulator` and
  `import TCSlib.Complexity.TuringMachine.Build.VirtualInput` (13 modules join the closure; no
  cycle). The pre-ship elaborated the file with them: E-Q's proofs unchanged, exactly the target's
  sorry warning (`NTimeDiagonalizerOverlay.lean.txt`).
- **In flight:** ⟨at the issue commit⟩.

## Parallel batches this round

None in `NTimeDiagonalizer.lean`. `NTimeHierarchy` imports your file and cites only the target's
statement, which is frozen; `Complexity.ntime_hierarchy` is proved from it. NF
(`ClassNP/NDNormalForm`) may be running; it never touches your file.

## What this is

**The lazy diagonalizer** ([AB09, proof of Theorem 3.2 and Figure 3.1]). For time-constructible `f`,
`g`, an effective scheme `c` and an exponential-time decider of the coded machines' bounded
acceptance (`hBF`), a nondeterministic machine `D` and a uniform `K` with: every branch of `D` on
every input halts within `K · (g |x| + 1)`; per code `α` a constant `C` such that, on `1ⁿ` with
`n ≥ 3` in a stage of `α`, in the middle `D` accepts `1ⁿ` iff (up to the stated slack) the coded
machine accepts `1^{n + 1}`, and at the top `D` accepts `1ⁿ` iff the coded machine does **not**
accept the stage's bottom `1^{ℓᵢ + 1}` within `T* = budget f ℓᵢ` (the statement, line 5406).

**Where it stands.** The body is `sorry`. Every host is proved, and E-Q's query is proved in your
file. **Proved modulo, exactly:** none. **A complete delivery has no `sorryAx` in the target.**

**Read first:** the route note with its revision (`ED-route-design.md`); the target's docstring
(lines 5346–5405), whose sketch this brief refines; `Build/NDHost.lean`'s `guessRunTM` family
(its docstrings name the setup hypotheses); E-Q's leaves named above and under "Cited
infrastructure", with their preconditions; the framed rows' delimiter hypotheses;
`exists_ndInterpreterCore`'s statement; `Build/VirtualInput.lean`'s header and `vhostCfg`.

## Owned regions and targets (modify these and nothing else)

`TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean`:
- **(a)** the imports: add exactly the overlay's three;
- **(b)** new private declarations after `exists_queryTM`'s proof (which ends at line 5344) and
  before `exists_diagonalizer`'s docstring (line 5346), in sections of your own. Every new declaration
  has a docstring, and every proof over 20 lines a literal `**Proof sketch.**` (`policy.md` §3);
  docstrings are public-facing (no campaign labels, dates or session narrative; provenance in
  `REPORT.md`); a hand-built machine's docstring says which public row it is not;
- **(c)** the target's body (line 5430, `sorry`);
- **(d)** the status text: the module docstring's line 70 ("(sorried; C1-E's second fill)"), and
  in the target's docstring the labels "(C1-E; …)", "the P3.3 gate's round 2" and "(the statement
  gate, finding 1)". Rewrite those labels in place as public-facing text (the docstring's other
  campaign references belong to the deferred cleanup); propose an `**Implementation.**` paragraph
  in `REPORT.md`, which the maintainer lands.

**Target:** `Turing.NTimeDiag.exists_diagonalizer` (line 5406), its statement frozen. E-Q's
declarations and every other statement are frozen too.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **`D` is `Turing.guessRunTM P pexit j Q qentry acc rej`**, bundled as a `FinNDTM`: one guessed
  block of `m = g n + 1 + L` cells (`L = |bits (g n)|`): its first `g n` bits the stream `s`, then
  one separator cell, then the budget word `w_b` of `L` bits. **Halting** is
  `guessRunTM_haltsWithin`; **acceptance** is `guessRunTM_accepts_iff` (not
  `guessRunTM_silent_spec`: your setup is not clean, it keeps the query word and the counter).
  Never compose `phaseHostND` yourself, and never re-prove a writer, handoff or acceptance lemma.
- **No published row splits a contiguous word.** Every framed row that reads a word from a head
  (`copyMapTM_run_ofCfg`, `transferMapTM_run_ofCfg`, `clearTM_run_ofCfg`, the counters of
  `expandTM_run_ofCfg` and of the step clock) demands blanks at the word's relative positions `-1`
  and `|w|`, and no published row writes a blank at one cell. The guessed block is nonblank
  throughout (`guessRunTM`'s `hblock`), and the query's tail has the flag before it, while the
  extractor's argument and `vhostSilentTM`'s buffer must each be exactly `FinTM.bufferTape` of
  their word (`vhostCfg`). So the route has **one own leaf**, `dzTakeTM` (⟨the maintainer's
  decision, review F1⟩): in one step, read the cell under a tape's head, **write a blank there**,
  step right, and enter `got o` with the symbol read. Its step lemma is its own (`qy_step` covers
  only steps that write nothing; rule 10's own-leaf clause), and its docstring names the missing
  row. It reads the flag, splits the block at the separator and reads the top's captured bit.
- **`P`, the deterministic setup:** the query call on the native input (released;
  `exists_queryTM`'s machine through `FinTM.exists_inputCallTM`; `qy_inputSpec`, `qy_callHost`);
  `g`'s witness call (released; through `timeConstructible_iff`), giving `bits (g n)`, and copies
  of it (`qy_copy`: each expansion consumes its counter, and the clock patches its own); the
  **block** on tape `j`: `1^{g n}`, one more `true` (the separator) and a copy of `bits (g n)`, for
  example `qy_expandHost` twice (the second with the counter `[true]`, written by `qy_writeConst`)
  and `qy_copy`, rewound to cell `0` (`qy_rewind`), blank on both sides; the **ruler** `1^{g n}`
  on its own tape (`qy_expandHost`, rewound); the clock's counter `bits (g n)` on its own tape; and
  `1^{n + 1}`, by the input call of the published `FinTM.computesFunInTime_prepend [true]`. Its
  first exit `TP ≤ P₀ · (g n + 1)`, uniform.
- **`Q`, the deterministic run**, a phase host (`Turing.phaseHostTM`) over:
  1. **the flag:** `dzTakeTM` on the query tape: `got none` (`n < 3` or not unary: the query is
     `[]`) → `rej`; `got (some true)` → the top; `got (some false)` → the middle. The flag's cell
     is now blank: the tail's left delimiter;
  2. **the tail:** copy it from the query tape's cell `1` onto a fresh buffer at cell `0`
     (`copyMapTM_run_ofCfg` directly: `qy_copy` assumes the word at cell `0`);
  3. **the middle's preparation** (route note, revision), from published rows, E-Q's leaves and
     `dzTakeTM`:
     - **the split:** skip back over the empty word on tape `j` (`skipBackTM_run_ofCfg`: its head
       from `0` to `-1`), then the lockstep walk `walkTM_run_ofCfg` with the ruler as its source,
       moving the ruler's head and tape `j`'s: tape `j`'s head lands on the separator, cell
       `g n`. `dzTakeTM` blanks it and steps right, so `w_b` is delimited; `transferMapTM_run_ofCfg`
       moves `w_b` onto a fresh tape at cell `0` and blanks its cells, which leaves tape `j`
       exactly `bufferTape s`; skip back over `s` (`skipBackTM_run_ofCfg`) returns its head to
       `0`;
     - **the test:** expand `w_b` to `1^b` (`qy_expandHost`: `expandTM_run_ofCfg` reads any
       little-endian word, top zeros included), rewind it, and compare `1^b` with `s` by
       `qyCmpTM`: `gt` → `rej`;
     - **the normalization** to `bits b`: the install call of `FinTM.computesFunInTime_lengthBits`
       on `1^b` (`FinTM.exists_installCallTM`; `qy_installSpec`, `qy_callHost`);
     - **`α`:** one install call, on the tail's buffer, of the function-level composite
       `FinTM.computesFunInTime_comp FinTM.pairExtractTM_fst FinTM.pairExtractTM_snd`, the second
       component of the first component (on `⟨⟨bits (g n), α⟩, 1^{n + 1}⟩` it is `α`, by
       `pairDecode_pairEncode`). Not `pairExtractTM false true` alone, whose output on the tail
       is `1^{n + 1}`, and not `prefixCanon_pairExtract_halt`, a native-input run that halts;
     - **the core's input** `⟨⟨bits b, α⟩, 1^{n + 1}⟩`, written onto a capture tape by three
       `qyEmitTM` emissions (`bits b`, each bit four times, then `[false, false, true, true]`;
       `α` doubled, then `[false, true]`; `1^{n + 1}` from `P`) **run under the capture wrapper
       `embedSilentTM`**, which records every emission and emits nothing. The word is
       `qy_writer_word`'s without its flag (take `W := α ++ [true]` and cancel the flag: no
       second word lemma). Rewind the capture tape to cell `0`, the virtual input's position;
  4. **the middle's run:** the step clock (counter `bits (g n)`, allowance `g n`) over
     `vhostSilentTM R`, `R` the interpreter core, stopping at its `accept` or `reject`, **embedded
     into `D`'s tapes** (`embedEmitTM`, `qy_embed`): the core's stream tape on tape `j`
     (`bufferTape s`, head `0`), the virtual input's buffer on the capture tape just rewound, the
     core's other tapes and `vhostSilentTM`'s capture tape on tapes blank there, the counter on its
     copy. `finish accept` → `acc`; `finish reject` and `timeout` → `rej`;
  5. **the top's run:** the same composition over `vhostSilentTM BF` on the tail's buffer
     `⟨⟨bits T*, α⟩, 1^{ℓᵢ + 1}⟩` (`query_eq`'s top branch, exactly `hBF`'s input shape), stopping
     at `BF`'s halt. The captured output sits on `vhostSilentTM`'s capture tape with its head
     after it (`embedSilentCfg_cap`): rewind it and read cell `0` with `dzTakeTM`: `false` →
     `acc`; anything else, or a `timeout`, → `rej`.

  **State the clocked, hosted run once**, generic in the hosted machine and its stop set (the
  step clock over `vhostSilentTM`, embedded: a composition of two registered hosts, not a new
  host, and a promotion candidate), and use it for both runs; two copies would be a same-file
  duplicate.

  **`Q` is silent:** both simulators are hosted silently and every other phase emits nothing, so
  the run's output is empty at its verdict, as `guessRunTM_accepts_iff` requires.

### The route (binding where it names a row; the rest is the recommended shape)

**Time, uniform.** `TP + 2m + T + 11` with `m = g n + 1 + L ≤ 2 (g n + 1)` (`length_bits_le_self`)
and `T` the preparation `O(g n + 1)` (the expansion of `w_b` is at most `2 g n` cells:
`qy_two_pow_bits_le`), the clock's `5 g n + 2L + 2` and the dispatches; so `K` is uniform and
`guessRunTM_haltsWithin` gives `D.tm.HaltsWithin x (K · (g |x| + 1))` on **every** input (off unary
inputs the query is `[]` and `Q` rejects at once).

**The middle, per code `α`** (`C = max 1 (max C_R C_BF)`):
- **Completeness:** an acceptance of `1^{n + 1}` along `v`, `|v| = t'`, `C (t' + 1) ≤ g n`: take the
  stream `v` padded to `g n` bits, any separator bit, and `w_b := bits t'` padded with zeros to
  width `L`. The test
  passes, the core runs on `⟨⟨bits t', α⟩, 1^{n + 1}⟩` and accepts at `T ≤ C_R (t' + 1) ≤ g n`,
  inside the allowance (`finish accept`); `guessRunTM_accepts_iff` gives the accepting branch at the
  budget `K (g n + 1)`.
- **Soundness:** an accepting branch has a stream `s` and `b ≤ g n` whose core run accepts inside
  the allowance, so the coded machine's branch along `s.take b` halts with `[true]` (the core's
  clause): `AcceptsWithin (1^{n + 1}) b`, then `AcceptsWithin.mono` to `g n`.

**The top:** `BF` completes within `C_BF 2^{C_BF (T* + 1)} ≤ n ≤ g n`, inside the allowance, so `D`
accepts iff `BF` answers `[false]`; every stream gives the same verdict.

**The interpreter's prefix clause is not used** (its `|x|` term carries the per-code constant, which
the uniform `K` cannot absorb when `g n = n`).

**Edge cases that must stay true:** `n ≤ 2` and non-unary inputs (the query is `[]`: `rej`); a
budget word above `g n` (`qyCmpTM`'s `gt`: `rej`); `b = 0` (`1^0` is empty: `qyCmpTM` and the
`lengthBits` call on the empty word); a stream shorter than an acceptance (the core rejects or times
out: `rej`); `BF` halting with a word other than `[false]` or `[true]` (`rej`); the clock's
`timeout` in either run (`rej`); and `g n = 0` (only at `n = 0`, for the halting clause): the
block is the separator alone, the ruler, `w_b` and every counter are empty, the walk moves one
cell, and the clock's allowance is `0`.

## Gate guidance (binding)

- **Gate 39** (the C1-E statement gate, round 2): the uniform `K`; the per-code `C`; the top's
  premise `C 2^{C (T* + 1)} ≤ n`; the middle's two directions with their slack.
- **The route note and its revision:** one guessed block through `guessRunTM` (ruled); the binary
  budget, tested and normalized (ruled); E-Q's leaves cited, never copied.

## Cited infrastructure (public and proved at the issue commit; `EDImportProbe.lean.txt`, 59 checks)

Extend a copy of the import probe by every name you cite beyond it, and run it.

- **The host** (`Build/NDHost`): `Turing.guessRunTM`, `Turing.guessRunCfg` with its five field
  equations (`guessRunCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`),
  `Turing.guessRunTM_haltsWithin`, `Turing.guessRunTM_accepts_iff`; for reference only,
  `Turing.guessRunTM_silent_spec` and `Turing.streamStartCfg` (the clean-setup form, which does not
  apply: your setup keeps the query word and the counter).
- **The core** (`NDCodeSimulator`): `Turing.exists_ndInterpreterCore` (its total-time clause
  `T ≤ C (t + 1)` and its verdict clause; not its prefix clause).
- **The clock** (`Build/StepClock`): `Turing.exists_stepClockTMVia` (`exists_stepClockTM` is its
  plain form).
- **The hosts of a machine** (`Build/VirtualInput`, `Build/Embed`): `Turing.vhostSilentTM`,
  `Turing.vhostSilentCfg` (`vhostSilentCfg_eq`, the `vhostCfg_*` fields, `vhostBuffer_eq`,
  `vhostBank_eq`, `vhostCap_eq`), `Turing.vhostSilentTM_runFrom` with `FinTM.VirtualTag_iff` for
  its arrival tag; `Turing.embedSilentTM`, `Turing.embedSilentCfg` (`embedSilentCfg_cap`,
  `_selected_tape`, `_selected_pos`, `_unselected`), `Turing.embedSilentTM_runFrom`; the forwarding
  embedding `Turing.embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitCfg_eq`; the clock's layout
  through `clockCfg_*` and `wordPatch_*`, its stops through `Cfg.stopped_iff`.
- **The calls:** `Turing.FinTM.exists_inputCallTM`, `Turing.FinTM.exists_installCallTM`,
  `Turing.seamReleaseTM` (`seamReleaseTM_runFrom_pos`), and their function-level rows:
  `Turing.FinTM.computesFunInTime_lengthBits`, `Turing.FinTM.computesFunInTime_prepend`,
  `Turing.FinTM.computesFunInTime_comp` with `Turing.FinTM.pairExtractTM_fst` and
  `Turing.FinTM.pairExtractTM_snd` (`Turing.pairDecode_pairEncode` reads the result).
- **The rows** (framed `_ofCfg` forms; each needs blanks at its word's relative positions `-1`
  and `|w|`): `Turing.expandTM`, `Turing.expandTM_run_ofCfg` (it reads the word by
  `Nat.ofDigits 2`, top zeros included), `copyMapTM_run_ofCfg`, `transferMapTM_run_ofCfg`,
  `walkTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `rewindTM_run_ofCfg`; the phase host
  `Turing.phaseHostTM` (`phaseHostTM_run`, `phaseHostTM_run_le`, `phaseHostTM_q₀`;
  `initCfg_ofWords`).
- **E-Q's normal-form wrappers, in your file** (cite them; a second one is a copy): `qyC`,
  `qy_step`, `qy_hosted'`, `qy_hosted`, `qy_hosted_last`, `qy_hosted_run`, `qy_hosted_halt`,
  `qy_guard_of_cut`, `qy_patch_end`; `qy_copy`, `qy_copy_over`, `qy_transfer`, `qy_clear`,
  `qy_writeConst`, `qy_rewind` (each with its word at cell `0` under a head at `0`, or appended at
  a head at the word's end: an off-origin step uses the framed row directly); `qy_embed_gen`,
  `qy_embed`, `qy_embed_state`; `qy_call`, `qy_callHost`, `QySpec`, `QyInSpec`, `qy_installSpec`,
  `qy_inputSpec`; `qy_expand_start`, `qy_expandHost`; `qy_emit_run`, `qy_emit_stop`,
  `qy_emit_halt`; `qy_bits_val`, `qy_two_pow_bits_le`, `qy_blank_bank`, `qy_arg_bank`.
- **The readings:** `Complexity.timeConstructible_iff` (its first conjunct gives `n ≤ g n`, the top's
  last step); `Turing.FinNDTM.acceptsWithin_iff`, `Turing.FinNDTM.AcceptsWithin.mono`;
  `Turing.NDTM.HaltsWithin`; `Turing.pairEncode_eq`; `Turing.counterValue_eq`,
  `Turing.counterValue_bits`; `Turing.length_bits_le_self`; `Turing.MultiTapeTM.step_of_some`; and
  E-Q's public results in your file (`query_eq`, `query_of_not_guard`, `budget_eq`, the ladder and
  stage lemmas, `stageCode_eq`).

**The route probe** (`EDRouteProbe.lean.txt`, sealed over 11 definitions with the four `@[simp]`
TCSlib definitions erased; its 17 controls in `EDSealControl_*.lean.txt`) proves the route's
arithmetic and readings from these: the block's width `g n + |bits (g n)| ≤ 2 (g n + 1)` (with
the separator cell, `g n + 1 + |bits (g n)| ≤ 2 (g n + 1)` follows the same way); a budget
word of that width has value at most `2 g n` (so its expansion is `O(g n)`); a budget `t' ≤ g n`
fits the width, and its zero-padded word has value `t'`; an accepting word of length `t'`, padded to
`g n`, is the stream's first `t'` bits; soundness (acceptance along `s.take b`, `b ≤ |s| = g n`, is
acceptance within `g n`); the middle's and the top's allowance arithmetic; the uniform constant
`(P₀ + P₁ + 15) (g n + 1)`; and the query word's three shapes (top, middle, off-stage). Its lemmas
are a probe record: re-prove what you need under your prefix, citing the same published lemmas.
**The duplication probe** (`EDDupProbe.lean.txt`): `exact?` closes only `|bits G| ≤ G`
(`length_bits_le_self`) and `counterValue (bits t) = t` (`counterValue_bits`); `2 ^ |bits G| ≤
2 G + 1` is your file's `qy_two_pow_bits_le` (cite it).
**The review probe** (⟨staged as `RVRouteRows.lean.txt` and `RVOverlayAx.lean.txt`⟩) proves from
published rows the split's obstruction (`rv_no_left_delim`), the positioning (`rv_skipBack_empty`,
`rv_walk_to_boundary`), `α` by the composite (`rv_alpha_row`, `rv_alpha_value`), `1^{n + 1}` by
the prepend row (`rv_tail_ones`) and the flagless word from `qy_writer_word` (`rv_core_word`), and
prints every row cited here free of `sorryAx`.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d). List every new declaration with its role.
2. **Statement freeze** over the target, `exists_queryTM` and every landed declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. The top does not depend on the middle's preparation.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the base's and the overlay's three; add none.
7. **One proof per shared argument.** Never write a second host, writer, clock, counter, call,
   seam, embedding, capture, comparison, emitter or rewind. **E-Q's leaves are yours to cite, not
   to copy**: a second length comparison, emitter, word lemma or normal-form wrapper (the list
   under "Cited infrastructure") in the file is a copy. Your own leaf is `dzTakeTM` (with the
   phase hosts' redirects) and nothing else; the two clocked, hosted runs are one lemma. Never
   re-walk
   `NTimeHierarchy`'s `exists_timed_universal_NDTM`/`un_setup` (the same guess-then-run pattern
   with a clean setup: cite the host's lemmas), `ExhaustiveReplay`'s `xr_` replays, or `NDHost`'s
   `wr_`/`gr_` privates.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts.
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).** As in E-Q's briefs: never unfold
    another file's definition, and no definitional closure; read `TimeConstructible` through
    `timeConstructible_iff`, `ComputesFunInTime`/`ComputesInTime` through their `_iff` readings,
    `pairEncode` through `pairEncode_eq`, the transports and hosts through their published
    equations, and `guessRunTM` only through its lemmas. Core and Mathlib definitions may reduce in
    `rfl`, `decide` or `show`, never passed to `simp`, `rw` or `unfold`. Own leaves: unfold `step`
    and `Action.apply` by `unfold`/`rw`/`simp only` (never `show`/`change`/`rfl`), preferring
    `MultiTapeTM.step_of_some` and the `Action.apply_*` equations. **Self-check by both methods:**
    a seal test (every other-file TCSlib definition your code reaches: at least the route probe's
    11 and, as in E-Q cont1's rule 10, `FinTM.ComputesFunInTime`, `FinTM.ComputesInTime`,
    `MultiTapeTM.runFrom`, `MultiTapeTM.initCfg`, `Cfg.ofWords`, `stateWord`, `clockCfg`,
    `wordPatch`, `counterLoopCfg`, `expandTM`, `copyMapTM`, `transferMapTM`, `walkTM`,
    `skipBackTM`, `rewindTM`, `writeConstTM`, `seamReleaseTM`, `phaseHostTM`, `Cfg.mapState`,
    `Cfg.Stopped`, `embedEmitTM`, `embedSilentTM`, `embedEmitCfg`, `embedSilentCfg`,
    `vhostSilentTM`, `vhostSilentCfg`, `vhostCfg`, `FinTM.VirtualTag`, `guessRunTM`, `guessRunCfg`,
    `FinTM.bufferTape`, `pairDecode`; the four `@[simp]` TCSlib definitions erased; a reducible
    `abbrev` read through its body) **with controls**, and an inspection table; ship the raw
    outputs. The readings are E-Q cont1's: `clockCfg` through `clockCfg_*`, `wordPatch` through
    `wordPatch_of_mem`/`_of_not_mem`/`_append`, the R1 transports through their equations and
    `embedEmitCfg_eq`, `counterLoopCfg` through `counter_cfg_eq`, a released call through
    `seamReleaseTM_runFrom_pos`, `Cfg.ofWords`/`stateWord` through their equations, and
    `FinTM.VirtualTag` through `VirtualTag_iff`.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows; use the framed `_ofCfg`
    forms. Cite no private declaration of another file. Keep your new privates under the `dz_`
    prefix (`Dz`/`dz` for types and definitions; unused in the tree). A `private inductive` with
    `deriving` gets public instance names (`instDecidableEqDz…`; `workflow.md` §4, counting public
    names): check them against the tree and every open PR, or write `private instance`s.

### Checkpoints (for a partial; ground rule 9)

1. **The overlay and `P`** as a contract (the block with its separator, the ruler, the counters,
   `1^{n + 1}`), with its uniform bound.
2. **`dzTakeTM`, the flag, the tail's copy and `Q`'s dispatch** (the phase host's redirects).
3. **The split, the budget's test and normalization** (`skipBackTM`, `walkTM`, `dzTakeTM`,
   `transferMapTM`; `qy_expandHost`, `qyCmpTM`, the `lengthBits` call).
4. **`α` and the rewrite** (the composite's install call; the three emissions under
   `embedSilentTM`; the capture rewound).
5. **The clocked, hosted run** (one lemma, generic in the hosted machine), its two uses and their
   verdict readers.
6. **`Q`, `D` and the time bound `K`** (`guessRunTM_haltsWithin`).
7. **The middle and the top** (`guessRunTM_accepts_iff`, the core's clause, `BF`).
8. **The target.**

Each may land alone. **Add no new admission. One checkpoint, one commit, one zip, delivered at
once.**

## Duplication governance (binding)

As in E-Q's briefs: both v3 screens on frozen copies, one at a time under `nice -n 10`; the
semantic search for every new private (in the tree, on every open PR branch, by name and statement,
and by an `exact?` or `apply?` probe), listed per private in `REPORT.md`. **The population** is
38 files (`screen-population.txt`): your file; the files the route cites; the known hazards
(`NTimeHierarchy`, `ExhaustiveReplay`, `NDCodeSimulator`, `CodeSimulator`, `Build/SeamLayout`).
**The base** is `campaign/fills/eq/logs/eq-fill-diagonalizer-screen-base.txt`: ⟨…⟩. A pair at 90%
or more is a copy; every new pair gets one disposition (idiom; re-derivation of a published lemma:
cite it instead; of another file's private: keep yours and request a promotion), and `REPORT.md`
carries "new copies: none" or lists each pair. **Known hazards:** `NTimeHierarchy`'s guess-then-run
setup; E-Q's own leaves (cite them); the one-step identity (ledger RO-1); the `Cfg.mapState` idiom.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only**; **never `lake build`**, never
  the unfiltered `lake exe cache get`; `scripts/lean_check_tree.sh` for every check, one Lean
  process at a time (a screen may run beside one). **A process deviation never ends the item.**
  The cache tool's own compilation inside `lake exe cache get` is not a deviation (E-SERIAL).
- **Budget:** E-Q cont1's last Claude host (4 CPUs) ran 2–3× slower than the maintainer's: expect
  about 20 minutes for the bootstrap and each screen 2–3× the screen base's time; reserve about
  an hour for the finishing sequence.
- **Bootstrap** from the order list (84 modules), logging each module's time and maximum memory.
  **The base sorry set** has 19 declarations in 9 modules (static count,
  `campaign/fills/eq/logs/eq-fill-diagonalizer-base-sorries.txt`); yours is the target's one.
- **Final checks:** your file with zero errors and no sorry warning (a partial: the target's only);
  every other module the base's; the import probe re-run; after every proof edit, the order list's
  tail from your module on.
- **Axiom prints** for the target and every new private: within `[propext, Classical.choice,
  Quot.sound]`.
- **Lint:** `campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL (base: 0 FAIL, 3
  WARN over 5 files; the file is 5,432 lines at the base and 5,435 with the overlay), and
  `style_lint.py` on your file. No new line over 100 characters; the file's size WARN is
  expected.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target (the list in
`campaign/fills/eq/logs/eq-fill-diagonalizer-base-sorries.txt`).

## REPORT.md checklist

- [ ] The preflight, the roots and the cache fetch (with the logs), the bootstrap, the base blob.
- [ ] The overlay only; nothing outside regions (a)–(d); E-Q's text untouched.
- [ ] The checkpoints reached (1–8), one zip each; the base hash and the ancestor check.
- [ ] Every new declaration with its role; `P`'s and `Q`'s phases and tapes, with the injection
      of each embedded machine (the clocked, hosted runs' tape plan); each call's release; each
      E-Q leaf cited and where; `dzTakeTM`'s docstring naming the missing row.
- [ ] `K`, term by term; the per-code `C`; each edge case with the lemma that covers it.
- [ ] Promotion candidates and escalations, or "none"; the proposed `**Implementation.**`
      paragraph.
- [ ] Rule 10 (the citations outside your file, the probe re-run, **the seal test with its controls
      and both raw outputs**, the inspection table); rule 11.
- [ ] Duplication: both v3 screens, every new pair justified, the semantic search per private,
      "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **The simps field equations are pointwise**: `funext` before `rw`.
- **Every framed row needs both delimiters** (relative positions `-1` and `|w|`): a word inside a
  nonblank block cannot be copied, moved, cleared or counted until a blank is written before it
  (`dzTakeTM`). E-Q's wrappers assume the word at cell `0` under a head at `0`.
- **`vhostSilentTM`'s buffer is exactly `FinTM.bufferTape y`**, its head at the virtual input
  position minus one: the virtual input sits alone on its tape from cell `0`, its head at `0`
  (input position `1`), with the initial tag `true` (`FinTM.VirtualTag_iff`).
- **The install call's start is `Cfg.ofWords (input := x) entry (stateWord C.k arg)`**: every tape
  of the call blank except tape `0`, all heads at `0`, the input head at `1`. Embed it on tapes
  blank there (`qy_callHost`).
- **`P` starts at its initial configuration** (`guessRunTM`'s lemmas take
  `P.runFrom (P.initCfg z)`): the phase host's initial state through `phaseHostTM_q₀`, the blank
  seam through `initCfg_ofWords`. The calls' and the clock's times are existential: fix them before
  the ledger.
- **`FinTM.lengthBitsTM_computes` is sorried** (the base set): the normalization cites
  `FinTM.computesFunInTime_lengthBits`, whose axioms are the standard three.
- **A call's entry may equal its exit**: run every call released (`seamReleaseTM`), as E-Q's
  review F1 found.
- **The clock's stop state** and first-stop reasoning: E-Q's `qy_clocked_call` and `QyClockSpec` are
  the model for an install call; for a hosted machine, state the clock's clauses afresh over
  `vhostSilentTM`'s run lemma.
- **No core or Mathlib definition is reduced outside `rfl`, `decide` or `show`.** `omega` with
  products as atoms (`ring` first). The linter needs a literal "Proof sketch" before every
  `sorry` (partial only).
