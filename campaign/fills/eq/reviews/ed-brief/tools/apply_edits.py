"""Apply the review's proposed edits to the E-D draft, every replacement asserted.
usage: python3 -I apply_edits.py <draft.md>   (edits in place)"""
import sys

p = sys.argv[1]
s = open(p, encoding='utf-8').read()


def rep(old, new):
    global s
    n = s.count(old)
    assert n == 1, (n, old[:120])
    s = s.replace(old, new)


def rep_between(start, end, new):
    """Replace the text from `start` (inclusive) through `end` (inclusive)."""
    global s
    assert s.count(start) == 1, start[:80]
    assert s.count(end) == 1, end[:80]
    i = s.index(start)
    j = s.index(end) + len(end)
    assert i < j
    s = s[:i] + new + s[j:]


# F10: the header's commit references
rep("""> **DRAFT** (maintainer, 2026-11-04), drafted against PR #176's head `cecd76a0` (E-Q cont1's
> landing; gate 87 passed, 2026-11-04; it merges with the campaign merged in, after
> `replay-leqc2`). Issues after #176 merges; ⟨…⟩ marks what the pre-ship fills in at the issue
> commit (line numbers, counts, probes). **Agent: Claude** (user, 2026-11-04).""",
"""> **DRAFT** (maintainer, 2026-11-04), drafted against PR #176 (E-Q cont1's landing; gate 87
> passed, 2026-11-04; it merges with the campaign merged in, after `replay-leqc2`). Its owned blob
> `852931eb9347377fcd2e4e3c1e754462b236c1ad` is the same at `cecd76a0`, at `029f3aa9` (the
> pre-ship's tree) and at `f69b86b9`. Issues after #176 merges; ⟨…⟩ marks what the pre-ship fills
> in at the issue commit (line numbers, counts, probes). **Agent: Claude** (user, 2026-11-04).""")

# F3: E-Q's wrappers in the ancestor list
rep("""    install call (`QyClockSpec`, `qy_clocked_call`) and the hosted-phase segments (`qy_hosted*`).
    Same-file privates are citable;""",
"""    install call (`QyClockSpec`, `qy_clocked_call`), the hosted-phase segments (`qy_hosted*`) and
    the normal-form wrappers of the rows, calls, expansion and embedding that E-Q's machine is
    built from (listed under "Cited infrastructure"). Same-file privates are citable;""")

# F3, F1: read first
rep("""(its docstrings name the setup hypotheses); E-Q's leaves named above; `exists_ndInterpreterCore`'s
statement; `Build/VirtualInput.lean`'s header.""",
"""(its docstrings name the setup hypotheses); E-Q's leaves named above and under "Cited
infrastructure", with their preconditions; the framed rows' delimiter hypotheses;
`exists_ndInterpreterCore`'s statement; `Build/VirtualInput.lean`'s header and `vhostCfg`.""")

# F14: region (d)
rep("""  gate, finding 1)". Rewrite them as public-facing text; propose an `**Implementation.**` paragraph
  in `REPORT.md`; the maintainer lands it.""",
"""  gate, finding 1)". Rewrite those labels in place as public-facing text (the docstring's other
  campaign references belong to the deferred cleanup); propose an `**Implementation.**` paragraph
  in `REPORT.md`, which the maintainer lands.""")

# F1, F2, F4, F5, F6, F7: the hosts
rep_between("- **`D` is `Turing.guessRunTM P pexit j Q qentry acc rej`**",
            "  the run's output is empty at its verdict, as `guessRunTM_accepts_iff` requires.\n",
"""- **`D` is `Turing.guessRunTM P pexit j Q qentry acc rej`**, bundled as a `FinNDTM`: one guessed
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
""")

# F1: the time bound with the separator
rep("""**Time, uniform.** `TP + 2m + T + 11` with `m ≤ 2 (g n + 1)` and `T` the preparation
`O(g n + 1)`, the clock's `5 g n + 2L + 2` and the dispatches; so `K` is uniform and""",
"""**Time, uniform.** `TP + 2m + T + 11` with `m = g n + 1 + L ≤ 2 (g n + 1)` (`length_bits_le_self`)
and `T` the preparation `O(g n + 1)` (the expansion of `w_b` is at most `2 g n` cells:
`qy_two_pow_bits_le`), the clock's `5 g n + 2L + 2` and the dispatches; so `K` is uniform and""")

# F1: the completeness witness with the separator
rep("""  stream `v` padded to `g n` bits and `w_b := bits t'` padded with zeros to width `L`. The test""",
"""  stream `v` padded to `g n` bits, any separator bit, and `w_b := bits t'` padded with zeros to
  width `L`. The test""")

# F12: the edge case g n = 0
rep("""`timeout` in either run (`rej`).""",
"""`timeout` in either run (`rej`); and `g n = 0` (only at `n = 0`, for the halting clause): the
block is the separator alone, the ruler, `w_b` and every counter are empty, the walk moves one
cell, and the clock's allowance is `0`.""")

# F9: the cited list's heading
rep("""## Cited infrastructure (public and proved at the issue commit; `EDImportProbe.lean.txt`, 59 checks)""",
"""## Cited infrastructure (public and proved at the issue commit; `EDImportProbe.lean.txt`, 59 checks)

Extend a copy of the import probe by every name you cite beyond it, and run it.""")

# F9, F4: the hosts of a machine
rep("""- **The hosts of a machine** (`Build/VirtualInput`, `Build/Embed`): `Turing.vhostSilentTM`,
  `Turing.vhostSilentCfg`, `Turing.vhostSilentTM_runFrom`; `Turing.embedSilentTM`,
  `Turing.embedSilentCfg`, `Turing.embedSilentTM_runFrom`.""",
"""- **The hosts of a machine** (`Build/VirtualInput`, `Build/Embed`): `Turing.vhostSilentTM`,
  `Turing.vhostSilentCfg` (`vhostSilentCfg_eq`, the `vhostCfg_*` fields, `vhostBuffer_eq`,
  `vhostBank_eq`, `vhostCap_eq`), `Turing.vhostSilentTM_runFrom` with `FinTM.VirtualTag_iff` for
  its arrival tag; `Turing.embedSilentTM`, `Turing.embedSilentCfg` (`embedSilentCfg_cap`,
  `_selected_tape`, `_selected_pos`, `_unselected`), `Turing.embedSilentTM_runFrom`; the forwarding
  embedding `Turing.embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitCfg_eq`; the clock's layout
  through `clockCfg_*` and `wordPatch_*`, its stops through `Cfg.stopped_iff`.""")

# F2, F5, F9: the calls
rep("""- **The calls:** `Turing.FinTM.exists_inputCallTM`, `Turing.FinTM.exists_installCallTM`,
  `Turing.seamReleaseTM`, `Turing.FinTM.computesFunInTime_lengthBits`.""",
"""- **The calls:** `Turing.FinTM.exists_inputCallTM`, `Turing.FinTM.exists_installCallTM`,
  `Turing.seamReleaseTM` (`seamReleaseTM_runFrom_pos`), and their function-level rows:
  `Turing.FinTM.computesFunInTime_lengthBits`, `Turing.FinTM.computesFunInTime_prepend`,
  `Turing.FinTM.computesFunInTime_comp` with `Turing.FinTM.pairExtractTM_fst` and
  `Turing.FinTM.pairExtractTM_snd` (`Turing.pairDecode_pairEncode` reads the result).""")

# F1, F3, F9: the rows and E-Q's wrappers
rep("""- **The rows** (framed `_ofCfg` forms): `Turing.expandTM`, `Turing.expandTM_run_ofCfg` (it reads
  the word by `Nat.ofDigits 2`, top zeros included), `copyMapTM_run_ofCfg`,
  `transferMapTM_run_ofCfg`, `clearTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `rewindTM_run_ofCfg`;
  `Turing.FinTM.pairExtractTM`; the phase host `Turing.phaseHostTM`.""",
"""- **The rows** (framed `_ofCfg` forms; each needs blanks at its word's relative positions `-1`
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
  `qy_emit_halt`; `qy_bits_val`, `qy_two_pow_bits_le`, `qy_blank_bank`, `qy_arg_bank`.""")

# F1: the route probe's width with the separator
rep("""arithmetic and readings from these: the block's width `g n + |bits (g n)| ≤ 2 (g n + 1)`; a budget""",
"""arithmetic and readings from these: the block's width `g n + |bits (g n)| ≤ 2 (g n + 1)` (with
the separator cell, `g n + 1 + |bits (g n)| ≤ 2 (g n + 1)` follows the same way); a budget""")

# The review probe as an input
rep("""2 G + 1` is your file's `qy_two_pow_bits_le` (cite it).""",
"""2 G + 1` is your file's `qy_two_pow_bits_le` (cite it).
**The review probe** (⟨staged as `RVRouteRows.lean.txt` and `RVOverlayAx.lean.txt`⟩) proves from
published rows the split's obstruction (`rv_no_left_delim`), the positioning (`rv_skipBack_empty`,
`rv_walk_to_boundary`), `α` by the composite (`rv_alpha_row`, `rv_alpha_value`), `1^{n + 1}` by
the prepend row (`rv_tail_ones`) and the flagless word from `qy_writer_word` (`rv_core_word`), and
prints every row cited here free of `sorryAx`.""")

# F3, F4: ground rule 7
rep("""   seam, embedding, capture, comparison, emitter or rewind. **E-Q's leaves are yours to cite, not
   to copy**: a second length comparison or emitter in the file is a copy. Never re-walk""",
"""   seam, embedding, capture, comparison, emitter or rewind. **E-Q's leaves are yours to cite, not
   to copy**: a second length comparison, emitter, word lemma or normal-form wrapper (the list
   under "Cited infrastructure") in the file is a copy. Your own leaf is `dzTakeTM` (with the
   phase hosts' redirects) and nothing else; the two clocked, hosted runs are one lemma. Never
   re-walk""")

# F8: ground rule 10's readings and seal floor
rep("""    a seal test (every other-file TCSlib definition your code reaches, at least the route probe's
    11, with the four `@[simp]` TCSlib definitions erased) **with controls**, and an inspection table; ship the raw outputs.""",
"""    a seal test (every other-file TCSlib definition your code reaches: at least the route probe's
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
    `FinTM.VirtualTag` through `VirtualTag_iff`.""")

# F8: ground rule 11's derived instances
rep("""    forms. Cite no private declaration of another file. Keep your new privates under the `dz_`
    prefix (`Dz`/`dz` for types and definitions; unused in the tree).""",
"""    forms. Cite no private declaration of another file. Keep your new privates under the `dz_`
    prefix (`Dz`/`dz` for types and definitions; unused in the tree). A `private inductive` with
    `deriving` gets public instance names (`instDecidableEqDz…`; `workflow.md` §4, counting public
    names): check them against the tree and every open PR, or write `private instance`s.""")

# The checkpoints
rep("""1. **The overlay and `P`** as a contract, with its uniform bound.
2. **The flag and `Q`'s dispatch** (the one-step leaves, the phase host's redirects).
3. **The budget's test and normalization** (`expandTM`, `qyCmpTM`, the `lengthBits` call).
4. **`α` and the rewrite** (the extractor call; the three emissions under `embedSilentTM`).
5. **The two clocked, hosted runs** and their verdict readers.""",
"""1. **The overlay and `P`** as a contract (the block with its separator, the ruler, the counters,
   `1^{n + 1}`), with its uniform bound.
2. **`dzTakeTM`, the flag, the tail's copy and `Q`'s dispatch** (the phase host's redirects).
3. **The split, the budget's test and normalization** (`skipBackTM`, `walkTM`, `dzTakeTM`,
   `transferMapTM`; `qy_expandHost`, `qyCmpTM`, the `lengthBits` call).
4. **`α` and the rewrite** (the composite's install call; the three emissions under
   `embedSilentTM`; the capture rewound).
5. **The clocked, hosted run** (one lemma, generic in the hosted machine), its two uses and their
   verdict readers.""")

# F13: environment
rep("""  process at a time (a screen may run beside one). **A process deviation never ends the item.**""",
"""  process at a time (a screen may run beside one). **A process deviation never ends the item.**
  The cache tool's own compilation inside `lake exe cache get` is not a deviation (E-SERIAL).
- **Budget:** E-Q cont1's last Claude host (4 CPUs) ran 2–3× slower than the maintainer's: expect
  about 20 minutes for the bootstrap and each screen 2–3× the screen base's time; reserve about
  an hour for the finishing sequence.""")

# F11: the lint base
rep("""- **Lint:** `campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL (base: 0 FAIL, 3 WARN over 5 files), and
  `style_lint.py` on your file.""",
"""- **Lint:** `campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL (base: 0 FAIL, 3
  WARN over 5 files; the file is 5,432 lines at the base and 5,435 with the overlay), and
  `style_lint.py` on your file. No new line over 100 characters; the file's size WARN is
  expected.""")

# The REPORT checklist
rep("""- [ ] Every new declaration with its role; `P`'s and `Q`'s phases and tapes; each call's release;
      each E-Q leaf cited and where.""",
"""- [ ] Every new declaration with its role; `P`'s and `Q`'s phases and tapes, with the injection
      of each embedded machine (the clocked, hosted runs' tape plan); each call's release; each
      E-Q leaf cited and where; `dzTakeTM`'s docstring naming the missing row.""")

# F13: pitfalls
rep("""- **The simps field equations are pointwise**: `funext` before `rw`.""",
"""- **The simps field equations are pointwise**: `funext` before `rw`.
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
  `FinTM.computesFunInTime_lengthBits`, whose axioms are the standard three.""")

open(p, 'w', encoding='utf-8').write(s)
print('applied')
