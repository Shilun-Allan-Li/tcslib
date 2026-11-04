
**QyArith**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_ladder_succ_eq` | theorem | The next rung in terms of `X = f a + a + 1`: `ladder f (i + 1) = 2 ^ X ^ 4`. |
| `qy_ledger` | theorem | The ledger: the rungs passed before stage `s` sum to at most twice its bottom. |
| `qy_ones_val` | theorem | **The all-ones counter's value**: `m` ones are worth `2 ^ m - 1`. |
| `qy_rung_val` | theorem | **The next rung's counter value**: `m` zeros then a one are worth `2 ^ m`. |
| `qy_ones_ge` | theorem | **The counter is large enough**: the all-ones word of width `\|bits n\| + \|bits D\|` is worth at least `D (n + 1)`. |
| `qy_two_pow_bits_le` | theorem | **The counter is not too large**: `2 ^ \|bits n\| ≤ 2 n + 1`. |
| `qy_log_bits` | theorem | **`⌊log₂ n⌋` from `bits n`**: for `n ≥ 1`, `Nat.log 2 n + 1 = \|bits n\|`. |
| `qy_call_bound` | theorem | **The install call's bound under `f a ≤ n`** (the timeout certificate's arithmetic): with `a ≤ n` and `f a ≤ n`, the call's time bound `c' (c (f a + 1) + a + \|bits (f a)\| + 1)` is at most `c' (c ... |
| `qy_two_pow_le_ladder` | theorem | The ladder is at least `2 ^ (i + 1)`. |
| `qy_stage_lt_log` | theorem | **The stage index is below `log₂ n`**: for `n ≥ 3`, `stage f n < Nat.log 2 n`. |
| `qy_timeout_cert` | theorem | **The timeout certificate.** If the install call's exit time `t` is within its published bound `c' (c (f a + 1) + a + \|bits (f a)\| + 1)`, `a ≤ n`, and the clock's all-ones counter of width `\|bit... |

**QyA**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qyC` | def | A configuration in the normal form used by the main machine: a live state `s`, the input head `ip`, the work tapes `T`, the work heads `P` and the output `o`. |
| `qyC_mapState` | theorem | Renaming the state of a normal-form configuration renames its state only. |
| `qy_hosted` | theorem | **A hosted phase is a segment.** If phase `k` of a phase host runs from a normal-form configuration at `e` to one at the live exit `s'`, which the host redirects to `q'`, with no redirect earlier, ... |
| `qy_hosted'` | theorem | **A hosted phase is a segment**, with the avoided set checked along the phase's own run: it may contain states of phase `k` that the run does not visit up to its end. |
| `qy_hosted_last` | theorem | **A hosted last phase is a segment** without dispatch: if phase `k` runs to a live endpoint that the host does not redirect, with no redirect earlier, the host's run is the tagged phase run, avoidi... |
| `qy_hosted_run` | theorem | **A hosted phase's run.** The run part of `qy_hosted`, with no avoided set. |
| `qy_patch_end` | theorem | A word written over a buffer at its right end extends it: the cells `[\|u\|, \|u\| + \|w\|)` overwritten by `w`, and every other cell kept, is the buffer of `u ++ w`. |
| `qy_bufferTape_map` | theorem | The buffer of a mapped word is the mapped buffer. |
| `qy_guard_of_cut` | theorem | A guard from a row's first-visit cut: before the exit, every live state of the phase is one the host does not redirect. |
| `qy_copy` | theorem | **The mapped copy, appending.** `Turing.copyMapTM` copies the word `w` under the head of `src`, mapped by `g`, onto `dst` right after the word `u` there; nothing else changes. |
| `qy_copy_over` | theorem | **The mapped copy, overwriting.** `Turing.copyMapTM` copies the word `w` under the head of `src`, mapped by `g`, over the word `u` under the head of `dst`, which is no longer than `w`. |
| `qy_transfer` | theorem | **The mapped move.** `Turing.transferMapTM` with a blank residue moves the word `w` under the head of `src`, mapped by `g`, onto `dst` right after the word `u` there, blanking `src`. |
| `qy_clear` | theorem | **The clear.** `Turing.clearTM` blanks the word `w` under the head of tape `i`. |
| `qy_writeConst` | theorem | **The constant writer, appending.** `Turing.writeConstTM` writes the fixed word `w₀` on tape `i` right after the word `u` there, its head back where it started. |
| `qy_rewind` | theorem | **The rewind.** `Turing.rewindTM` brings the head of tape `i`, `n` cells into the word `u`, back to the word's start. |
| `qy_embed` | theorem | **An embedded run in normal form.** A source machine run along `σ` from the selected bank of a normal-form configuration, ending in normal form, is the host run of `Turing.embedEmitTM` from that co... |
| `qy_embed_state` | theorem | **An embedded run's states.** At every time, the state of the embedded run from a normal-form configuration is the source run's state from its selected bank. |
| `qy_call` | theorem | **A released call in normal form.** A call that reaches its exit first at the positive time `t`, with `res` installed, run through the release adapter from its fresh state over the seam of `arg`, r... |

**QyB**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_callHost` | theorem | **A hosted released call.** The install-call contract of `C` (positive exit time, positive cut, endpoint), run through the release adapter embedded along `σ`, from a normal-form configuration holdi... |
| `qy_step` | theorem | **One step of an own leaf.** At a live normal-form configuration, a transition that writes nothing, keeps the input head, moves each work head by `mv j` and emits `out` gives the normal-form config... |
| `QyCmp` | inductive | The control states of the length comparison `Turing.NTimeDiag.qyCmpTM`: the forward scan, the return pass carrying the verdict, and the live exits, one per verdict. |
| `qyCmpTM` | def | **The length comparison** (leaf L3, the unary compare). |
| `qyAt2` | def | The lockstep head vector of `Turing.NTimeDiag.qyCmpTM`: both compared heads at `i`. |
| `qyAt2_move` | theorem | Moving both compared heads by one step in the same direction. |
| `qy_cmp_run` | theorem | **The length comparison's run.** From the starts of words `u` and `v` on tapes `a` and `b`, `Turing.NTimeDiag.qyCmpTM` reaches `done (compare \|u\| \|v\|)` after exactly `2 · min \|u\| \|v\| + 2` s... |
| `QyEm` | inductive | The control states of the writer's emitter `Turing.NTimeDiag.qyEmitTM`: emitting the fixed prefix, reading a cell, holding a read symbol while looking ahead, emitting its copies, emitting the fixed... |
| `qyEmitTM` | def | **The writer's emitter** (leaf L6). |
| `qyBody` | def | The emitter's body: the word with each symbol written `rr + 1` times, its last symbol omitted when `dl` holds. |
| `qy_noMove` | theorem | Heads unmoved: the zero displacement. |
| `qy_moveOne` | theorem | One head moved right. |
| `qy_run_one` | theorem | One step of a run. |
| `qy_run_two` | theorem | Two steps of a run. |
| `qy_emit_run` | theorem | **The emitter's run.** From the start of the word `w` on tape `i`, `qyEmitTM` emits `pre ++ qyBody dl rr w ++ suf` and reaches `done`, the head of tape `i` at `\|w\|`, within `\|pre\| + \|suf\| + 3... |

**QyC**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_release_first_stop` | theorem | **A released call stops first at its exit time.** From the install call's contract alone (a positive exit time, the positive cut, the endpoint), the call wrapped by `seamReleaseTM` at its entry, st... |
| `qy_call_output_nil` | theorem | **A call before its exit is silent.** Every configuration of an install call before its exit has empty output: output only grows, and the exit's output is `[]`. |
| `qy_clocked_call` | theorem | **The clocked, released install call** (the first-arrival cut). |
| `qy_wordPatch_ones` | theorem | A word patched over an all-ones word of the same width is that word. |
| `qy_embed_gen` | theorem | **An embedded run, read through the transport.** The host run of `Turing.embedEmitTM` from a normal-form configuration is the transport of the source run from its selected bank. |
| `QyClockSpec` | def | **The clocked call's clause**, for a call `C` with entry and exit and a step clock `H` over its release adapter (the conclusion of `Turing.NTimeDiag.qy_clocked_call` after its witnesses). |
| `qy_clock_start` | theorem | The clocked call's start, in normal form: the call's seam on the bank, the all-ones counter on the clock tape, the input head at `1`. |
| `qy_clockHost_finish` | theorem | **The hosted clocked call, finishing.** If the call returns within the all-ones counter's value `2^m - 1`, the clock embedded along `σ` brings the normal-form configuration to `finish`, with the re... |
| `qy_clockHost_timeout` | theorem | **The hosted clocked call, timing out.** If the call has not returned within the all-ones counter's value, the clock embedded along `σ` reaches some `timeout` within `5 (2^m - 1) + 2m + 2` steps, s... |
| `qy_expand_start` | theorem | The expansion's start, in normal form: the destination word under the body head and the counter word under the counter head. |
| `qy_expandHost` | theorem | **The hosted expansion.** `Turing.expandTM` with the pattern `[true]`, embedded along `σ` (body tape `dst`, counter tape `ctr`), with the word `u` on `dst` and its head at the end, and the counter ... |
| `qy_seekHost` | theorem | **The hosted input seek.** The input seek of `Turing.exists_inputSeekTM`, embedded along `σ` on tapes holding `[true]` and a blank, brings the input head home to `1` from anywhere within `C (\|[tru... |
| `qy_emit_halt` | theorem | **The emitter halts at its exit.** One step from `done` halts with the output unchanged. |

**QyD**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `QySpec` | def | **An install call's clause**: from the seam of every argument `arg`, over every native input, `C` reaches its exit first at a positive time within `B arg`, with `F arg` installed. |
| `QyInSpec` | def | **An input call's clause**: from the blank seam over every native input `x`, `C` reaches its exit first at a positive time within `B \|x\|`, with `F x` installed. |
| `QySpec.mono` | theorem | An install call's clause is monotone in its bound. |
| `qy_installSpec` | theorem | An install call of a function-level machine has the clause of its contract. |
| `qy_inputSpec` | theorem | An input call of a function-level machine has the clause of its contract. |
| `QyKit` | structure | **The main machine's kit**: every called machine with its clause, the step clock over `f`'s call, and the input seek. |
| `qy_pow_mono` | theorem | `(n + 1)^a ≤ (n + 1)^b` for `a ≤ b`. |
| `qy_kit_exists` | theorem | **The kit exists** for time-constructible `f` and `g`: the published calls, the step clock over `f`'s call and the input seek, with their clauses' bounds simplified. |

**QyE**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `QyKit.K` | def | The tape count of the main machine: sixteen named tapes, then one block per call bank (each call's tape `0` is a named tape; its other tapes are its block). |
| `QyKit.le_K` | theorem | The sixteen named tapes come first. |
| `QyKit.tp` | def | The named tape `c`: `0` the unary `n + 1`, `1` the width word `1^{\|bits n\|}`, `2` the rung, `3` the next rung, `4` the word `1^{X - 1}`, `5` its fourth power, `6` the next rung's counter, `7` `f`... |
| `QyKit.tp_inj` | theorem | Named tapes are distinct when their names are. |
| `qyBank` | def | A call's bank: its tape `0` on the named tape `t0`, its other tapes on the block from `off`. |
| `qyBank_zero` | theorem | A bank's tape `0` is its named tape. |
| `qyBank_val` | theorem | A bank's other tapes lie in its block. |
| `qyEmb2` | def | Two tapes as a two-tape bank. |
| `QyKit.tp_val` | theorem | The value of a named tape. |
| `QyKit.bCb` | def | The banks, each at its block: the bank of `bits n`'s input call, tape `0` on tape `1`. |
| `QyKit.bCf` | def | The bank of `f`'s call bank, tape `0` on tape `7`. |
| `QyKit.bPu` | def | The bank of the fourth power's call bank, tape `0` on tape `5`. |
| `QyKit.bAb0` | def | The bank of the counter's increment bank, tape `0` on tape `6`. |
| `QyKit.bAbJ` | def | The bank of the increment bank of `j`, tape `0` on tape `10`. |
| `QyKit.bAbK` | def | The bank of the increment bank of `k`, tape `0` on tape `11`. |
| `QyKit.bPr` | def | The bank of the prefix call's bank, tape `0` on tape `9`. |
| `QyKit.bCl` | def | The bank of the length call's bank, tape `0` on tape `10`. |
| `QyKit.bPb` | def | The bank of the square's call bank, tape `0` on tape `4`. |
| `QyKit.bCg` | def | The bank of `g`'s call bank, tape `0` on tape `14`. |
| `QyKit.bClk` | def | The clock's bank: `f`'s call bank, then the counter tape. |
| `QyKit.tp_ne` | theorem | The named tapes are distinct. |
| `QyLK` | inductive | The locator's phases, in round order: the anchor; the argument and the clocked call; the length test; the word `1^{X - 1}` and its test; the fourth power and its test; the next rung and its compari... |
| `QyLPh` | abbrev | The locator's phase carriers. |
| `qyLPhFintype` | instance | The locator's phase carriers are finite. |
| `qyLPhDecEq` | instance | The locator's phase carriers have decidable equality. |
| `qyLocM` | def | The locator's phase machines. |
| `qyLocRed` | def | The locator's dispatch table. |
| `qyLoc` | def | **The locator**: the phase host over the round's phases, started at its anchor. |
| `QySK` | inductive | The setup's phases: `bits n`; `1^n`, one more cell, the rewind; the first rung `1^3`; the test `n ≥ 3`; the seek's `[true]`; the counter's copy, its fixed tail, the counter. |
| `QySPh` | abbrev | The setup's phase carriers. |
| `qySPhFintype` | instance | The setup's phase carriers are finite. |
| `qySPhDecEq` | instance | The setup's phase carriers have decidable equality. |
| `qySetM` | def | The setup's phase machines. |
| `qySetRed` | def | The setup's dispatch table. |
| `qySet` | def | **The setup**: the phase host over the setup's phases. |
| `QyTK` | inductive | The top's phases: the code's argument `1^{j + 1}` and `bits (j + 1)`; the budget `bits (X²)`; the three emissions. |
| `QyTPh` | abbrev | The top's phase carriers. |
| `qyTPhFintype` | instance | The top writer's phase carriers are finite. |
| `qyTPhDecEq` | instance | The top writer's phase carriers have decidable equality. |
| `qyTopM` | def | The top's phase machines. |
| `qyTopRed` | def | The top's dispatch table; the last emission's exit halts. |
| `qyTop` | def | **The top's writer**: the phase host over the top's phases. |
| `QyMK` | inductive | The middle's phases: the input head home; the code; the budget `bits (g n)`; the three emissions. |
| `QyMPh` | abbrev | The middle's phase carriers. |
| `qyMPhFintype` | instance | The middle writer's phase carriers are finite. |
| `qyMPhDecEq` | instance | The middle writer's phase carriers have decidable equality. |
| `qyMidM` | def | The middle's phase machines. |
| `qyMidRed` | def | The middle's dispatch table; the last emission's exit halts. |
| `qyMid` | def | **The middle's writer**: the phase host over the middle's phases. |
| `QyMain` | inductive | The main machine's phases: the setup, the locator, the two writers, and the empty output. |
| `QyMainPh` | abbrev | The main machine's phase carriers. |
| `qyMainPhFintype` | instance | The main machine's phase carriers are finite. |
| `qyMainPhDecEq` | instance | The main machine's phase carriers have decidable equality. |
| `qyMainM` | def | The main machine's phase machines. |
| `qyMainRed` | def | The main machine's dispatch table: the setup's long exit to the locator's anchor and its short exits to the empty output; the locator's top escape to the top's writer and its other escapes to the m... |
| `qyM₁` | def | **The main machine `M₁`**: the phase host over the setup, the locator and the writers. |

**QyF**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `QyKit.m` | def | The clock's counter width on inputs of length `n`: the bits of `n` and of the call bound's constant. |
| `qyLay` | def | **The anchor layout** at the rung `a - 1` with `unpair h = (j, k)`: `1^{n+1}` on tape `0`, the width word on tape `1`, the rung `1^a` on tape `2`, `1^j` and `1^k` on tapes `10` and `11`, the seek's... |
| `QyKit.tape_cases` | theorem | Every tape is a named tape or none of them (`Classical.exists_or_forall_not`). |
| `qyBank_ne_tp` | theorem | A bank's tapes other than its tape `0` lie in its block, off every named tape. |
| `qySetF` | def | The setup's exits: the long exit at the end, and the short exits of the test `n ≥ 3`. |
| `qySetB` | def | The setup's time bound on inputs of length `n`. |
| `qy_bits_val` | theorem | The bits of `n` are worth `n`. |
| `qy_blank_bank` | theorem | A blank bank holds the seam of the empty argument. |
| `qy_arg_bank` | theorem | A bank holding `arg` on its tape `0` and blanks elsewhere holds the seam of `arg`. |
| `QyKit.bPr_ne` | theorem | The prefix call's bank tapes other than tape `0` are off the named tapes. |
| `qySetT5` | def | The setup's tapes before its test: `bits n` expanded, `1^{n+1}` on tape `0`, the width word on tape `1`, the rung `1^3` on tape `2`, every other tape blank. |
| `qy_setup_head` | theorem | **The setup's head**: from the blank seam, `bits n` by the input call, its expansion to `1^{n+1}` on tape `0`, and the first rung `1^3` on tape `2`, within `cbA (n + 1) + 7n + 2\|bits n\| + 27` ste... |
| `qy_setup_long` | theorem | **The setup, long path** (checkpoint 2): on inputs of length `n ≥ 3`, from the blank seam, the setup reaches its long exit at the anchor layout of the first rung `ℓ₀ = 2` (`a = 3`) with `unpair 0 =... |
| `qy_setup_short` | theorem | **The setup, short path** (checkpoint 2): on inputs of length `n ≤ 2`, from the blank seam, the setup stops at a short exit of its test `n ≥ 3` within `qySetB κ n` steps, avoiding its exits before,... |

**QyG**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_bits_len_mono` | theorem | The length of `bits` is monotone. |
| `qy_lt_two_pow_bits` | theorem | Every number is below two to the length of its bits. |
| `qy_unpair_succ_lt` | theorem | The successor of a pair below the diagonal's next corner: `(j, k) ↦ (j + 1, k)` when `j + 1 < k`. |
| `qy_unpair_succ_last` | theorem | The successor at the column's last pair below the diagonal: `(k - 1, k) ↦ (k, 0)`. |
| `qy_unpair_succ_diag` | theorem | The successor on the diagonal: `(j, j) ↦ (0, j + 1)`. |
| `qy_unpair_succ_gt` | theorem | The successor above the diagonal: `(j, k) ↦ (j, k + 1)` when `k < j`. |
| `QyKit.bClk_castSucc` | theorem | The clock's bank on the call's tapes is the call's bank. |
| `QyKit.bClk_last` | theorem | The clock's last tape is the counter tape `8`. |
| `QyKit.bCf_ne` | theorem | `f`'s call bank tapes other than tape `0` are off the named tapes. |
| `QyKit.bPu_ne` | theorem | The fourth power's call bank tapes other than tape `0` are off the named tapes. |
| `QyKit.bAb0_ne` | theorem | The counter's increment bank tapes other than tape `0` are off the named tapes. |
| `QyKit.bAbJ_ne` | theorem | The increment bank of `j`: tapes other than tape `0` are off the named tapes. |
| `QyKit.bAbK_ne` | theorem | The increment bank of `k`: tapes other than tape `0` are off the named tapes. |
| `qyLayT` | def | The anchor layout's tapes. |
| `qyAnc` | def | The locator's anchor. |
| `QyLK.isEsc` | def | The locator's escape phases: interior, top and timeout. |
| `qyLocE` | def | The locator's escapes: every state of an escape phase. |
| `qy_notStop` | theorem | A state of a phase other than the anchor and the escapes is off the round's stop set. |
| `qy_esc_mem` | theorem | An escape phase's sweep state is an endpoint of a round. |
| `qyScratch` | def | The tapes a round may leave dirty: the clock's bank (the call's and the counter) and the round's scratch tapes `3` to `6`. |
| `QyEscT` | def | **An escape's tapes**: off the round's scratch, the anchor layout, every head at `0`. |
| `qy_tp7_mem` | theorem | `f`'s call tape is in the clock's bank. |
| `qy_tp8_mem` | theorem | The counter tape is in the clock's bank. |
| `qy_not_scratch` | theorem | Off the scratch means off the named scratch tapes `3` to `8`. |
| `qy_round_of_seg` | theorem | **A round from its first step and a segment.** If the run from `c`, at the anchor, reaches `c₁` in one step, and from `c₁` a segment avoiding the round's stop set reaches `c'`, at the anchor or an ... |
| `qy_rnd_call` | theorem | **The round's call** (checkpoint 3): from the anchor layout at the rung `1^a`, `a ≤ n`, the locator copies the rung onto `f`'s call tape and runs `f`'s witness under the clock. |

**QyH**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qyTA` | def | The tapes after the round's call: `bits F` on `f`'s call tape `7` and the counter's word `w'` on tape `8`, over the anchor layout. |
| `qyTB` | def | The tapes after a passed round's tests: `1^{F + a}` on tape `4`, the expanded counter on tape `7`, `1^{X⁴}` and `1^{X⁴ + 1}` on tapes `5` and `6`, and the next rung `1^{ℓ' + 1}` on tape `3`. |
| `qyTestS` | def | The tests' time bound when the round stops: linear in `n`, plus the fourth power's call on a word shorter than `\|bits n\|`. |
| `qyTestP` | def | The tests' time bound when the round passes: the next rung, plus polylogarithmic terms. |
| `qy_rnd_tests` | theorem | **The round's tests** (checkpoint 3): from the length test after a returned call (`bits F`, `F = f a`, on tape `7`), with `X = F + a + 1` and the next rung `ℓ' = 2 ^ X⁴`, the locator ends at its in... |

**QyI**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_rnd_clean` | theorem | **A passed round's cleanup** (checkpoint 3): from the tapes `qyTB` after the tests, the locator clears the old rung, moves the next rung `1^{ℓ' + 1}` onto the rung's tape, clears the scratch tapes ... |
| `qy_layT_pair` | theorem | The anchor layout with the pair's tapes changed is the layout of the new pair. |
| `qy_rnd_pair` | theorem | **A passed round's pair update** (checkpoint 3): from the anchor layout with `(j, k) = unpair h` on tapes `10` and `11`, the locator moves the pair to `unpair (h + 1)` by the successor rule of `Nat... |

**QyJ**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qyRndP` | def | A passed round's time bound: the next rung `ℓ'`, the counter's width `m`, the call's bound on arguments below `\|bits n\|`, the polylogarithmic calls, and the pair `(j, k)`. |
| `qyRndS` | def | A stopping round's time bound: linear in `n` and in the clock's budget `2 ^ m`, plus the fourth power's call on a word shorter than `\|bits n\|`. |
| `qy_round` | theorem | **One round of the locator** (checkpoint 3), as a `Turing.Round` at the anchor with the three escapes: from the anchor layout at the rung `1^a`, `a ≤ n`, with `(j, k) = unpair h`, and with `X = f a... |

**QyK**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_pow6_le` | theorem | **A sixth power is at most exponential**: `x ^ 6 ≤ 6 ^ 6 · 2 ^ x`. |
| `qy_sum_affine` | theorem | A sum of an affine family: `∑_{r < s} (11 u r + c) = 11 ∑_{r < s} u r + s c`. |
| `qyCk` | def | The kit's polylogarithmic constant: the coefficient of `(\|bits n\| + 1) ^ 5` in a round. |
| `qyDk` | def | The kit's linear constant: the coefficient of `n + 1` in a stopping round. |
| `qyLoopA` | def | The locator's constant: its whole run on inputs of length `n ≥ 3` is within `qyLoopA (n + 1)`. |
| `qy_rndP_le` | theorem | **A passed round's bound, simplified**: with `j + k ≤ \|bits n\|`, the bound `qyRndP` is at most `11 ℓ'` plus the polylogarithmic `qyCk (\|bits n\| + 1) ^ 5`. |
| `qy_rndS_le` | theorem | **A stopping round's bound, simplified**: with `a ≤ n`, the bound `qyRndS` is at most `qyDk (n + 1)` plus the polylogarithmic `qyCk (\|bits n\| + 1) ^ 5`. |
| `qyAt` | def | The locator's anchor configuration at the stage `i` on inputs of length `n`: the rung `ℓᵢ + 1` and the pair `unpair i`. |
| `qy_loop` | theorem | **The locator's loop** (checkpoint 4): on inputs of length `n ≥ 3`, from the anchor at the first rung, the locator runs, avoiding its escapes before the end, to an escape at the stage `s = stage f ... |

**QyL**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_not_scratch_ge` | theorem | A tape past the blocks of the input call and `f`'s call is off the round's scratch. |
| `qy_not_scratch_tp` | theorem | A named tape other than `3` to `8` is off the round's scratch. |
| `qy_bank_not_scratch` | theorem | A bank tape other than tape `0`, at an offset past `f`'s call bank, is off the scratch. |
| `QyEscT.tp` | theorem | An escape's tapes at a named tape off the scratch: the layout's word, its head at `0`. |
| `QyEscT.bank` | theorem | An escape's tapes at a bank tape past `f`'s call bank: blank, its head at `0`. |
| `QyKit.bCl_ne` | theorem | The length call's bank tapes other than tape `0` are off the named tapes. |
| `qy_code_calls` | theorem | **The stage code's calls after an escape** (checkpoint 5): on an escape's tapes with the input head at `1`, the increment's call on the bank of tape `10` gives `1^{j + 1}`, and the length call on t... |
| `qy_seek_run` | theorem | **The input seek after an escape** (checkpoint 5): on an escape's tapes, from any input head position, the seek on tapes `12` and `13` (`[true]`, worth `1`, and a blank tape) returns the input head... |
| `qy_mid_code` | theorem | **The middle writer's head** (checkpoint 5): from its entry on an escape's tapes, the input seek, the increment of `j` and the length call reach the budget's call with the input head at `1` and `bi... |
| `qy_top_code` | theorem | **The top writer's head** (checkpoint 5): from its entry on an escape's tapes with the input head at `1`, the increment of `j` and the length call reach the budget's call with `bits (j + 1)` on tap... |

**QyM**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_flatMap_dbl_dbl` | theorem | Doubling twice is quadrupling: `(B.flatMap dbl).flatMap dbl = B.flatMap (replicate 4)`. |
| `qy_writer_word` | theorem | **The writer's word** (L6's three emissions): the flag, the budget field's bits each written four times and `[false, false, true, true]`; the code's bits but the top one, doubled, and `[false, true... |
| `qy_hosted_halt` | theorem | **A hosted phase that halts**: if phase `k` halts at time `t`, with no redirect before, the host halts at `t` with the phase's output. |
| `qy_emit_stop` | theorem | An emitter's run to its halt: the run of `qy_emit_run` and one more step (`qy_emit_halt`). |
| `QyKit.bCg_ne` | theorem | `g`'s call bank tapes other than tape `0` are off the named tapes. |
| `QyKit.bPb_ne` | theorem | The square's call bank tapes other than tape `0` are off the named tapes. |
| `qyMidB` | def | The middle writer's time bound: the seek, the code's calls, `g`'s call and the emissions. |
| `qyTopB` | def | The top writer's time bound: the code's calls, the square's call on `1^{X - 1}` and the emissions. |
| `qy_mid_run` | theorem | **The middle writer** (checkpoint 6): from its entry on an escape's tapes, it halts within `qyMidB` steps with the output `false :: ⟨⟨bits (g n), α⟩, 1^{n + 1}⟩`, `α` the bits of `j + 1` but the to... |
| `qy_top_run` | theorem | **The top writer** (checkpoint 6): from its entry on an escape's tapes with `1^{F + a}` on tape `4` (`F = f a`, `a` the rung), it halts within `qyTopB` steps with the output `true :: ⟨⟨bits ((F + a... |

**QyN**

| declaration | kind | role (docstring's first sentence) |
|---|---|---|
| `qy_initCfg` | theorem | `M₁`'s initial configuration is the blank seam at the setup's entry. |
| `qy_mainRed_setup` | theorem | `M₁` dispatches from its setup only at the setup's exits. |
| `qy_mainRed_loc` | theorem | `M₁` dispatches from its locator only at the locator's escapes. |
| `qyWk` | def | The writers' constant: the coefficient of `g n + 1` in either writer. |
| `qyMainA` | def | `M₁`'s constant `A`: the setup's, the locator's and the writers'. |
| `qy_midB_le` | theorem | The middle writer's bound is linear in `g n + 1` when `j ≤ n ≤ g n`. |
| `qy_topB_le` | theorem | The top writer's bound is linear in `n + 1` when `X³, X², a, j ≤ n`. |
| `qy_main_long` | theorem | **`M₁` on inputs of length `n ≥ 3`** (checkpoint 7): from its initial configuration it halts within `qyMainA (g n + 1)` steps with the stage query of `1ⁿ` as its output. |
| `qy_main_short` | theorem | **`M₁` on inputs of length `n ≤ 2`** (checkpoint 7): from its initial configuration it halts within `qyMainA (g n + 1)` steps with the empty output, the stage query of `1ⁿ`. |
| `qy_main` | theorem | **The main machine computes the query on the unary word of every input's length** (checkpoint 7, the target's `hmain`): for time-constructible `f` and `g`, `M₁` halts on every input `x` within `qyM... |
