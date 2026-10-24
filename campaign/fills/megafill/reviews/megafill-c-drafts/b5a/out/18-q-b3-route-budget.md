# 18 Q-B3 (the two refinements), the route's soundness, the ledger and the budget

## The two refinements of the frozen sketch
1. **The window `x.take t`** instead of "x on a buffer tape". The only published row that places
   a suffix of the input on a tape is `exists_inputWindowCopyTM`, which copies
   `(z.drop p).take (value of the counter)`; with the counter `bits t` that is `x.take t`
   (`ic_window_call`'s statement). Copying all of `x` would need a counter ≥ |x|, which the
   startup does not have. Bounded acceptance within `t` steps reads at most `t` input cells, so
   `ComputesInTime (x.take t) [true] t ↔ ComputesInTime x [true] t` (the route probe's
   `b5a_accepts_take`, proved from `NDTM.runWith_initCfg_take`). Legitimate: the sketch is not
   edited, the mathematics is the same, and the brief binds where it refines.
2. **The landed verdict `h1HostedVerdict_accepts`** instead of re-describing the clock. It is the
   same machine the sketch describes (the step block hosted by Z1 on the buffer, the counter loop
   over `bits t`, the summary test at `escape`, `false` at `done`), already proved in the file.
   Citing it is required by "never re-walk a landed contract".
Policy §3 asks the docstring to describe the proof the code performs; the target's docstring is
frozen and its fill appendices (8584–8653) also carry campaign labels, dates and `audits/` paths.
The draft leaves the rewrite to the maintainer at integration (lines 245–247), as for the core
(its F7, edit 4). Suggest: for a complete delivery REPORT.md proposes the `**Implementation.**`
paragraph (phases, the window and locality, the ledger), which the maintainer edits in at landing.

## The five-step route: soundness (checked against the published statements)
- Phase order equals the core's (out/09): pass 1, input rewind, pass 2, rewind `bits t`, copy the
  counter (heads unchanged by `copyTM_run_ofCfg`), the window from the suffix (head at
  `4|bits t| + 2|α| + 7 = 2|u| + 3` after pass 2; the counter consumed), second input rewind,
  rewind `α`, install (`Cfg.ofWords … (stateWord C.k α)` needs head 1 and α at 0; returns
  `stateWord C.k (serializeK M)`), layout (src = the installed tape, cleared; table and summary at
  0), rewind the window (the buffer head is `d.inputPos − 1 = 0`), the verdict by R1.
- The verdict's start is exactly `vhostCfg (counterLoopCfg (some (.dec .run)) d (bufferTape t.bits) 0) true 1 []`
  with `d` the represented initial configuration on the window (`StepBlock.Rep_iff`), `d.output = []`;
  `S`'s output is `[] ++ [answer]`; halting is the verdict's halt through `embedEmitTM` and the seams.
- **Missing from the route:** the start from `S.tm.initCfg z` (out/11).
- Nothing else is assumed beyond published lemmas: every cited row is public and on the standard
  axioms (out/04, out/05); the window verdict and the five route lemmas are proved (out/06–07).

## The uniform ledger (N = |α| + |x| + t + 1, L₀ = |F.serialize F.fallback|)
passes 16|bits t| + 8|α| + 25 each; input rewinds p + 1 with p ≤ |z| + 1 = 2(2|bits t| + |α| + 2)
+ 2 + |x| + 1; rewinds n + 2; copy 2|bits t| + 2; window C(min t |x| + 1) + 2|bits t|; install
a((|α| + 1)^d + |α| + max |α| L₀ + 1); layout C'(|serializeK M| + 1) ≤ C'(max |α| L₀ + 1) (by
`serialize_eq`, `serialize_decode_length_le`); loop t·50(|table| + 1) + 4t + 2|bits t| + 3 with
|table| ≤ max |α| L₀ (`b5a_table_le`); seams +1 each. Each is ≤ c·N^e with c, e depending on F
only (|bits t| ≤ t); the sum is ≤ D·N^D for D ≥ Σc and D ≥ max e since N ≥ 1. Every constant
(the installer, the layout's C', the window's C, a, d, L₀) is chosen from F before α, x, t: the
uniform quantifier order of note 34 holds. Sound.

## Size and budget
- Under A: the startup assembly is the bulk. The core's phases 1–11 and loop entry are about
  1,060 lines (NDCodeSimulator 924–1990) for a fixed `k = 3` bank (`Fin 7`, numerals, `omega`);
  B5a's verdict has `1 + (F.k + 2 + 1)` tapes with `F.k` a parameter, so its embedding and tape
  bookkeeping are more general. The drafting report's 800–1,200 lines is plausible; 5 hours with
  two long screens makes a complete delivery unlikely; a partial at checkpoint 3–4 is the
  realistic expectation (the draft says so).
- Under B: plus the kit's analogues (about 300 lines), as the report says.
- Screens: 87 minutes before; the after run longer (out/12). With the before run in the background
  and the after run counted outside the item's budget (the report's Q-M2 recommendation), 5 hours
  of fill time remain about 4.5; otherwise 6 hours.
