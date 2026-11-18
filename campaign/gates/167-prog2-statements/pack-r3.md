# Gate 167, round 3 · (a5) PROG-2: the signatures of Light with input and output (statement gate on a mirror)

**Round 3 of a statement gate on a mirror.** No Lean PR is gated.

Round 2 (`findings-r2.md`) was **HOLD**: 0 blocking, 1 major, 3 minors. It confirmed G167-01,
-03, -04 and -06 and note N4 as resolved, with the core definitions, the lifting, the deliverables
and the corollary sound. Round 3 answers the four open findings; `resolutions-r3.md` maps each
to its repair. Seyoon dispatches.

- **The mirror:** `campaign/items/ram-tm/prog2/PROG2Mirror.lean.txt`, 1,295 lines. Round 2's text
  is `PROG2Mirror-r2.lean.txt`. It elaborates with 0 errors and 67 sorried statements
  (`prog2/mirror.log`), on `oleans-cl169-cl166`, the RAM branch's build after #385.
- **The design:** `campaign/items/ram-tm/PROG2-DESIGN.md`. §4 now gives the exact compiler edit
  set: which files change, which stay over `List Instr`, the footprint, and `Extended`'s new
  lemmas.

## Brief for the auditor

1. **G167-02.** `StartUp` is now in the edit set. Check:
   - `steps_start_proj` restates the vendored `steps_start` faithfully over the projection;
   - `xsteps_start` is true, including its footprint within `xcells`;
   - the five `xcodeAt_*` lemmas match the layout of `xcompileProgram`;
   - no other unchanged file is stated over `compileProgram` or over the type of the code.
2. **G167-07.** `XFinished.run` is now an `XStepsIn` run within `XSetting.cells`. Check:
   - that `xsim` stays true with it: every cell a compiled statement reads or writes lies in
     `[-max(2Q, 25 + 4·disp), lim.space)`;
   - that the whole-program setting's cells equal `xcells`;
   - that the named route suffices: footprint versions of the segment lemmas, `stepsIn_straight`,
     `XStepsIn.of_stepsIn_proj`, `xStepsIn_mono` and `xStepsIn_trans`.
3. **G167-05.** The readers restate their definitions; no new landing definition lacks one.
4. **G167-08.** The three new checks are true.
5. **Anything H1 or H2 would still need** that the mirror does not freeze.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate167-prog2-statements-r3-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
