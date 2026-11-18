# Gate 167, round 2 · (a5) PROG-2: the signatures of Light with input and output (statement gate on a mirror)

**Round 2 of a statement gate on a mirror.** No Lean PR is gated. Round 1 (`findings.md`) was
**HOLD**: 0 blocking, 4 major, 2 minor, 9 notes. Round 2 revises the mirror. Each finding's
resolution is in `resolutions.md`. Seyoon dispatches.

- **Ruling (Seyoon, 2026-11-18), on G167-03's scope:** H2's compiler theorem covers **all three**
  parts: coin streams, a footprint independent of time, and the padding and probability
  interface.
- **The mirror:** `campaign/items/ram-tm/prog2/PROG2Mirror.lean.txt`, 1,137 lines (round 1 is
  `PROG2Mirror-r1.lean.txt`). The main change: **the compiler is now mirrored concretely**.
  - `XStmt.size`, `xcompileStmt`, `XStmt.width`, `XCodeAt`;
  - `XSetting`, `XStart`, `XFinished`, `XSimulates`, `xsim`;
  - the program layout through `xcompileProgram`, and `xcompileProgram_correct`.

  These are built over the vendored `List Instr` code, which stays unchanged. Nothing is opaque
  any more.
- **The design:** `campaign/items/ram-tm/PROG2-DESIGN.md`. §3 now lists the deliverables and
  corrects round 1's `PolyTimeComputable` claim. §5 resizes H2, and §7 records the round-2
  ruling.
- **Check:** the mirror elaborates with 0 errors and 55 `sorry` warnings, all of them the intended
  statements (`prog2/mirror.log`). It was elaborated on `oleans-cl168-cl166`, the RAM branch's
  build with #379 and job E's draft. Only `Classes` and the Light and RAM files are used.

## Brief for the auditor

1. **The round-1 findings.** For each of G167-01 to G167-06, decide whether `resolutions.md` and
   the named declarations resolve it.
2. **The lifting (G167-01).** `XProgram.SilentSet` makes `XExec.traces_nil`, `EndsIO.ofXEnds` and
   `MeetsIO.ofXMeets` true. Check:
   - closure under calls;
   - stability under `append` and `behind`;
   - that it serves `Light.Std`'s routines inside a program whose other procedures emit and use
     coins.
3. **The compiler (G167-02, G167-06).** Fidelity to the vendored compiler in the bundle:
   - the seven old `xcompileStmt` cases are the vendored code under `.base`;
   - the four new cases and their sizes are right, with the local store;
   - the layout reproduces `ProgramCode`;
   - `XStart`, `XFinished` and `XSimulates` extend `Start`, `Finished` and `Simulates` with the
     output and coin count;
   - `xsim` is true with `1 ≤ lim.word`;
   - the claimed type boundary holds: which files stay untouched, and `XCodeAt.proj` with
     `XSteps.of_steps_proj`.
4. **The deliverables (G167-03, G167-04).** Check that each is true and is what its consumer needs.
   - **Agreement on streams.** The RAM reads `ρ.getD k false`; the Light run consumes a prefix.
   - **The footprint.** `xcells = [-lowCell, lim.space)` holds every cell a compiled step reads or
     writes, its size is `xcellCount`, and it does not grow with time.
   - **Padding and transfers.** `haltsWithin_of_streams` and `acceptsND_iff_haltsWithin` must
     match `WordRAM.mem_NSPACE_of_accepts` (bundled). `acceptProb_eq_randProb` needs `m ≥ T`.
   - **`polyTimeComputable_of_runs`** must match `WordRAM.polyTimeComputable_of_computes`.
5. **Readers and checks (G167-05, N2, N4, N8).** The readers restate their definitions. The
   inversions are true. The permanent checks state what the notes asked.
6. **Anything H1 or H2 would still need** that the mirror does not freeze.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate167-prog2-statements-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
