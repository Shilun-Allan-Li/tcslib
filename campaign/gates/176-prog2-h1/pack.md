# Gate 176 · PROG-2 job H1: input, output and coins in the Light language core (PR #394)

**Not yet clear to merge.** PR #394 is a draft into `complexity/ram-simulation`. It extends the
vendored light language in place with `inBit`, `emit`, `coin` and `half` and the stream-aware
logic. This is job H1 of PROG-2, the Codex fill `fill-prog2-h1`. The Codex audit was approved by
Seyoon on 2026-11-19. Seyoon dispatches and merges.

- **Lean head:** `3d3d0f1aa0b59cd4ec2a2c1c83176e0b9bc5f010` (branch `ram/prog2-h1`). The commits:
  1. the fill's patch, landed unchanged (`fill-prog2-h1.zip` SHA-256 `38413406…`; it reproduces
     all 13 delivered files byte for byte);
  2. a maintainer edit to `Calls`' vendored header, naming its one change (`meets_iff`'s explicit
     arguments), and removing two stray blank lines;
  3. a merge of the RAM branch, bringing in #391 (no conflict; #391 touches no Light file);
  4. a maintainer repair of this gate's first run, which found four new style findings. Three
     readers in `IO.lean` used `@[inherit_doc]` instead of a docstring; they now have their own.
     The vendored `Ends.of_blockSafe` grew past the proof-sketch threshold with its four new
     cases; it now has a docstring with a sketch, listed in `Rules`' header. Run 2 has no new
     style finding.
- **The frozen statements:** gate 167 cleared the mirror
  `campaign/items/ram-tm/prog2/PROG2Mirror.lean.txt` (bundled). Its header maps each mirror name
  to its in-place name. The brief is `briefs/fill-prog2-h1.md`.
- **Rulings that bind:**
  - the design's process (Seyoon, 2026-11-18): a mirror statement gate, then H1 with the compiler's
    new cases as disclosed temporary admissions, then H2;
  - rule 10 does not apply between vendored files (Seyoon, 2026-11-18);
  - `meets_iff` takes the mirror's explicit arguments (Seyoon, 2026-11-19). This changes the
    statement of a reader job G published (#382), forced by the brief's naming; its one user in
    `TMProc` was updated;
  - H2's Complexity-facing home is a new `RAMSimulation/LightIO.lean` (Seyoon, 2026-11-19), so
    H1 lands none of `AcceptsND`, `acceptProb` or the deliverables.

## What it adds

| Area | Content |
|---|---|
| `Syntax` (in place) | `Stmt` gains `inBit`, `emit`, `coin`, `half`; `Limits` gains `input`; `Exec` gains the output and coin indices and four rules; `inBitVal`, `inBitVal_eq`; reader `State.bounded_iff` |
| `Logic`, `Assigns`, `RunsStayInLimits`, `Renumber`, `Rules` (in place) | the six inductions over `Exec` extended; `Ends` keeps its type and hides `σ' o r c`; reader `ends_iff`; `Exec.bounded` gains `1 ≤ lim.word`; `Stmt.shift`'s four arms and its eleven readers, `Program.behind_eq` |
| `Light/IO.lean`, `Light/IO/Exec.lean` (new, 491 and 170 lines) | `EndsIO`, `MeetsIO` and their rules, `EndsIO.callLast`, `Ends.coin`; `Exec.det`, the trace-length bounds, the four inversions; `Stmt.silent`, `Stmt.calls`, `Program.SilentSet` and the lifting `EndsIO.ofEnds`, `MeetsIO.ofMeets`; `EndsIO.take_iff`; five permanent checks |
| `Compiler/StatementCode`, `Simulation`, `WholeProgram` | sizes and widths for the new arms, with four width readers; the indices threaded; `sim_seq`, `sim_whileTrue`, `sim` and `compileProgram_correct` gain `1 ≤ lim.word`; **the admissions:** the four new arms of `compileStmt`, `length_compileStmt` and `sim` (12 sites) |
| `Calls`, `TMProc` | `meets_iff`'s explicit arguments; one witness line |

The fill's landing table (`LANDING.md`, 79 rows) compares every landed signature with the
renamed mirror's: all match. The changed existing statements are those the kit lists as changed
headers, each forced by the new constructors, the indices or `Exec.bounded`'s new hypothesis
(`REPORT-prog2-h1.md`, "Forced changes"); plus `meets_iff`, ruled above.

## Brief for the auditor

1. **Fidelity to the mirror.** Every landed declaration states what the mirror froze, after the
   renaming. In particular, `Light.Ends` keeps its type and only hides the two new traces, and
   `Limits.input` replaces the mirror's `XLimits` wrapper. Check that the mirror-only declarations
   did not land.
2. **The semantics** of the four rules: `inBit` reads `inBitVal`, `0` off the input; `emit`
   appends "nonzero"; `coin` consumes one bit; `half` is `⌊e/2⌋`. Check the costs and that the
   old rules emit and consume nothing.
3. **The logic.** `Exec.det`, the trace-length bounds and the inversions are true. `EndsIO`'s rules
   are sound. The silent-set lifting is stable under appending and relocation, as gate 167's
   round 3 (N3, N5) required.
4. **Forced changes only.** Every changed existing statement is forced, and the 13 new readers
   are pure restatements.
5. **The admissions** are exactly the compiler's new cases, and nothing outside `Compiler/`
   reaches one. The kit's admission walk shows this (below).
6. **Duplication.** The five private helpers (`rest_prefix`, `trace_length`, `of_empty`,
   `map_run`, `shift_facts`) factor the shared arguments. Check that no `Ends` rule's proof is
   copied for its `EndsIO` twin.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay on `oleans-cl174b-cl175`, the RAM branch's build
  after #391. 39 modules, the closure of the changed Light files: 39 passed, 0 failed. The kit's
  static `sorry` count differs from the replay's for one module, by a **declared exception**
  (`static_sorry_expected`). `Compiler/StatementCode` has 2 admitted source declarations, and
  Lean warns 9 times, once per auxiliary declaration of the recursive `compileStmt` and
  `length_compileStmt`. Any other mismatch would fail.
- **Admission walk** (`ADMISSION-WALK.json`): `EndsIO.ofEnds`, `MeetsIO.ofMeets`, `Exec.det`,
  `EndsIO.take_iff`, `EndsIO.callLast`, `check_det_length` and `Light.exists_tmProc` reach **no**
  admission. `compileProgram_correct` reaches exactly `compileStmt`, `length_compileStmt` and
  `sim`.
- **Seals:** 55 proofs. The two new TCSlib files, `IO` and `IO/Exec`, pass with every other
  file's definitions irreducible. The vendored files fail where upstream's proofs destructure
  `Ends` or read `ProgramCode`'s layout. These are vendored-to-vendored reads, already present at
  the base, and exempt by ruling. The logs are in the data carrier.
- **Controls:** 73 definitions and 146 identities in two parts, native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 4 read candidates in 104 roots, all in
  `compileProgram_correct`'s vendored `simp` calls (`codeLayout`, `mainFrame`, `tailPos`, defined
  in `ProgramCode`). They are unchanged from the base and exempt as vendored-to-vendored.
- **Style lint:** no new finding at the head (run 2).
- **Copy screen:** the 13 changed files plus the 24 unchanged Light files. 63 → 65 pairs, 2 new
  and 0 gone, both classified. Upstream's `Ends.seq`/`Ends.whileStep` cross half once the two
  trace witnesses are threaded through them.
- **The fill's report** (`REPORT-prog2-h1.md`) and landing table (`LANDING.md`).

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate176-prog2-h1-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
