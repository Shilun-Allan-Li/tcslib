# Gate 158 round 2 · W6: the final audit, with the repair PR (PR #PRNUM)

**Round 2 of the final audit.** Seyoon dispatches and merges.

- **Round 1** audited campaign `506078d6` (Lean `179c8c9c`) and returned HOLD: 0 blockers,
  1 major and 8 minors (`findings.md`, verbatim). This round checks the resolutions in
  `resolutions.md`.
- **The audited head** is PR #PRNUM's head (branch `closeout/g158-repairs`); the dispatch prompt
  gives the commit. It holds the round's records and its Lean:
  - **Records:** the round 1 corrections, already on the campaign branch at `12a3ce18`, and
    the later records on the PR branch.
  - **Lean:** head `bf6e26e8a42c0254a38837772e0ade27e57a62e4`. Its base is the campaign Lean `179c8c9c` (the #356 merge), and
    no Lean changed on the campaign between them.
- `pack.md` is round 1's. Its evidence (probes, census, lint) stands for the unchanged rest of
  the chapter scope.

## What changed since round 1

### Records (no Lean)

- **`FIDELITY.md`** (G158-02, -03, -04, -08, and G158-01's record):
  - row 1 names the tracked headline and its square-overhead hypothesis, and attributes the
    book form to `time_hierarchy_book`;
  - row 3 is a genuine restriction for non-monotone `f`, with the new book form for monotone
    `f`;
  - row 4's book column is `NTIME(n) ⊊ NTIME(n^1.5)`, disclosed as a weaker illustration;
  - row 5 is a strengthening; row 11's `S + 1` is constant absorption; row 18 has no
    divergence;
  - a new summary, and §Major.
- **`campaign/closeout/PLAN.md`** D3 lists Exercise 4.7 (G158-07).
- **`campaign/closeout/CARRIED-REGISTER.md`** (G158-05, G158-06):
  - the refactor plan's register items, with reasons and pointers: CH34-D3, RW-1 and the
    `zfBFallback` residual;
  - §3.2's optional items;
  - R2c's recorded reason;
  - the 712 stale blueprint entries (draft PR #362);
  - the #354 readers marked apart from the prospective ch2-4 overlap;
  - the 69 lint flags classified (`evidence/lint/LINT-CLASSIFIED.json`).

### Lean (PR #PRNUM; 6 files)

**New public declarations** (Seyoon, 2026-11-17), in `Diagonalization/NTimeHierarchy`:

```lean
theorem ntime_hierarchy_book {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hmono : Monotone f)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f (n + 1) ≤ g n) :
    NTIME f ⊂ NTIME (fun n => g n + 1)

theorem ntime_hierarchy_book_of_pos {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hmono : Monotone f) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f (n + 1) ≤ g n) :
    NTIME f ⊂ NTIME g
```

Both apply the existing `ntime_hierarchy` and `ntime_hierarchy_of_pos` through the private
`nh_book_dom`, which proves `f(n+1) + f(n) + n + 1 ≤ 3·f(n+1)` from monotonicity and
`n + 1 ≤ f(n+1)`.

**Documentation** (Seyoon, 2026-11-17: repair rather than carry):
- proof sketches for `mult_contribution`, `mult_next_column`, `mult_validate_field` (Mult),
  `compQ_length_le` (QueryReshape) and `searchDown_run` (NARMPSem) (G158-06);
- `## Main results` in `Machines/Parse.lean` (G158-06);
- EXPCOM's module text no longer calls the proved `exists_uniformMachineCode` a "sorried
  existence" (G158-09);
- NTimeHierarchy's module text gives the counterexample and lists the book forms. It no longer
  says that the linear overhead alone reaches book strength (G158-01).

**Two proof repairs** in Mult. These proofs are unchanged in round 1's tree. Their docstrings
changed here, so the seal check now covered them, and both failed it in run 1:
- `mult_contribution`'s last step unified through `astep`. It now applies `AReach.single`
  with explicit arguments and rewrites by `astep_inc`.
- `mult_next_column`'s first two steps used `change` through `astep`. They now rewrite by
  `astep_half` and `astep_inc`.

`nh_book_dom` first projected `TimeConstructible` directly; it now reads it through
`timeConstructible_iff`. `searchDown_run`, whose docstring also changed, unfolded `PreS` with
`simp`. It now cites `preS_of_ins`, as Deepen does. `mult_validate_field` unfolded `Canon` to
prove that the empty field is canonical; it now cites FragDec's `canon_bits 0`.

`SOURCE.json`: 6 owners, 8 changed or added declarations, 2 added (the two theorems above), none removed, no statement or definition body changed. Net **+102 Lean lines** (+125/−23). By file: NTimeHierarchy +55, Mult +25, NARMPSem +9, Parse +9, QueryReshape +5, EXPCOM −1.

## Brief for the auditor

1. **G158-01.** Check that the two new theorems state [AB09, Theorem 3.2] with only
   monotonicity of `f` added (and positivity of `g` for the exact class). Check that the
   private bound proves them, and that FIDELITY row 3, §Major and the module docstring describe
   the remaining restriction accurately.
2. **G158-02, -03, -04, -07 and -08.** Check the corrected rows and the D3 line against the
   book and the Lean.
3. **G158-05.** Check the register against REFACTOR-PLAN §3–§4, the duplication ledger and
   `R2C-SCANNER.md`.
4. **G158-06 and -09.** Check the classification of all 69 flags, and that the six genuine
   items and the EXPCOM text are repaired. Check that each new proof sketch describes its
   proof.
5. **Rule 10** on the PR: the changed proofs, with seals, controls and both sweeps (counts
   below).
6. **Done criteria** (PLAN §4) after these repairs: items 1–5 and item 6's W6 half.

## Evidence (`evidence/r2-repair/`)

- **`REPLAY.json`:** the merged-tree replay of the 6 owners' downstream closure on `oleans-c179c8`.
  - 129 modules replayed: 129 passed, 0 failed, 0 inherited admissions.
  - 898 objects in and 898 out.
  - Pool 3 of 4 cores under the 2026-11-17 parallelism rule; peak memory 3.6 GB of 16.9 GB; no
    back-off.
- **`BookProbe.lean` and `BookProbe.out`:** `#check` of both new theorems, which print the
  statements above, and `#print axioms`, which prints `propext`, `Classical.choice` and
  `Quot.sound` for each. The probe was run against the replay's output snapshot.
- **Seals:** the 8 changed or added proofs in 4 owners (NTimeHierarchy 3, Mult 3, NARMPSem 1, QueryReshape 1) pass, with all 18 other-file definitions they reach made irreducible. EXPCOM's and Parse's changes are module text only.
- **Controls:** one part, **29 sealed definitions and 58 paired identities**, each native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 8 roots and 0 read candidates. The Lean-backed sweep (`DEFSWEEP-SUMMARY.json`) finds 57 identifiers (Mult 44, NARMPSem 10, QueryReshape 3) and **no flag**: Mult's reach only core and Mathlib (`Function.update`, `reduceIte`, `rfl`, `Alternative.failure`). Citation homes (`CITATION-HOMES.json`): NTIME, TimeConstructible, ARM, ARMProof and FragDec, all bundled. The scope pass has `unknown namespace LogProg` errors in Mult and QueryReshape, the same kind gates 154 and 155 recorded.
- **Lint** (`style_lint.py` on the 6 changed files): 17 flags at the base, 9 at the head, none
  new.
  - **8 gone:** the five proof sketches, Parse's `## Main results`, and NTimeHierarchy's two
    prose false positives (line 32), whose text changed.
  - **9 left, all carried:** three oversized files, NTimeHierarchy's `## Main definitions`,
    and five signature-inflated sketch flags. The oversized files grow: NTimeHierarchy
    1,934 → 1,989 lines, Mult 1,474 → 1,499, QueryReshape 2,625 → 2,630. The register lists the
    round 1 sizes.
- **Copy screen** (population: the 6 changed files): 221 → 222 declarations, 25 → 25 directed
  pairs, 0 new, 0 gone (`PAIR-DISPOSITIONS.json`).
- **Earlier runs:**
  - **Run 1** (Lean head `7e213e5b`) passed its replay (129/129), but three seals failed:
    `nh_book_dom` and the two Mult proofs above.
  - **Run 2** (`e5e03fdd`) passed the replay, seals and controls. Its proof-syntax sweep
    flagged `searchDown_run`'s `simp [PreS, hdec]`.
  - **Run 3** (`0f37c470`) passed the same. Its sweep flagged `mult_validate_field`'s
    `simp [empty, Canon]`.

  This pack's evidence is from run 4, on `bf6e26e8a42c0254a38837772e0ade27e57a62e4`. The logs of runs 1–3 are in the carrier
  under `run1/` to `run3/`.
- `DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate158-w6-final-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
