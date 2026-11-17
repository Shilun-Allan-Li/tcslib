# Gate 158 · W6: the final audit of the chapters 3–4 scope

**The final audit** (PLAN W6), over the campaign after W5. It includes no PR: the audited tree is
the campaign branch at the commit in the dispatch prompt. Seyoon dispatches.

- **Lean:** campaign Lean `179c8c9c` (the #356 merge, W4). #361 (W5, merged as `7149da27`)
  changed no Lean, and every later commit is records only.
- **Probes:** they ran on that Lean with snapshot `oleans-c179c8` on 2026-11-17, and stand for
  the audited tree.
- **Bundle:** the governing records, this gate's evidence, the 145 chapter-scope Lean files, and
  the class and constructibility definitions they rest on.

## Scope (PLAN W6)

One Codex gate over the chapter scope, the 145 modules under `ClassOracle`, `ClassPSPACE`,
`Diagonalization`, `SpaceComplexity` and `TimeHierarchy`. It covers:

- the headline and admission probes;
- the statement-vs-book fidelity table (PLAN §1);
- standards lint;
- the W1 census, refreshed;
- the carried-debt register.

The closeout is done when all of the following hold (PLAN §4):
1. Every core and core-late item is proved with standard axioms.
2. The chapter scope has no admission.
3. Every deferred item is listed (D3).
4. Every duplication family is retired or in the carried register (D4).
5. The blueprint covers the chapters (W5).
6. W6 is CLEAR and W7 has merged.

## Evidence

- **Headlines** (`evidence/probes/CloseHeadlines.*`): all 27 tracked headline theorems reach no
  constant that uses `sorryAx`, and each prints exactly `propext`, `Classical.choice`,
  `Quot.sound`. These are the 9 of chapter 3, the 17 of chapter 4, and `ladner`.
- **Additional results** (`CloseExtra.*`): the 19 additional roadmap results use standard axioms
  only. `Game.determined` uses `propext` and `Quot.sound`.
- **Admissions in scope** (`CloseAdmissions.*`): 21,573 owned constants checked, **0 direct
  admissions**. There were 21 on 2026-11-16; W2 (#328) removed the RD-2/H6 route.
- **Census** (`CENSUS.json`, `CensusAll.*`): all 898 modules of the snapshot, 76,201 constants,
  122 direct admissions, none in the chapter scope.
  - By area: BooleanAnalysis 78, Complexity 19, Programs 18, ErrorCorrectingCodes 7.
  - Complexity's 19 are RAMSimulation 14, `Build/RecordTable` 4 and `Expanders/Chernoff` 1. They
    are inherited from `main` and are the same as at W1.
  - The 166 of W1 less the 41 W2 removed is 125; the remaining difference comes from `main`'s own
    changes, synced in W4.
- **Fidelity** (`FIDELITY.md`): one row per headline, Lean statement against AB09.
  - 21 rows match the book exactly.
  - Three use `n + 1` or `S + 1` to cover the value 0.
  - `time_hierarchy` generalizes the book, whose form is the separate `time_hierarchy_book`.
  - `ntime_hierarchy` states its `o(·)` hypothesis with harmless extra terms.
  - `space_universal` fixes the input interface (the space bound is passed in binary).
  - No statement is weaker than the book's.
- **Lint** (`evidence/lint/`):
  - `campaign_style_lint.py --check8b` reports no failure in the chapter scope; its 37 failures
    are elsewhere.
  - `style_lint.py` over the 145 files reports long-standing items:
    - 11 files exceed the 1,000-line limit (TQBF, Ladner, NTimeDiagonalizer, NTimeHierarchy,
      Hierarchy, Inclusions, InputAccess, Mult, QueryReshape, Padding, WindowClock);
    - 13 module docstrings lack `## Main definitions`;
    - the 5 umbrella import files lack the standard `set_option` lines;
    - six findings are parser false positives on prose, such as "public `theorem theorem,`".
  - **Carried by ruling** (Seyoon, 2026-11-17): all three kinds are listed in the carried
    register's "Standards-lint items" section.
- **Register:** `campaign/closeout/CARRIED-REGISTER.md`, final at stage 3. Deferred items: W8
  (Exercise 3.3), W9 (relativized hierarchies) and the ch2-4 merge items.
- **Blueprint:** W5 (#361, gate 157 CLEAR in round 2). Validation is clean, and no undocumented
  declaration remains in scope. The 712 stale chapters 1–2 entries outside the scope are to be
  deleted in a later small PR (Seyoon, 2026-11-17).

## Brief for the auditor

1. **Probes.** Check that the four probe sources do what the pack says. Check that their outputs
   support the claims: the headline walks and axioms, the extra results' axioms, the scope
   admission count, and the census totals by area.
2. **Fidelity.** For each of the 27 rows of `FIDELITY.md`, check the Lean statement against the
   bundled source and its stated AB09 counterpart. Report any divergence the table misses or
   misstates. A Lean statement weaker than the book's is a finding.
3. **Definitions.** Check that `DTIME`, `NTIME`, `SPACE`, `NSPACE`, `TimeConstructible` and
   `SpaceConstructible` match AB09's definitions up to the documented conventions.
4. **Done criteria** (PLAN §4). State whether each criterion holds: items 1–5, and item 6's W6
   half.
5. **Register.** Check that every carried item is disclosed with a reason, including the lint
   items carried by ruling.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate158-w6-final-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
