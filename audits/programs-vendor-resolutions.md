# Programming-layer port, fidelity gate: resolutions (CLOSED, round 1)

## Round 1 (2026-10-12): 0 blockers, 0 majors, 7 minors, 66 notes

The findings are verbatim in `audits/programs-vendor-findings.md`. The pack is
`audits/programs-vendor-pack.md`, with its 118-section bundle `audits/programs-vendor-bundle.md`.
The auditor checked every file pair, not a sample:
- **Integrity and provenance.** It recomputed every hash and blob id. The upstream and the
  vendored trees were also confirmed against GitHub at their pinned commits (notes 8–9).
- **No undeclared code change.** The only code differences beyond M1–M6 and M11 are the two M7
  substitutions and the nine M8 repairs (note 10).
- **Statements unchanged.** Every retained signature and definition body is unchanged after the
  renames. The 796 named declarations match, and the only drops are M4's 17 (notes 11–12).
- **Each repair is a faithful local proof-body edit** (notes 64–72).
- **The generator** reproduces all 41 files, the facades and the whole diff byte for byte
  (note 17).

| Finding | Disposition |
|---|---|
| 1 (minor): `Programs.lean` does not import the three topic facades, so they are unreachable from the root. `NOTICE` names two facades (`Light/Lib.lean`, `Light/Compiler.lean`) that do not exist | **Resolved.** `TCSlib/Programs.lean` now imports `TCSlib.Programs.Util`, `.WordRAM` and `.Light`, as well as every module, so all 46 area files are reachable from the root. `scripts/vendor_afm26/facades.py` reproduces this. The nested facades are not created, since the lint's facade rule requires direct imports. `NOTICE` now names exactly the four facades. The closure check of `TCSlib.Programs` is clean. |
| 2 (minor): `light_assoc`'s docstring ("No definition is opened") and the module text ("stays closed") promise more opacity than `with_reducible` gives | **Resolved (documentation only).** Both passages now carry a vendoring note: at v4.25.0, reducible definitions such as abbreviations may unfold. The edit is made by `fixes.py` (two documentation entries) and listed in the file's header. The closure check of `Light/Tactics` is clean. PROG-1(b) keeps the revisit at the next Lean bump. |
| 3 (minor): the exclusion list is not exhaustive. The generic `Lang/Renumber.lean` (procedure relocation) and `Machine/Footprint.lean` (read/write footprints) were omitted | **Accepted.** The port is described as the 41-module import closure of the README's roots, not as upstream minus a complete exclusion list. The two generic modules are recorded as **deferred** in design §15b and PROG-1(e): `Footprint` is a candidate input to stage 2's space bound, and `Renumber` to the compiler extensions. Neither is needed by the present 41 files. |
| 4 (minor): `shipcheck.py` rejects the M10 Batteries import | **Resolved.** The committed script accepts `Mathlib` and `Batteries` imports. The historical census is not presented as a run of the current script. |
| 5 (minor): "713 new public names" includes a docstring false match. The screen's populations and command are not attached | **Resolved.** A comment-aware, namespace-qualified enumerator, `scripts/vendor_afm26/namescreen.py`, gives **712** public names in `TCSlib/Programs`, against 3,838 outside `Complexity` and `Programs`, with **no intersection** (`audits/logs/programs-vendor-namescreen.log`). Both inventories are attached (`audits/evidence/programs-vendor/names-*.txt`). The older count of 3,966 used the old line-based enumeration; the `Complexity` library is covered exactly by the joint elaboration. |
| 6 (minor): "records only, plus one comment line" overstates the relationship between `155255ed` and the code commit | **Accepted; corrected here.** Under `TCSlib`, only `WordRAM/Basic.lean`'s docstring line changed between them. The generator (`vendor.py`) also gained `EXTRA_IMPORTS` for M10 and the docstring-name restoration. |
| 7 (minor): the file map's line counts are one too high | **Resolved.** `evidence.py` now counts lines with `splitlines()`. The file map and the diff are regenerated at the gate-close head; the diff now also contains the finding-2 documentation lines. |
| 8–73 (notes) | Confirmed. As note 19 says, the closure check is a closure test, not a separate-module build; the replay supplies the latter. The replay of this round covers the gate-close edits. |

**Gate CLOSED.** The vendored programming layer is accepted as a faithful port of [AFM26]'s
41-module closure, with the listed modifications.
