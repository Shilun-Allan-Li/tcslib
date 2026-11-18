# EF-H12 sub-agent rules (binding; from COMMON.md §3–§5 and policy.md)

You are a sub-agent of the EF-H12 fill (Levin reduction of every witness relation to 3-colouring,
Lean 4.25.0 + pinned Mathlib). The lead owns git commits, lake and the Mathlib cache.

## Your environment
- Your worktree: `/home/user/work/wt-<X>` (sparse: `TCSlib/`, `scripts/`, top-level files), branch
  `sub/<X>`, `.lake/packages` symlinked to the lead's. **Never run `lake` (no `lake build`, no
  `lake exe cache get`), never `git commit`/`push`.** Edit only the file(s) you own.
- Your olean tree: `/home/user/work/ol-<X>` (already holds every base module and `Relations`).
- Compile ONE module (path without `.lean`), always through the shared pool (3 slots for all agents):
  `TCSLIB_OLEANS=/home/user/work/ol-<X> /home/user/work/tools/lean_slot.sh /home/user/work/wt-<X> TCSlib/Cryptography/ZeroKnowledge/LevinHardness/<File> 2>&1 | tee -a /home/user/work/ev/evidence/subagents/<X>/build.log | tail -40`
  Pass = exit 0, no `error:` lines. Do not wrap checks in short timeouts. Never `pkill -f`.
  For quick experiments, write a scratch file under `/home/user/work/wt-<X>/scratch/` (e.g.
  `scratch/Probe.lean`, module path `scratch/Probe`) and compile it the same way; delete it after.
  `#check`, `#print`, `example`, `exact?` in a scratch file are the way to look things up.
- Run Python as `python3 -I`. Keep notes/logs in `/home/user/work/ev/evidence/subagents/<X>/`.

## Lean rules (reviewers check these mechanically)
1. **Rule 10 (no unfolding foreign definitions).** Any definition from another file — every TCSlib
   file, including the lead's `Relations.lean` and any other `LevinHardness/` file — is read ONLY
   through its published lemmas (`*_eq`, `*_iff`, `*_def`, case lemmas, spec theorems). Never
   `unfold X`, `simp [X]`, `rw [X]`, `X.eq_1`, `delta`, nor let `rfl`/`show`/`change`/`decide`/
   anonymous-constructor elaboration see through a TCSlib definition from another file. (Reviewers
   seal every foreign TCSlib definition with `attribute [local irreducible]` and recompile.) Core /
   Std / Mathlib definitions may reduce in `rfl`/`decide`/`show`, but are passed to `simp`/`rw`/
   `unfold` only through their equation lemmas (`List.getD_eq_getElem?_getD`, `Std.Sat.CNF.eval_cons`,
   …). Your OWN file's definitions you may unfold freely, but every public `def` must land with its
   reader (`foo_eq : foo x = <body> := rfl`, or `_iff`, or case lemmas) — consumers use those.
   If you need a foreign reader that does not exist, STOP using that definition and report it as
   MISSING (proposed one-line reader) — do not work around by unfolding.
   Known MISSING readers (do not use these definitions' bodies): `Complexity.SAT3`,
   `BoolCircuit.DAGCircuit.Satisfiable`, `Std.Sat.CNF.WidthAtMost` (TCSlib, Formulas/CNF.lean),
   everything in `Complexity/NPReductions/ThreeSATToColoring.lean`.
2. **Duplication.** Before stating any definition or lemma, search TCSlib/Mathlib/Std for it
   (`grep -rn`, `exact?`). Never restate a public lemma; never re-prove a TCSlib/Mathlib fact inline;
   cite it. Every near-relative you knowingly specialize goes in your report with `path:line`.
3. **Hosts first.** No private loop/search/recursion machinery. Build machines only from public
   `PolyTimeComputable` combinators (`.comp`, `.pairEncode`, `.append`, `polyTimeComputable_ite`,
   `polyTimeComputable_and/or/not`, `polyTimeComputable_transduce`, the `BinArith` rows,
   `polyTimeComputable_unary_*`, `ComposeMachines.polyTimeComputable_flatMap_range`
   (`TCSlib/Cryptography/SecureComputation/ComposeSecurity/Machines.lean:81`, the tabulation host),
   `polyTimeComputable_forLoop`, `polyTimeComputable_iterate`, …). Pitfall: state `PolyTimeComputable`
   goals in applied form (`fun z => f (g z)`), and prove extensional equality with `.congr` /
   `funext` against a reader rather than letting unification unfold string functions.
4. **Form.** File header exactly like `LevinHardness/Relations.lean` (copyright block, precise
   imports — never bare `import Mathlib`, the three `set_option` lines, a module docstring with
   `# Title`, `## Main definitions`, `## Main results`, `## References`). Namespace
   `TCSlib.Cryptography.LevinHardness`. Every public declaration has a docstring that opens with a
   natural-language statement including its formula; every proof of ≥ ~20 lines has a
   `**Proof sketch.**` paragraph in its docstring. Glue lemmas say "Glue." and carry no citation.
   Cite only: [AB09] Arora–Barak (Def 6.9, Lemmas 6.10/6.11 p. 111, Remark 6.7, Def 2.7, Thm 2.10,
   "[AB09, §2.3]"), [PS10] Pass–shelat §4.7 Thm 124.1 step 2, and the course material
   `ThreeSATToColoring.lean` (CS 294-268, UC Berkeley, Spring 2026) for the 3SAT→3COL gadget.
   Never invent quotations, page or theorem numbers. Lines ≤ 100 chars; file < 1000 lines (split
   into a second owned file only if the lead agrees); no new `@[simp]`; no `sorry`, `admit`,
   `native_decide`, `axiom`, `opaque`; `private` only for genuinely file-local glue (never a host,
   never something another file would need).
5. **Efficiency.** Every honest map must come with `PolyTimeComputable` of the explicit string map.

## Reporting
When done (or blocked), write `/home/user/work/ev/evidence/subagents/<X>/REPORT.md`: the final list
of public declarations with one-line statements, the foreign readers used (`name — path:line`),
MISSING readers, overlaps/near-relatives with `path:line`, the last compile's result, and anything
unfinished. Your final message to the lead should summarize the same briefly.
