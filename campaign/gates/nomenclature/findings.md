# Stage-1 pre-audit sweep — findings (2026-10-01)

Scope: the merged chapter-6 surface (`Complexity/CircuitComplexity/`, 15
files) plus a hygiene look at the trees it touches
(`BooleanAnalysis/RazborovSmolensky/`, `Switching/`, `LMN/`). Baseline:
commit `286e08ba` (post-nomenclature-pass; the three rename commits
`88e15478`/`4046e553`/`9ab1a241` precede it). Items marked **[pre-audit]**
should be settled before the audit freezes names; **[anytime]** items are
cosmetic and can follow later. *Status markers updated 2026-10-01 after the
execution batch (catalog facade, registry carve-out, N4/N5/N6, DecisionTree
registration); items touching `Formulas.lean` are frozen while a colleague
works on that file concurrently.* All decisions rest with Seyoon and the
chapter-6 / BooleanAnalysis authors.

## 1. Verification attestations (facts, no action needed)

* **Axiom prints clean.** 30 headline theorems spanning all audit-scope
  files (every `InPPoly`/`InSIZE` headliner, the Shannon counting bound,
  the hierarchy theorem family, CKT-SAT and Tseitin lemmas, the encoding
  round-trips, the FeedForward↔tree conversions, the NC/AC inclusions,
  parity, UHALT, and `RazborovSmolensky.MODq_notin_AC0p_quantitative`)
  each depend on exactly `[propext, Classical.choice, Quot.sound]` — no
  `sorryAx` (kernel-level sorry-freedom) and no `ofReduceBool`
  (no `native_decide`).
* **No `native_decide` anywhere in scope.** A repo-wide grep finds it only
  in `CommunicationComplexity/` (five proof sites), outside the audit
  scope (see §5).
* **Compile baseline green.** The 23-module dependency sweep
  (`scripts/circuit_module_order.txt`) passes at the baseline commit.
* **Style lint:** `CircuitComplexity/` is at 0 FAIL / 0 WARN across all
  15 files; the RS tree's state is §2.

## 2. Razborov–Smolensky tree lint (decision: fix vs. record)

31 FAIL + 7 WARN, all pre-existing, breaking down as:

* 28 missing statement docstrings (ACpGates 12, CircuitDegree 9,
  SmolenskyAlgebra 3, LowDegreeObstruction 2, and the `gatePolyFamily`
  def family);
* 5 module docstrings lacking a `## References` section;
* 5 files missing the standard header options (WARN);
* 2 files over the 1000-line policy ceiling: `SmolenskyAlgebra.lean`
  (1182) and `LowDegreeObstruction.lean` (1091) — policy requires a split
  or a recorded justification.

**Decision (2026-10-01): record as accepted baseline** (default adopted);
the mechanical subset below remains on offer to the authors.

**Recommendation:** the RS tree is outside the proposed audit scope, so
none of this blocks the audit. Record the current counts as the accepted
baseline; offer the authors the mechanical subset (References sections,
header options — I can do those safely without touching proofs) and leave
the 28 statement docstrings and the two oversize files to them, with a
one-line justification in a decision log if they prefer not to split.

## 3. Nomenclature and organization findings

**N1. [TODO — frozen: colleague's concurrent Formulas.lean work] `Term` does double duty in `Formulas.lean`.**
`CNF n := List (Term n)` where `Term n` is documented as "a conjunction of
literals" [OD14, Def 4.1] — yet `CNF.evalClause` evaluates the very same
`Term` value *disjunctively*. Definitionally sound, but a genuine reader
trap at the heart of the switching development. *Proposal:* add
`abbrev Clause (n : ℕ) := List (Literal n)` and let `CNF n :=
List (Clause n)`; since `Term` and `Clause` would be definitionally equal
abbreviations, downstream LMN/Switching code keeps compiling unchanged and
signatures adopt the honest name opportunistically. Zero proof churn.

**N2. [PARTLY RESOLVED] Two root-namespace files, not one.**
*Resolution (decision trees):* `DecisionTree` is registered as a root model
type under the new `policy.md` §1 registry exception
(`TCSlib/ComputationalModels.lean`), and `buildFullDTree` moved into its
namespace as `DecisionTree.buildFull` (with `buildFull_depth`/`buildFull_eval`).
*Still TODO:* `dtDepth` remains a root-level *function* — deliberately
deferred because its name is baked into switching theorem names
(`switching_bernoulli_dtDepth_dnf`, …), the colleague's concurrent zone.
*Frozen:* the Formulas.lean half (candidate namespace: `BoolFormula`).
Original finding follows. Besides the known
`Formulas.lean` (`Literal`/`Term`/`DNF`/`CNF` at root; namespace choice
deliberately deferred), `DecisionTree.lean` also declares everything at
the root: the `DecisionTree` type, its `eval`/`depth`/`deepPath`, and the
free-floating `buildFullDTree`; `LMN/DecisionTreeFourier.lean` extends the
root `DecisionTree` namespace. *Proposal:* settle both homes in one
decision. A root *type* carrying its own namespace is standard Mathlib
practice, so one defensible outcome is: keep `DecisionTree` and the
formula types as root types, but (a) move `buildFullDTree` into the
`DecisionTree` namespace, and (b) record the policy-§1 exemption
explicitly. The alternative (a `Formula`/`Switching`-flavored namespace)
costs a ~20-file churn across LMN/Switching. Either way the names freeze
at audit time.

**N3. [RESOLVED — via the catalog] Three literal types, three CNF
types, two DNF notions.** The "which formula type is which" note now lives
in `TCSlib/ComputationalModels.lean`. `Literal n` / `BoolCircuit.Lit` /
`Std.Sat.Literal`; `CNF n` / `Std.Sat.CNF ℕ` / `NPReductions.CNFFormula`;
`DNF n` vs. the campaign's DNF fragment over `Std.Sat.CNF ℕ`. The
division of labor is defensible and already recorded (backlog §4); no
merging proposed. *Proposal:* a short "which formula type is which" note
(a paragraph in `lean-glossary.md` or a `Formulas`-adjacent README), so
the audit pack and future readers don't rediscover this.

**N4. [RESOLVED] `DecisionTree.lean` is in the wrong
tree.** Moved to `TCSlib/BooleanAnalysis/DecisionTree.lean`. Decision trees are not circuits, and the file's only consumers
are `BooleanAnalysis` (`Switching/Restriction`, `LMN/DecisionTreeFourier`)
plus the facade. *Proposal:* relocate to `BooleanAnalysis/` (the mirror
of the `FeedForward.lean` move, in the opposite direction). Doing it
before the audit keeps the audited file list equal to the actual AB09
chapter-6 surface.

**N5. [RESOLVED] Dangling `ch6/PLAN.md` references.** Repointed at
`backlog.md` §3; the stale pre-merge claims ("TCSlib has no machine model
and no class `P`") corrected in the same pass, and the dangling
`ch6/NOT_FORMALIZED.md` reference in NCAC.lean reworded. Three sites cite a
file that is not in the repository, by item ID: `UHalt.lean:36`,
`SizeClasses.lean:38` (both "U5"), `NCAC.lean:70`. An auditor will chase
these. *Proposal:* the authors either commit the plan or the references
get repointed at `backlog.md` §3 (which now tracks the same deferrals).

**N6. [RESOLVED] `SwitchingLemma2` is a versioned namespace with no
version 1.** Renamed to `SwitchingLemma` (27 Lean files, 276 blueprint
reference files). The generated `dep_graph.json` and `blueprint/lean_decls`
were healed with the full cumulative rename map — including 869 stale `ACP`
names the earlier unbundling pass had missed (erratum, disclosed here);
`blueprint_validate.py` reports 0 orphan labels. All seven `Switching/` files use it; no `SwitchingLemma`
namespace exists. Pure residue of a rewrite. *Proposal:* rename to
`SwitchingLemma` (or `Switching`) when convenient — colleague's call,
outside the audit scope.

**N7. [TODO] Draft-version references in prose.**
`LowDegreeObstruction.lean` refers three times to
`RazborovSmolenskyModqLowerBound_v19` / "`v19`" — a draft file not in the
repository. *Proposal:* reword to describe the split without naming the
dead draft.

**N8. [TODO] Minor structure.** `Hierarchy.lean` has two
`BoolCircuit` namespace blocks around a root-extension gap (could be
consolidated); `NCAC.lean` bundles family predicates, both classes, and
the fan-in simulation (optional split, previously noted); `Basic.lean` is
674 lines against the 600 target (INFO-level).

## 4. Checked and fine

No further class-named namespaces survive the ACP pass; casing
conventions hold throughout `CircuitComplexity/` (spot-checked);
`Language.uhalt` and friends follow the naming grammar;
`Nat.Partrec.Code.haltingSet` extending a Mathlib namespace is standard
practice; `NC_eq_AC` is correct for the union classes (NC^i ⊆ AC^i ⊆
NC^(i+1)) — at most worth a docstring note preempting reader surprise.

## 5. Out-of-scope observations (recorded, not proposed)

For the BooleanAnalysis owners, from the hygiene pass: three files have
no namespace at all (`polylogIndep.lean` — 20 root-level declarations and
a lowercase filename against the file-naming convention — `BLR.lean`,
`Hypercontractivity/Main.lean`); `polylogIndep.lean` additionally has
**no importers anywhere** (orphan module — it may not even be in the
build closure, depending on lakefile globs). And repo-level:
`CommunicationComplexity/` uses `native_decide` in five proofs, which
weakens the kernel-only trust story for that tree (fine if intentional;
worth a recorded note).
