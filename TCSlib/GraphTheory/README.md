# GraphTheory — layout

Bondy & Murty, *Graph Theory with Applications*, chapters 1–12.

Reorganized per `log/graphtheory-EXERCISE_TRIAGE.md` §F. Every declaration keeps its
book exercise/theorem number and its verbatim B&M statement — the move changed **where**
declarations live, never **what** they say.

```
Core/                 12 modules, one per chapter — THE RETRIEVAL SURFACE
Examples/              9 modules — witnesses, counterexamples, worked applications
Tests/                 1 module  — exact small values (regression tests)
Deferred/              7 modules — vacuous or undischargeable today; do not build on these
ExtractionArchive/     markdown manifest — declarations removed as Mathlib duplicates
book copy/             source markdown
```

## What goes where

| Directory | Contents | For an automated prover |
|---|---|---|
| `Core/` | definitions, numbered theorems, and the exercises carrying reusable inference steps, sharp thresholds, bridge lemmas or structural characterisations | **index this** |
| `Examples/` | facts about one specific graph/sequence/configuration: the Petersen graph, the mutilated chessboard, Graham's graph, sharpness witnesses | do not index — retrieving them can only help on goals about that same object |
| `Tests/` | exact values (`r(P₄,P₄) = 5`, `s₁ = 2`, `s₂ = 5`) | do not index — reference data, useful as `decide`/`Nat.card` regression tests |
| `Deferred/` | statements that are vacuous (quantify over a `def … := sorry`) or undischargeable (take a `Prop := sorry` hypothesis), plus two with unresolved source fidelity | **never cite** — in `Core/` these look like available API and are traps |

## Building

There is **no aggregator module**, and one cannot be written yet — see below. Build the
subtree with:

```bash
find TCSlib/GraphTheory -name '*.lean' \
  | sed 's|^TCSlib/|TCSlib.|; s|/|.|g; s|\.lean$||' \
  | xargs lake build
```

Individual modules build normally, e.g.
`lake build TCSlib.GraphTheory.Core.Trees`.

`TCSlib.lean` does **not** import this subtree, and that predates the reorganization —
the subtree is built on its own while `sorry`s remain.

## ⚠ Why there is no `TCSlib/GraphTheory.lean` aggregator

**12 declaration names are defined in more than one `Core/` chapter**, all in
`namespace SimpleGraph`. Any module importing two of the conflicting chapters fails
with `environment already contains …`:

| Name | Defined in |
|---|---|
| `IsVertexCut` | Connectivity, EulerHamilton, IndependentSetsCliques, PlanarGraphs, VertexColourings |
| `IsEdgeCut` | Connectivity, DirectedGraphs, Matchings, VertexColourings |
| `petersenGraph` | EdgeColourings, EulerHamilton, Matchings, PlanarGraphs |
| `vertexConnectivity` | Connectivity, EulerHamilton, PlanarGraphs |
| `edgeConnectivity` | Connectivity, Matchings, VertexColourings |
| `join` | EulerHamilton, IndependentSetsCliques, VertexColourings |
| `IsCutVertex` | Connectivity, Trees |
| `subdivide` | Connectivity, EdgeColourings |
| `numComponents` | EulerHamilton, Trees |
| `degreeSequence` | EulerHamilton, IndependentSetsCliques |
| `DegreeMajorised` | EulerHamilton, IndependentSetsCliques |
| `IsCovering` | IndependentSetsCliques, Matchings |

This was latent before the reorganization only because **no chapter file imported any
other** — every module was standalone, so the clashes never met. They are not new.

Two consequences:

1. **No aggregator.** `import`ing all of `Core/` is impossible until these are
   consolidated. The definitions also genuinely disagree in places — `petersenGraph` has
   two carriers *and* two `:= sorry` copies (triage §D.1), and `numComponents` is
   `Nat.card` in `Trees` but `Fintype.card` in the chapter-1 exercise (§D.3) — so
   consolidation requires mathematical decisions, not renaming.

2. **`Examples/`, `Tests/` and `Deferred/` are split by chapter, not by role.** The
   triage sketched role-based files (`Examples/Counterexamples.lean`,
   `Examples/Witnesses.lean`, …), but each would have to import several chapters at
   once and would hit the table above. Each file here imports **exactly one** `Core/`
   chapter, which sidesteps the clash entirely and preserves the property that actually
   matters: `Core/` is a clean retrieval surface and `Deferred/` is visibly separate.

   Regrouping by role is a mechanical follow-up once the 12 names are consolidated.

See `log/graphtheory-EXERCISE_TRIAGE.md` §D and §E for the consolidation decisions that
need a human.
