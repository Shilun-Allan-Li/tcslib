# EF-D4 · `LossyTDF` and `ABOTDF` interfaces, efficiency in the definition

**Unit** `ef-d4-ltdf-interfaces` · **Route** Claude statement job (definitions, readers and small proved
sanity theorems; no admitted targets), then a Codex gate before EF-H9/EF-R4/EF-R5 build on it ·
**Base** REC `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62` · **Size** 300–500 new Lean lines (±40%) ·
**Rulings** Q9 A, Q1 A, Q11 A.

Read `../COMMON.md` first; it is part of this brief.

## Scope

Nothing in TCSlib defines lossy or all-but-one trapdoor functions as primitives (audit rows N10, N11, R47):
`TrapdoorFunctions/Lossy/*` and `TrapdoorFunctions/AllButOne/*` are the [PW10] §6.2–§6.4 lattice
mathematics, with function-level hybrids only. Ruling Q9 A: define the interfaces now, efficiency in the
definition, "so that the lossy and ABO results have a primitive to land in". This job writes the two
interfaces as structures whose honest algorithms carry their uniform efficiency as fields (class E·s), and
their correctness, lossiness and indistinguishability predicates over `NUPPT`. No instance is built here
(EF-H9), and no lattice file changes.

## Targets (proposed; the worker may refine with disclosure)

**File** `TrapdoorFunctions/Defs.lean`, namespace `TCSlib.Cryptography.TrapdoorFunctions`. Follow the
conventions of `Collection`/`TrapdoorCollection` (`Asymptotic/Collections.lean:128`, `:374`) and `CRH`
(`Hashing/CollisionResistant.lean:56`): generators are uniform `NUPPT`s run as `gen.runAt n [] r` with
`pairFstD`/`pairSndD` outputs, evaluators are `PolyTimeComputable` string maps on `⟨1^n, …⟩`
(`atParam`), domains are `Fin (inLen.eval n) → Bool`.

1. `structure LossyTDF` — an `(n, k)`-lossy trapdoor function [PW10, §3.1]:
   - `inLen lossBits : PolyExpr` (input length `n(κ)`, lossiness `k(κ)`);
   - `genInj genLoss : NUPPT` (injective-mode generator outputs `⟨s, t⟩`; lossy-mode generator outputs a
     function index `s`), `genInj_uniform : genInj.Uniform`, `genLoss_uniform : genLoss.Uniform`;
   - `eval inv : List Bool → List Bool` (`⟨1^n, ⟨s, x⟩⟩ ↦ F_s(x)`, `⟨1^n, ⟨t, y⟩⟩ ↦ x`),
     `eval_poly : PolyTimeComputable eval`, `inv_poly : PolyTimeComputable inv`.
   With `LossyTDF.fn n s x`, the evaluation read back (reader `fn_eq`), and the predicates:
   - `LossyTDF.Correct`: for every `n`, every injective-mode coin string and every `x`, `inv` on the
     trapdoor and `fn n s x` returns `List.ofFn x` (perfect, every coin string, as
     `TrapdoorCollection.inv_spec`); disclose any weaker variant you choose;
   - `LossyTDF.Lossy`: for every `n` and every lossy-mode coin string, the image of `fn n s` has at most
     `2^{n(κ) − k(κ)}` elements;
   - `LossyTDF.ModesIndist`: every `NUPPT` `D` has negligible advantage between the function indices of
     the two modes (`Negligible fun n => distAdv … (D.distinguisherL n)`);
   - `LossyTDF.Secure := Correct ∧ Lossy ∧ ModesIndist`, with `_iff` readers for each.
2. `structure ABOTDF` — an all-but-one trapdoor function with branch set `{0,1}^{b(κ)}` [PW10, §3.2]:
   - `inLen lossBits branchLen : PolyExpr`; `gen : NUPPT` run on the lossy branch `b*`
     (`gen.runAt n (List.ofFn b*) r = ⟨s, t⟩`), `gen_uniform`; `eval inv` on `⟨1^n, ⟨s, ⟨b, x⟩⟩⟩` and
     `⟨1^n, ⟨t, ⟨b, y⟩⟩⟩` with `eval_poly`, `inv_poly`.
   Predicates `ABOTDF.Correct` (every branch `b ≠ b*` is inverted), `ABOTDF.Lossy` (the branch `b*` has
   image at most `2^{n − k}`), `ABOTDF.HiddenBranch` (for every `NUPPT` `D` there is a negligible `ε` with,
   for all `n` and all `b₀*, b₁*`, the advantage between the function indices generated for `b₀*` and for
   `b₁*` at most `ε n`: the quantifier order of `PrivateKeyScheme.SingleMessageSecure`), and
   `ABOTDF.Secure`, with readers.
3. **Sanity theorems (proved)**: `LossyTDF.fn_injective_of_correct` (correctness makes every
   injective-mode function injective), the analogue for ABO branches `b ≠ b*`, and
   `LossyTDF.lossy_card_lt` (for `k ≥ 1` the lossy image is strictly smaller than the domain), so the
   predicates are visibly non-trivial. Optional, only if the ingested source supports it after Q-D4-1:
   an ABO with a one-bit branch set gives a `LossyTDF` (the lossy branch `b* = 1`) — skip it otherwise.

## Sources

- [PW10] C. Peikert, B. Waters, *Lossy Trapdoor Functions and Their Applications*, author version dated
  4 June 2010: §3.1 (lossy TDFs) and §3.2 (all-but-one TDFs) for the definitions. **The ingested reference
  `peikert-waters-2010-lossy-tdf` covers printed pages 33–39 only (§6.2–§6.4)**; §3 is not ingested (see
  Q-D4-1). Cite §6.2–§6.4 anchors (`pdf-74f48b0eff6f-p033-b001` …) only for remarks about the lattice
  instances.
- [PS10] Definitions 26.8 (`NUPPT`) and 23.4 (uniform PPT); the `Collection` and `TrapdoorCollection`
  conventions ([PS10] Definitions 55.1, 56.1) as `Asymptotic/Collections.lean` cites them.

## Must reuse

- `NUPPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `distinguisherL`, `distAdv`, `Negligible`, `atParam`,
  `padFin`, `pairEncode`/`pairFstD`/`pairSndD` with their readers; `Ensemble.Indist` if the
  indistinguishability predicates are stated through ensembles (`Asymptotic/Ensembles.lean:182`) — choose
  one form and state why.
- The conventions (and nothing private) of `Collection`, `TrapdoorCollection`, `CRH`.

## Duplication sweep (maintainer, static)

- `LossyTDF`, `ABOTDF`, `AllButOneTDF`, `lossy`/`branch` interfaces: none on any of the 280 remote heads.
- Near-relatives: `TrapdoorCollection` (permutations, `Asymptotic/Collections.lean:374`) — an LTDF in
  injective mode is an injective trapdoor function, not a permutation, so it is not an instance; state no
  bridge here. `Lossy/Matrix.lean` `conceal`/`evaluate`/`injectiveKey`/`recover` (`:46`, `:60`, `:92`,
  `:110`) and `AllButOne/Basic.lean` `allButOneKey`/`evaluateBranch` (`:59`, `:80`) are the future
  instances' mathematics: do not restate them.
- `CRH.Compresses` (`Hashing/CollisionResistant.lean`) uses `Fintype.card {y // …}`; use the same
  counting idiom for `Lossy` rather than a new cardinality helper.

## Files (create or change only these)

| File | Kind |
|---|---|
| `TCSlib/Cryptography/TrapdoorFunctions/Defs.lean` | new |
| `TCSlib/Cryptography/TrapdoorFunctions.lean` | facade: one import and its `## Contents` entry |

**Disjointness check (maintainer, mechanical).** Neither path is an owner file of `scope.tsv`/`s2a-items.tsv`,
changed on `cleanup/stage2-s2a`, touched by #376/#377, or under any Arora–Barak/Ladner branch. Read-only
imports owned by Stage 2: `Asymptotic/Collections.lean`, `Asymptotic/Ensembles.lean`,
`Hashing/CollisionResistant.lean` (J0/J2: readers added and proofs re-pointed; no statement change to the
declarations used here, except `Ensemble.copies_X`, which this job does not use).

## Checks and evidence (in addition to COMMON C1–C13)

- **D4-P1 non-vacuity of the types**: a toy `LossyTDF` value in a probe file (identity evaluation on
  `inLen = var`, `lossBits = 0`, constant generators) elaborates and satisfies `Correct` and `Lossy`;
  `ModesIndist` is then trivially true (identical modes), which the probe states as a sanity remark only.
- **D4-P2**: the same for `ABOTDF` with `branchLen = 1`.
- **Gate preparation**: `REPORT.md` lists every definition with its readers and every design choice made
  against the [PW10] definitions (perfect versus negligible correctness error, the key/trapdoor layout, the
  form of indistinguishability), each marked as a question if it departs from [PW10].

## Size

`LossyTDF` with predicates and readers 120–200; `ABOTDF` 120–200; sanity theorems 50–100.

## Questions for Seyoon

**Q-D4-1. Source for the definitions.**
- **A (recommended).** Before dispatch, the maintainer extends the [PW10] ingestion to §3.1–§3.2 (the
  definitions), and the worker cites those anchors.
- **B.** Dispatch now; the worker cites [PW10, §3.1, §3.2] by section only, with no excerpt anchors and a
  disclosure, and the gate checks the wording against the author PDF.
