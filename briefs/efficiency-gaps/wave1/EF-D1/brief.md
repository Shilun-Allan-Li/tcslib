# EF-D1 · `LWE.EfficientFamily` and `SIS.EfficientFamily`

**Unit** `ef-d1-lattice-families` · **Route** Claude (definitions with proved readers and non-vacuity;
a Codex gate reads the delivery before EF-H4 and the scheme instances build on it) ·
**Base** IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (needs `CoinSampling/Contract`) ·
**Size** 350–650 new Lean lines (±40%) · **Rulings** Q3 A, Q11 A.

Read `../COMMON.md` first; it is part of this brief.

## Scope

Ruling Q3 A: "`EfficientFamily extends Family` (uniform parameter map, noise sampler in the #378 contract
form); `DLWEAssumption`/`SISAssumption` stay on the raw `Family`; every scheme instance requires
`EfficientFamily`." Today `LWE.Family` (`LWE/Assumption.lean:65`), `LWE.Noise` (`LWE/Noise.lean:41`) and
`SIS.Family` (`SIS/Assumption.lean:66`) carry no efficiency (audit rows N4–N6; their docstrings say so).
This job adds the efficient structures **beside** them, without touching them:

1. `LWE.EfficientFamily extends LWE.Family`: a uniform parameter map `1^κ ↦ ⟨n, m, q⟩` and the noise
   sampler's efficiency in the `CoinSampling.SamplesEfficiently` form;
2. `SIS.EfficientFamily extends SIS.Family`: a uniform parameter map `1^κ ↦ ⟨n, m, q, β⟩`;
3. constructors for polynomially scheduled dyadic families (the form every TM-route instance of wave 1
   and EF-H4/H5–H7 will use), and one **non-vacuity instance** of each structure, with no hardness claim.

Uniform matrix and secret draws need no field: residues modulo a `q` read from the parameter word are
already efficient (`CoinSampling.samplesEfficiently_residue`), and dyadic matrices are coin
pass-throughs (`Encoding/DyadicUniform`).

## Targets (proposed; the worker may refine with disclosure)

**File A** `LWE/Efficient.lean`, namespace `TCSlib.Cryptography.LWE`:
- `def Parameters.encode (w : ℕ) (P : Parameters) : List Bool` — the parameter word, e.g.
  `⟨1^n, ⟨1^m, natToList w q⟩⟩` with `pairEncode`; readers `Parameters.encode_eq`, `encode_injective` on
  `q < 2^w` (or the `length` reader), as needed by the fields below.
- `def noiseWord (P : Parameters) (w : ℕ) (e : ℤ) : List Bool` — the encoded noise output consumed by
  honest algorithms; proposed: the residue `natToList w ((e : ZMod P.modulus).val)` (the honest algorithms
  only add `e mod q`). A sign-magnitude form is the alternative; choose one and disclose why.
- `structure EfficientFamily extends Family` with fields (names may change):
  - `params_uniform : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = (parameters κ).encode (residueBits.eval κ)`;
  - `encodeSeed : ∀ κ, (noise κ).Coins → List Bool`;
  - `noise_efficient : CoinSampling.SamplesEfficiently (P := fun _ => Unit)
      (fun κ _ => (parameters κ).encode (residueBits.eval κ)) (fun κ _ => encodeSeed κ)
      (fun κ _ e => noiseWord (parameters κ) (residueBits.eval κ) e) (fun κ _ => (noise κ).sample)`.
  The parameter word is the encoded public input the sampler reads (the contract's `y κ π`); the honest
  algorithms compose `params_uniform` in front of it.
- Readers only where a projection is not enough. **No assumption on `EfficientFamily`**: consumers write
  `DLWEAssumption F.toFamily` (an `EfficientFamily.DLWEAssumption` would restate `dlweAssumption_iff`,
  a G45-01 major).
- Constructors: `theorem params_uniform_of_schedule (N M W : PolyExpr) …` giving the `params_uniform`
  field for `n = N(κ)`, `m = M(κ)`, `q = 2^{W(κ)}` (W ≥ 1), and
  `theorem noise_efficient_of_bitNoise (t : PolyExpr) (f : …) (hf : PolyTimeComputable …)` for the
  bit-seed noise `bitNoise` (`LWE/BitNoise.lean:40`), whose seeds are fair coins (failure `0` with the
  bucket sampler at `N = 2^t`), and its `centeredNoise` instance (`BitNoise.lean:78`).
- Non-vacuity: `def dyadicExample : EfficientFamily` (for instance `n = κ + 1`, `m = 2(κ + 1)²` or any
  polynomial schedule, `q = 2^{κ+1}`, `χ = centeredNoise 1`), with a docstring that says **no hardness is
  claimed**.

**File B** `SIS/Efficient.lean`, namespace `TCSlib.Cryptography.SIS`:
- `def Parameters.encode (w b : ℕ) (P : Parameters) : List Bool` — `⟨1^n, ⟨1^m, ⟨q, β⟩⟩⟩` with `q` at
  width `w` and `β = sqNormBound` at width `b`; readers.
- `structure EfficientFamily extends Family` with `params_uniform : ∃ f, PolyTimeComputable f ∧
  ∀ κ, f (1^κ) = (parameters κ).encode (residueBits.eval κ) (magnitudeBits.eval κ)`.
- `theorem params_uniform_of_schedule` for polynomial `n`, `m`, `β` and dyadic `q`, and one non-vacuity
  instance (a small dyadic schedule defined here; **not** `Hashing.SIS.dyadicFamily`, whose module sits
  above `SIS/`: EF-H4 builds that instance).

## Sources

- [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016, Definitions 4.1.1 (SIS),
  4.2.1, 4.2.3 (LWE) — as `LWE/Assumption.lean` and `SIS/Assumption.lean` cite them (`peikert2016-lattice-survey`
  ingested).
- [PS10] Definition 23.4 (uniform PPT: one machine, uniform coins), Definition 26.8 (non-uniform PPT),
  as `CoinSampling/Contract.lean` cites them.
- The structures themselves are a repository convention (rule 15, ruling Q3 A): say so ("Glue: rule 15's
  efficiency-in-the-definition form; [Pei16] states the families without an efficiency clause").

## Must reuse

- `CoinSampling.SamplesEfficiently`, `samplesEfficiently_iff_exists`, `SamplesEfficiently.intro`,
  `DrawSamplable`, `CoreComputable`, `CoreComputable.map`, `bucketSampler`, `drawSamplable_residue`,
  `samplesEfficiently_residue`, `BoundedModulus`, `modulusWord`, `residueEnc`
  (`CoinSampling/{Contract,Efficiency,Buckets}.lean`), and `CoinSampling.CoinSampler.noiseSeeds`,
  `lweSeeds` (`CoinSampling/Instances.lean:95`, `:116`) for any seed-level statement.
- `LWE.bitNoise`, `bitNoise_Coins`, `bitNoise_sample`, `centeredNoise`, `centeredValue_eq`
  (`LWE/BitNoise.lean`); `Candidates.natToList`, `listToNat_natToList`.
- `EnsembleLemmas.polyTimeComputable_zeros` (`Asymptotic/EnsemblesLemmas.lean:212`),
  `CollectionsLemmas.polyTimeComputable_zerosPoly` (`:62`), `polyTimeComputable_polyUnary`
  (`TCSlib/Complexity/ClassNP/PolyTimePairing.lean:195`) for unary schedules; `BinArith` with the
  `Encoding/BinaryArith` adapters for the binary modulus word and for `centeredValue`'s core.

## Duplication sweep (maintainer, static)

- `EfficientFamily`, `Parameters.encode`, `noiseWord`: no declaration on any of the 280 remote heads.
- Parameter encodings: none exists for `LWE.Parameters` or `SIS.Parameters`; `LWE.encodeChallenge`,
  `SIS.encodeChallenge`, `SIS.encodeSolution` encode challenges and solutions, not parameters. The IO base
  has `CoinSampling.modulusWord` for a bounded modulus: reuse it for `q` if its `BoundedModulus` form fits,
  and disclose the choice.
- Noise samplers: `CoinSampling.CoinSampler.noiseSeeds` (seed-level, `Instances.lean:95`) is the coin
  sampler of a `Noise`'s seeds, not its efficiency; build on it, do not restate it. No `SamplesEfficiently`
  instance for `bitNoise` exists.
- Uniform schedules: no `PolyTimeComputable` lemma for a `PolyExpr`-indexed parameter word exists; the
  unary pieces above do.
- #377 adds `LWE.Family.RatioBounded` (`LWE/Ratio.lean:49`, head `7563734a`): unrelated, no clash.

## Files (create or change only these)

| File | Kind |
|---|---|
| `TCSlib/Cryptography/LWE/Efficient.lean` | new |
| `TCSlib/Cryptography/SIS/Efficient.lean` | new |
| `TCSlib/Cryptography/SIS.lean` | facade: one import and its `## Contents` entry |

**`TCSlib/Cryptography/LWE.lean` is not changed by this job.** #377 (`land/gsw-6b-statements`, head
`7563734a8badba842223e0687c719b3b4692e9d2`) changes that facade; the maintainer adds
`import TCSlib.Cryptography.LWE.Efficient` at landing, after #377 merges. Until then, the
`campaign_style_lint.py` facade-coverage line for `LWE/Efficient.lean` is an expected, disclosed WARN/FAIL
(C8: report it as the one allowed new line).

**Disjointness check (maintainer, mechanical).** `LWE/Efficient.lean`, `SIS/Efficient.lean` and `SIS.lean`
are not owner files of `scope.tsv`/`s2a-items.tsv`, not changed on `cleanup/stage2-s2a`, not touched by
#376/#377, and not under any Arora–Barak or Ladner branch. The only overlap found is the `LWE.lean` facade
with #377, excluded above.

## Checks and evidence (in addition to COMMON C1–C13)

- **D1-P1**: `dyadicExample` and the SIS instance elaborate; `#eval` of the parameter word at `κ ≤ 3`
  against the encoding.
- **D1-P2 consumer smoke test** (probe file): `fun (F : LWE.EfficientFamily) (h : LWE.DLWEAssumption F.toFamily)
  (D : NUPPT) => h D` and the same for SIS; an `LWE.EfficientFamily` passes where #377-style statements
  take `F : LWE.Family` (`F.toFamily`).
- **D1-P3**: the `noise_efficient` field of `dyadicExample` is proved, not assumed (C5 axioms clean).

## Size

Structures and encodings 120–200; `params_uniform_of_schedule` (LWE and SIS) 100–200; bit-noise sampler
efficiency 100–200; instances 30–50.

## Questions for Seyoon

None beyond the README's; the noise output form (residue or sign-magnitude) is left to the worker with
disclosure.
