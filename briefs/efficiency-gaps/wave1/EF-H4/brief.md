# EF-H4 · The dyadic SIS hash as a `CRH` instance

**Unit** `ef-h4-sis-crh` · **Route** Claude fill (one worker) · **Base** `<BASE>` = EF-D1's delivered final
head on IO (`5ed465f62e4ae0f93ded1a1ba49e807591b589eb` plus the `ef-d1-lattice-families` series, after the
maintainer's review of it; or the records commit where EF-D1 lands, if it lands first) ·
**Size** 400–750 new Lean lines (±40%) · **Rulings** Q3 A ("every scheme instance requires
`EfficientFamily`"), Q11 A ("then EF-H4"), rule 15. **Depends on** EF-D1 (`SIS.EfficientFamily`).

Read `../COMMON.md` first; it is part of this brief.

## Scope

The SIS hash is collision resistant in raw form only (audit R49, class M): `negligible_collisions_of_SIS`
(`Hashing/SIS/Asymptotic.lean:71`) and `dyadic_collision_negligible` (`:116`) bound `collisionAt`, a raw
experiment; there is no `CRH` value (audit N13; `Hashing/SIS.lean:32–33`). Its evaluator is already
polynomial-time (`polyTimeComputable_hashPoly`, `Hashing/SIS/Implementation.lean:89`), and at modulus
`2^W` its key generator is a pass-through of `N·M·W` fair coins (exact law, `Encoding/DyadicUniform`).
This job builds the `CRH` (`Hashing/CollisionResistant.lean:56`, class E·s) from an
`SIS.EfficientFamily` with dyadic modulus and exact polynomial schedules, proves compression and collision
resistance from `SISAssumption`, and instantiates it at the explicit dyadic profile.

## Targets (proposed; the worker may refine with disclosure)

File `Hashing/SIS/CRH.lean`, namespace `TCSlib.Cryptography.Hashing.SIS`:
- `def sisCRH (F : SIS.EfficientFamily) (N M W : PolyExpr) (hN : ∀ κ, (F.parameters κ).dimension = N.eval κ)
    (hM : ∀ κ, (F.parameters κ).columns = M.eval κ) (hW : ∀ κ, F.residueBits.eval κ = W.eval κ)
    (hq : ∀ κ, (F.parameters κ).modulus = 2 ^ W.eval κ) : CRH` (hypotheses as fields of a small
  `DyadicSchedule F` structure if cleaner) with `domLen := M`, `rangeLen := N * W`,
  `gen := NUPPT.ofPolyTimeUniform …` writing its `N·M·W` coins as the matrix encoding,
  `eval := hashPoly N M W` (the CRH input `atParam n ⟨i, x⟩ = ⟨1^n, ⟨i, x⟩⟩` is `hashPoly`'s layout),
  `inDom`/`inRange` everywhere `true`; readers for every field use.
- `theorem sisCRH_gen_runAt` (the generated index is `SIS.encodeChallenge … (bitsToMatrix …)` of the
  coins) and `theorem sisCRH_hash` (the hash is `encodeVector` of `A·x` mod `2^W`, from
  `hashPoly_encodeMatrix`).
- `theorem sisCRH_compresses (…) (hcomp : ∀ κ, N.eval κ * W.eval κ < M.eval κ) : (sisCRH …).Compresses`.
- `theorem sisCRH_collisionResistant (…) (hbound : ∀ κ, (F.parameters κ).columns ≤ (F.parameters κ).sqNormBound)
    (hwidth : ∀ κ, 0 < F.magnitudeBits.eval κ) (hSIS : SIS.SISAssumption F.toFamily) :
    (sisCRH …).CollisionResistant` — the collision game equals (or is bounded by) `collisionAt` under the
  coin law `bitsToMatrix_uniform`, then `negligible_collisions_of_SIS`.
- `def dyadicEfficientFamily : SIS.EfficientFamily` with `toFamily = dyadicFamily`
  (`Hashing/SIS/Profiles.lean:79`), its `params_uniform` from EF-D1's schedule constructor; and the
  corollaries `dyadicCRH : CRH`, `dyadicCRH_compresses`,
  `dyadicCRH_collisionResistant (hSIS : SIS.SISAssumption dyadicFamily)`.

## Sources

- [PS10] Definition 140.1 (CRH: ease of sampling and evaluation, compression, collision resistance), as
  `Hashing/CollisionResistant.lean` cites it.
- [Pei16] Equation (4.1.1) and the observations after it, §5.1 (the SIS hash and its collision
  resistance), as `Hashing/SIS/{Implementation,Asymptotic,Profiles}.lean` cite them.

## Must reuse

- `CRH`, `CRH.hash`, `hash_eq`, `Compresses`, `compresses_iff`, `collisionGame`, `collisionGame_eq`,
  `CollisionResistant`, `collisionResistant_iff`; the instance precedent `dlHash`
  (`Hashing/FromDiscreteLog.lean:451`) for structure and coin equivalences (`dlHash_coinsEquiv`).
- `hashPoly`, `hashPoly_eq`, `hashPoly_length`, `hashPoly_encodeMatrix`, `polyTimeComputable_hashPoly`;
  `collisionAt`, `collisionAt_eq`, `negligible_collisions_of_SIS`, `dyadic_collision_negligible`;
  `rawCollisionInputs` (`Hashing/SIS/CollisionOutput.lean:54`) and its readers; `dyadicFamily`,
  `dyadicParameters` and their `simps` readers, `dyadic_*` profile lemmas.
- `Encoding.DyadicUniform.bitsToMatrix`, `bitsToMatrix_uniform`, `encode_bitsToMatrix`;
  `SIS.encodeChallenge`; `NUPPT.ofPolyTimeUniform`, `ofPolyTimeUniform_uniform`,
  `coinsEquiv_ofPolyTimeUniform`, `coinsEquiv_ofPolyTimeUniform_ofFn`; `PrivateKeyScheme`-style coin
  transport (`acceptProb_distinguisherL_congr`) where useful.
- From EF-D1: `SIS.EfficientFamily`, `SIS.Parameters.encode`, `params_uniform_of_schedule`.

## Duplication sweep (maintainer, static)

- No `CRH` value from SIS exists on any remote head (grep `: CRH` gives only `dlHash`); `Hashing/SIS.lean`
  says "This adds no generic CRH contract".
- The collision reduction already exists as `negligible_collisions_of_SIS` (a proved `NUPPT` machine via
  `exists_compParam`): reuse it; do **not** build a second collision-finder machine. Only the transport
  between `collisionGame` (index from `gen`'s coins, `splitBits (padFin (d+d) …)`) and `collisionAt`
  (uniform matrix, `rawCollisionInputs`) is new; if the two splitting conventions differ, prove the
  inequality you need and disclose.
- Compression: no SIS-specific counting lemma for `CRH.Compresses` exists; `Hashing/SIS/Basic.lean`
  `cardinal_compression` (`:123`) and `dyadic_cardinal_compression` (`Profiles.lean:123`) are the
  mathematical relatives: reuse them where their statements fit.

## Files (create or change only these)

| File | Kind |
|---|---|
| `TCSlib/Cryptography/Hashing/SIS/CRH.lean` | new |
| `TCSlib/Cryptography/Hashing/SIS.lean` | facade: one import and its `## Contents` entry (its "adds no generic CRH contract" sentence may be updated, docstring only) |

**Disjointness check (maintainer, mechanical).** Neither path is an owner file of `scope.tsv`/`s2a-items.tsv`
(J2 owns `Hashing/SIS/CollisionOutput.lean` and `Hashing/CollisionResistant.lean`, docstring and proof-level
items only: imported read-only here), changed on `cleanup/stage2-s2a`, touched by #376/#377, or under any
Arora–Barak/Ladner branch, and neither is an EF-D1 file.

## Checks and evidence (in addition to COMMON C1–C13)

- **H4-P1**: `dyadicCRH` at `κ ∈ {0, 1}`: `#eval` the hash of a toy matrix and input against
  `A·x mod 2^{κ+1}`.
- **H4-P2**: `#print axioms dyadicCRH_collisionResistant`: standard only (the SIS hash becomes a `CRH`
  under `SISAssumption dyadicFamily`, class M).

## Size

`sisCRH` with readers 150–250; compression 60–120; collision resistance transport 150–300;
dyadic instance and corollaries 40–80.

## Questions for Seyoon

None. (The dependency on EF-D1 is sequencing, recorded in the README.)
