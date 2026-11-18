# EF-R2 + EF-R3 · Regev PKE and Regev symmetric: asymptotic security with `NUPPT` reduction machines

**Unit** `ef-r23-regev` · **Route** Claude fill (lead, up to 2 sub-agents on disjoint files) ·
**Base** IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (needs `Asymptotic/Realization`, #380) ·
**Size** 1,100–1,900 new Lean lines (±40%) · **Rulings** Q11 A (start now; statements over the raw
`LWE.Family`, which needs no honest efficiency), Q10 A (TM tooling), rule 15.

Read `../COMMON.md` first; it is part of this brief.

**Why one job for both** (Q-R-1 A). Both reductions need the same new piece: arithmetic modulo a
**general** `q` read from the reduction's advice, on the fixed-width residue encodings of
`Encoding/Modular` (EF-R3 adds a fixed codepoint vector mod `q`; EF-R2 adds a binary-selected subset of
rows and a codepoint mod `q`). No general-modulus vector arithmetic exists (only the dyadic
`Encoding/{DyadicArithmetic,DyadicLinearAlgebra}`). One owner writes it once, public, as series 1; EF-R3
(series 2) and EF-R2 (series 3) use it. Under Q-R-1 B the job splits at series 1 (see the end).

## Scope

Audit rows R43 (Regev symmetric `distAdv_encrypt_le`, `Encryption/Symmetric/Regev/Experiments.lean:116`)
and R44 (Regev PKE `distAdv_encrypt_le`, `Encryption/PublicKey/Regev/Experiments.lean:301`) are class
**F**: per-`Parameters` bounds for an arbitrary Lean function `D`, with no machine and no asymptotic
statement. This job adds, for each scheme, over an arbitrary `F : LWE.Family`:
1. the **reduction machine**: for every `NUPPT` distinguisher `D` of the encoded scheme views, a proved
   `NUPPT` `D'` whose DLWE advantage `F.advantageAt D' κ` is the function-level reduction's advantage on
   `D`'s verdict (parameters and messages as advice: reductions may be non-uniform);
2. the **asymptotic security statement**: `DLWEAssumption F` (and, for the PKE, the width condition)
   implies negligible advantage for every `NUPPT` distinguisher of the encoded views.
The honest algorithms' efficiency and the scheme instances (`PrivateKeyScheme`, `BitPublicKeyScheme` over
`LWE.EfficientFamily`) are EF-H5/EF-H6, later; this job states nothing about them.

## Targets (proposed; the worker may refine with disclosure)

**Series 1, `Encoding/ModularArithmetic.lean`** (namespace `TCSlib.Cryptography.Encoding.ModularArithmetic`):
public, polynomial-time string maps on `⟨q, ⟨u, v⟩⟩`-style pairs with the modulus `q` as an MSB numeral of
the residue width, and their correspondence lemmas with `Encoding.Modular.encodeVector`:
- `addModPoly`/`vecAddModPoly`: coordinatewise `(u + v) mod q` of two encoded vectors, with
  `vecAddModPoly_encodeVector : … = encodeVector w (u + v)` for `u v : Fin len → ZMod q`, `q ≤ 2^w`, and
  `polyTimeComputable_vecAddModPoly`;
- `subsetSumModPoly`: `Σ_{i : r_i = 1} A_i mod q` for an encoded matrix and a bit vector `r`, with
  `subsetSumModPoly_encode : … = encodeVector w (A.transpose.mulVec (fun i => (r i).toNat))` and its
  polynomial-time theorem; and the scalar `⟨b, r⟩ mod q`;
- built only from `BinArith.add`/`mod` (`ClassP/BinaryArith/{AddSub,Div}`), the `Encoding/BinaryArith`
  adapters and the registered loops (`BinArith.forLoop`, `Words` loops); the dyadic layers are the
  precedent, not a substitute (they reduce mod `2^W`).

**Series 2, `Encryption/Symmetric/Regev/Asymptotic.lean`** (namespace
`TCSlib.Cryptography.Encryption.Symmetric.Regev`; EF-R3):
- `theorem exists_shiftMachine (F : LWE.Family) (μ : ∀ κ, Fin (F.parameters κ).samples → Bool)
    (D : NUPPT) : ∃ D' : NUPPT, ∀ κ, LWE.decisionAdvantage (F.parameters κ) (F.noise κ)
      (fun c r => D.distinguisherL κ (LWE.encodeChallenge (F.parameters κ) (F.residueBits.eval κ)
        (shift (F.parameters κ) (μ κ) c)) r) = F.advantageAt D' κ`
  (or `≤`, disclosed): the shift adds the codepoints `codepoint P (μ_i)` to the value vector modulo `q`;
  `μ`, `n`, `m`, `q` are advice. Built with `NUPPT.exists_realizesOn_of_preTarget_id` and
  `RealizesOn.distinguisherL_eq`/`runAt_coinsEquivPoly_symm`.
- `theorem singleMessageSecure_of_dlweAssumption (F : LWE.Family) (hF : LWE.DLWEAssumption F)
    (D : NUPPT) : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ κ (μ₀ μ₁ : Fin (F.parameters κ).samples → Bool),
      distAdv (encryptDist (F.parameters κ) (F.noise κ) μ₀) (encryptDist (F.parameters κ) (F.noise κ) μ₁)
        (fun c r => D.distinguisherL κ (LWE.encodeChallenge (F.parameters κ) (F.residueBits.eval κ) c) r)
        ≤ ε κ`
  — the quantifier order of `PrivateKeyScheme.SingleMessageSecure` (`ε` before the messages); the proof
  fixes the worst pair at each `κ` as advice (a non-uniform reduction), then `distAdv_encrypt_le` and
  `exists_shiftMachine` twice.

**Series 3, `Encryption/PublicKey/Regev/Asymptotic.lean`** (namespace
`TCSlib.Cryptography.Encryption.PublicKey.Regev`; EF-R2):
- `def encodeView (P : Parameters) (w : ℕ) (v : …view type…) : List Bool` — the public key through
  `LWE.encodeChallenge P w`, the ciphertext through `Encoding.Modular.encodeVector w` and the residue
  numeral; readers `encodeView_eq`, `encodeView_length` (and injectivity if used).
- `theorem exists_reductionMachine (F : LWE.Family) (μ : Bool) (D : NUPPT) : ∃ D' : NUPPT, ∀ κ,
    LWE.decisionAdvantage (F.parameters κ) (F.noise κ) (reduction (F.parameters κ) μ
      (fun v r => D.distinguisherL κ (encodeView (F.parameters κ) (F.residueBits.eval κ) v) r))
      = F.advantageAt D' κ` (or `≤`): `D'` draws the `m` subset coins `r` as its own coins, computes
  `(Aᵀ r, ⟨b, r⟩ + codepoint μ) mod q` with series 1, re-encodes the view and runs `D`; this is exactly the
  `ReductionEfficient` content that #377 takes as a hypothesis for GSW, here **proved** for Regev.
- `theorem singleBitSecure_of_dlweAssumption (F : LWE.Family) (hF : LWE.DLWEAssumption F)
    (hm : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (F.parameters κ).samples) (D : NUPPT) :
    Negligible fun κ => distAdv (realView (F.parameters κ) (F.noise κ) false)
      (realView (F.parameters κ) (F.noise κ) true)
      (fun v r => D.distinguisherL κ (encodeView (F.parameters κ) (F.residueBits.eval κ) v) r)`
  — from `distAdv_encrypt_le`, `two_extractionError_le` (with `F.modulus_le_pow`), the two machines, and
  `Negligible.add`/`mono` with `negligible_two_pow_neg`. The width condition is #377 A1's `hm`, verbatim.

## Sources

- [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016, §5.2.1 (Regev's encryption
  and its hybrids) and Definition 4.2.3 — as the two `Experiments.lean` files cite them.
- [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024, Definition 20.5 and Lecture 21 (symmetric
  Regev and its two-hybrid bound) — as `Symmetric/Regev/Experiments.lean` cites them
  (`wu2024-topics-cryptography` ingested).
- [Vad12] Theorem 6.18 (leftover hash), through `extractionError` only.
- [PS10] Definitions 26.8 (non-uniform PPT reductions) and 91.1 (single-message security; the quantifier
  order), as `Encryption/PrivateKey/EnsembleSecurity.lean` cites it.
- The modular toolkit is Glue (machine representation; [AB09, §7.2] for the arithmetic machines, as
  `ClassP/BinaryArith.lean` cites it).

## Must reuse

- `NUPPT.RealizesOn`, `realizesOn_iff`, `RealizesOn.distinguisherL_eq`, `RealizesOn.runAt_coinsEquivPoly_symm`,
  `exists_realizesOn_of_preTarget`, `exists_realizesOn_of_preTarget_id`, `exists_realizesOn_reparam_pre_post`
  (`Asymptotic/Realization.lean`); `NUPPT.exists_reparam_pre_post` (`Asymptotic/UniversalLemmas.lean:79`);
  `NUPPT.exists_compParam` as the precedent (`Hashing/SIS/Asymptotic.lean:71` uses it the same way).
- `LWE.Family.advantageAt`, `advantageAt_eq`, `dlweAssumption_iff`, `encodeChallenge_length_le`,
  `LWE.encodeChallenge`, `encodeChallenge_eq`/`_length`/`_injective` (`LWE/{Assumption,Encoding}.lean`).
- Symmetric: `shift`, `shift_fst`/`_snd`, `encryptDist`, `encryptDist_eq_shift_sample`,
  `acceptProb_uniform_shift`, `distAdv_encrypt_le`. PKE: `view`, `realView`, `reduction`, `reduction_eq`,
  `real_uniformKey_advantage`, `distAdv_encrypt_le`, `two_extractionError_le`, `encrypt_fst`/`_snd`.
- `LWE.BitEncoding.codepoint`, `codepoint_eq`; `Encoding.Modular.encodeVector`/`encodeMatrix` with
  `_eq`, `_length`, `_injective`; `Encoding.ModularDecode` if decoding inside a machine is needed.
- `BinArith.add`/`mod`/`le` and readers, `polyTimeComputable_iterate`, `forLoop`, the `Words` loops,
  `Encoding.BinaryArith.{toLE,fromLEPoly,normalizeWidthPoly}`; `PrivateKeyScheme.acceptProb_distinguisherL_congr`
  for coin transport.
- `negligible_two_pow_neg`, `Negligible.add`, `Negligible.mono`, `negligible_polyExpr_mul`
  (`Asymptotic/EnsemblesLemmas.lean`).

## Duplication sweep (maintainer, static)

- No asymptotic statement and no `NUPPT` for either Regev scheme exists (`grep NUPPT` in both `Regev/`
  folders: 0 hits; audit R43/R44).
- General-modulus vector arithmetic: none. `Encoding/DyadicArithmetic` (`addPoly`, `mulPoly`, `subPoly`)
  and `Encoding/DyadicLinearAlgebra` (`dotPoly`, `matVecPoly`) reduce mod `2^W` only; `Hashing/SIS/hashPoly`
  is `matVecPoly` after bit expansion (dyadic). `Candidates.addStr`/`divModStr` compute plain add/divmod on
  numerals and are **being discharged by EF-H1 in parallel**: do not prove their polynomial-time
  theorems here (that would duplicate EF-H1), and EF-H1 does not write modular vector maps. If both jobs
  end up needing the same word-level reader, request it.
- #377 (`GSW/Asymptotic.lean`, head `7563734a`) has `encodeView`, `ReductionEfficient`, A1 for **GSW**: the
  Regev statements here are analogues in another namespace (disclose; reuse nothing private). The short
  name `encodeView` will exist in both namespaces: C10's shadow scan must show no resolution change.
- The non-uniform worst-message choice: the precedent is `NUPPT.exists_withAdvice` and the averaging in
  `Encryption/PrivateKey/FromPRG.lean` (`prgScheme_singleMessageSecure`): reuse its pattern, cite it.

## Files (create or change only these)

| File | Kind |
|---|---|
| `TCSlib/Cryptography/Encoding/ModularArithmetic.lean` | new (series 1) |
| `TCSlib/Cryptography/Encoding.lean` | facade: one import and its `## Contents` entry |
| `TCSlib/Cryptography/Encryption/Symmetric/Regev/Asymptotic.lean` | new (series 2) |
| `TCSlib/Cryptography/Encryption/Symmetric/Regev.lean` | facade line |
| `TCSlib/Cryptography/Encryption/PublicKey/Regev/Asymptotic.lean` | new (series 3) |
| `TCSlib/Cryptography/Encryption/PublicKey/Regev.lean` | facade line |

**Disjointness check (maintainer, mechanical).** None of the six paths is an owner file of
`scope.tsv`/`s2a-items.tsv`, changed on `cleanup/stage2-s2a`, touched by #376/#377, or under any
Arora–Barak/Ladner branch. Stage 2 owns `Encoding/{BooleanVector,DyadicUniform}.lean` (J2, proof-level
re-points), which this job may import read-only.

## Checks and evidence (in addition to COMMON C1–C13)

- **R-P1 toolkit probes**: `vecAddModPoly` and `subsetSumModPoly` against `ZMod` arithmetic for
  `q ∈ {2, 3, 5, 7, 8, 12}`, lengths ≤ 3, by kernel `decide` or `#eval` evidence; malformed inputs total.
- **R-P2 machine semantics**: for a toy `LWE.Family` (`n = 1`, `m = 2`, `q = 5`, bit noise) and a toy `D`,
  `#eval` that the realized machine's run equals the reduction function on sample encodings.
- **R-P3**: `#print axioms` of `singleMessageSecure_of_dlweAssumption` and `singleBitSecure_of_dlweAssumption`:
  standard only (the audit's R43/R44 become class **M**).
- `REPORT.md` states, for each scheme, the reduction's advice (what it contains and its length bound as a
  `PolyExpr`) and the coin layout of `D'`.

## Size

Toolkit 350–600; symmetric 300–500; PKE 450–800. Total 1,100–1,900.

## Questions for Seyoon

**Q-R-1. One worker or two.**
- **A (recommended).** One worker, three series as above: the toolkit is written once by its only first
  user.
- **B.** Two workers: EF-R3 dispatched first with series 1–2; EF-R2 dispatched on EF-R3's delivered head
  (its `<BASE>`), series 3 only. Slower; no file overlap either way.

**Q-R-2. Modulus generality.**
- **A (recommended).** General `q` (statements over every `LWE.Family`), since `DLWEAssumption` is stated
  for every family and EF-R1 (GSW) will need the same toolkit.
- **B.** Dyadic families only (`q = 2^{residueBits}` as a hypothesis), reusing the dyadic layers; the
  general case deferred.
