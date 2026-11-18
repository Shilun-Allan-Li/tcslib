# EF-R1 · `ef-r1-gsw-reductions`: GSW's reduction machines; A1 and A3 unconditional

**Unit** `ef-r1-gsw-reductions` · **Route** Claude fill, a lead with up to 2 sub-agents on disjoint files · **Base**
EF1, the commit named in `EF-R1/base.md` at the records pin (a **stacked** base: the #377 merge B6 plus the accepted
EF-R2-R3 head, which sits on `iO/phase-a-base`) · **Size** 700–1,200 new Lean lines (±40%; audit §5.1) ·
**Delivery** `inbox/fills/ef-r1-gsw-reductions/` on `exchange/pass-shelat-ch5-8` · **Rulings** efficiency Q2 A (EF-R1
proves the predicates for every family, parameters as advice; A1/A3 unconditional by one-line wrappers; P6-Q10
superseded), Q10 A (TM tooling), rule 15 · **Local inputs (rule 16)** none.

Read `../COMMON.md` first; it is part of this brief. Then `../dup-sweep.md` §0 and §EF-R1 (binding must-reuse list),
and `briefs/efficiency-gaps/wave1/EF-R2-R3/brief.md` (the toolkit you reuse).

**If `EF-R1/base.md` says PENDING at the records pin, stop with E-BASE**: the base does not exist yet.

## Why a unit of its own (README Q-6BF-1 A)

- **It proves the predicates; it does not restate them.** `ReductionEfficient F` and `LeveledReductionEfficient F L`
  (`GSW/Asymptotic.lean:218`, `:246`) are definitions frozen by Gate 46; EF-R1 proves them as theorems for every
  `F : LWE.Family`, and A1/A3 (U18-U19's targets, statements unchanged) become unconditional through two one-line
  wrappers. Nothing in `Asymptotic.lean` changes.
- **Different base and tooling.** The machines need `NUPPT.RealizesOn` (`Asymptotic/Realization.lean`, #380, on the
  iO base) and the general-modulus arithmetic of EF-R2-R3 (wave 1, in progress); the six GSW proof units need neither
  and run now on B6.
- **File size.** `Asymptotic.lean` is 340 lines and U19 adds 150–280; EF-R1's 700–1,200 lines cannot go there under
  the 1,000-line limit.

## What the two predicates need (audit §3.3, refined)

Both predicates say: for every `NUPPT` `D` and bit `μ`, one `NUPPT` `D'` has, at every `κ`, DLWE advantage
`F.advantageAt D' κ` at least the advantage of the reduction run on `D_κ = D.distinguisherL κ ∘ encode`:
`reduction P_κ μ D_κ` (phase 5: encrypt `μ` under the challenge key with binary `R`, run `D`); and, for the leveled
form, every `levelReduction P_κ χ_κ L(κ) μ e j b D_κ` and both `reduction P_κ μ' (challengeDist …)`.

**Recommended route** (README Q-6BF-6 A; you may refine with disclosure):
1. **Averaging, then advice.** Each reduction's own coins (the binary `R`, `R₀`, the `Rs` of `hybridPlant`, and the
   leveled seeds `LeveledSeeds P χ L`, which hold uniform residues and `χ`-seeds) form a factor of its coin type
   apart from `D`'s coins `ρ`. `CommitmentLemmas.exists_fixCoins` (after regrouping with `acceptProb_comp_equiv`)
   gives a fixed value `c₀` of that factor whose fixed-coin reduction has at least the advantage. **No `χ` or uniform
   residue is ever sampled by a machine**, so no sampler bridge and no `EfficientFamily` is needed, and the theorem
   holds for every `F`.
2. **Worst index.** For the leveled form, the index set `Fin L(κ) × Fin N × Bool ⊕ Bool` is finite and nonempty (the
   challenge side); `Finset.exists_max_image` picks the index whose fixed-coin advantage is largest. One `D'` then
   dominates every index (r3 §H8 item 13).
3. **Deterministic pre-processing.** With `ω κ` = (parameters, chosen index, fixed coins and the encodings of every
   view part that does not depend on the challenge key), the fixed-coin reduction is `D` run on `pre κ (ω κ) x`, where
   `x` is the DLWE challenge. Every view here has the shape
   `prefix ++ enc(pk) ++ middle ++ (concatenation over t of encodeCiphertext (encrypt P pk μ_t R_t)) ++ suffix`
   with `pk` the challenge: phase-5 views (`prefix = middle = suffix = []`, one encryption), the level reduction
   (`pk` planted as `pk_{e+1}`; the `N` planted level-`e` ciphertexts by `hybridPlant_eq`: `0` before `j`, the
   challenge encryption at `j`, the key bits after `j`), the challenge reduction (`pk` as `pk_0`, one encryption last).
   `enc(pk)` is the challenge string itself (`encodeView`/`encodeLeveledView` use `LWE.encodeChallenge P.lwe P.width`,
   and `P.lwe = F.parameters κ`, `P.width = F.residueBits.eval κ` by the `ofFamily` readers).
4. **Realisation.** `NUPPT.exists_realizesOn_of_preTarget_id` with `A := D`, the polynomial-time target `f` (the
   splice map), the advice encoding and its length bound; `RealizesOn.distinguisherL_eq` and
   `RealizesOn.runAt_coinsEquivPoly_symm` identify `F.advantageAt D' κ` with the fixed-coin reduction's advantage
   (`LWE.Family.advantageAt_eq`, `PrivateKeyScheme.acceptProb_distinguisherL_congr` for the coin transport).
5. **Type-level transport.** The reductions are stated over `(Parameters.ofFamily F κ).lwe`, `advantageAt` over
   `F.parameters κ`. Read `ofFamily` only through `Parameters.ofFamily_lwe`/`_width` (Gate 46); a route that
   generalizes `Parameters.ofFamily F κ` to a `P` with `hP : P.lwe = F.parameters κ` and `cases`/`subst` on its fields
   is acceptable; unfolding `ofFamily` is not. If no reader-only route exists, that is **E-SCOPE** (a proposed
   reader), not an unfold.

## Targets (proposed; refine with disclosure, COMMON §4)

**Series 1, `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/EncryptPoly.lean`** (namespace
`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW`): the **uniform** string map of GSW encryption, usable later
by EF-H8 for honest encryption (COMMON §6):
- `def encryptStr : List Bool → List Bool`: on an input carrying `q`, `n`, `m`, `ℓ` (as numerals), the challenge-format
  key `LWE.encodeChallenge P.lwe P.width pk`, the bit `μ` and the coin matrix `R`, the string
  `encodeCiphertext P (encrypt P pk μ R)`: column `j` is the subset sum of the rows of `[A | b]` selected by
  `R_{·,j}` mod `q` (EF-R2-R3's `subsetSumModPoly` and the scalar `⟨b, r⟩ mod q`) plus `μ·G_{·,j}` (`vecAddModPoly`
  with the gadget column; `gadget_apply`), then transposed to `encodeMatrix`'s row-major order. Layout yours,
  documented; readers `encryptStr_eq` and an input-layout function with its `_length`.
- `theorem encryptStr_encode`: on the encoded input of `(P, pk, μ, R)`, `encryptStr … = encodeCiphertext P
  (encrypt P pk μ R)` (via `encrypt_eq`, `Regev.augmented`'s reader, `lift_apply`, `gadget_apply`, the toolkit's
  `encodeVector` correspondences, `encodeMatrix_eq`).
- `theorem polyTimeComputable_encryptStr : PolyTimeComputable encryptStr`.
- `def spliceStr` (the reductions' pre-processing target) with `spliceStr_eq` and `polyTimeComputable_spliceStr`:
  `⟨prefix, middle, suffix, (μ_t, R_t)_t, params⟩` and the challenge string `x` give
  `prefix ++ x ++ middle ++ (encryptStr of each (x, μ_t, R_t)) ++ suffix`.

**Series 2, `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/ReductionMachines.lean`** (same namespace):
- `theorem reductionEfficient (F : LWE.Family) : ReductionEfficient F`
- `theorem leveledReductionEfficient (F : LWE.Family) (L : PolyExpr) : LeveledReductionEfficient F L`
- `theorem indCPA_of_dlwe (F : LWE.Family) (hF : LWE.DLWEAssumption F) (hm : ∀ κ, ((F.parameters κ).dimension + 1) *
  F.residueBits.eval κ + 2 * κ ≤ (F.parameters κ).samples) (D : NUPPT) : Negligible fun κ => distAdv (realView
  (Parameters.ofFamily F κ) (F.noise κ) false) (realView (Parameters.ofFamily F κ) (F.noise κ) true) (fun v r =>
  D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r)`
  `:= indCPA_of_dlweAssumption F hF (reductionEfficient F) hm D` (A1's conclusion, without `heff`);
- `theorem leveledINDCPA_of_dlwe (F) (L) (hF) (hm) (D)` `:= leveledINDCPA_of_dlweAssumption F L hF
  (leveledReductionEfficient F L) hm D` (A3's conclusion, without `heff`);
- the string-level view lemmas the realisation needs (e.g. `encodeView` and `encodeLeveledView` of the fixed-coin
  views equal `spliceStr` of the advice and the challenge), public with readers, or private if only this file uses
  them.

Names as proposed (README Q-6BF-5 A). Docstrings: A1's and A3's tags for the wrappers ([GSW13, §3.2, p009-b002;
BV11, Def 3.1, p013-b002] and [BV14, Thm 3.7, p016-b001; BV11, Thm 3.1, p015-b001]); the predicates' theorems carry
[GSW13, §3.2, Lemma 1, p009-b002, p010-b001] for the reduction and [PS10, Definition 26.8] for non-uniformity, as
`LWE/Assumption.lean` and `Asymptotic/Realization.lean` cite it; the string maps are Glue.

## Files (create or change only these)

| File | Kind |
|---|---|
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/EncryptPoly.lean` | new (series 1) |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/ReductionMachines.lean` | new (series 2) |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean` | facade: two imports and their `## Contents` entries |

Frozen: everything else, in particular `GSW/Asymptotic.lean` (statements and definitions), EF-R2-R3's files
(`Encoding/ModularArithmetic.lean` and the Regev `Asymptotic` files: import, never edit), the iO-base files,
`ZeroKnowledge/CommitmentLemmas.lean` (a cleanup Stage 2 J6 owner: import read-only), and every GSW unit's file. A
missing reader in EF-R2-R3's toolkit is a scope request to Seyoon, not a local copy. **Disjointness** (maintainer,
`sweep/disjoint.txt`): the three paths are not Stage 2 owner paths, not changed on `cleanup/stage2-s2a`, and not
under any Arora–Barak or Ladner branch.

## Base and order

- EF1 = `tools/mkbase-ef-r1.sh <EF-R2-R3 head> [<gsw-6b-u18-u19 head>]` (deterministic; the maintainer runs it and
  records `BASE … tree …` in `EF-R1/base.md`). Reproduce it in your clone (fetch the heads `base.md` names; if a
  branch moved, fetch by hash) and stop with **E-BASE** on a different commit or tree.
- Compute the build order at EF1 with `tools/graph.py` and `tools/pins.py` (CHANGED = `GSW/Asymptotic`,
  `Encoding/ModularArithmetic`, `Asymptotic/Realization`, `ZeroKnowledge/CommitmentLemmas`, then the upstream closure),
  insert the two new modules after their last import and the facade after them, and record it in
  `evidence/build/order-final.txt` with its base admissions (C2's count: the base's set, unchanged).
- If EF1 contains U18-U19's final, **use `Parameters.ofFamily_columns_le`** for every `N ≤ (d(κ)+1)·ℓ(κ)` step; if
  not, a one-line private bound through `Parameters.columns_eq`, `ofFamily_lwe`, `ofFamily_width` and
  `F.dimension_le` is allowed, disclosed as the known twin of U18-U19's helper (the maintainer reconciles at landing).

## Axioms (C5)

- `reductionEfficient`, `leveledReductionEfficient`, series 1 and every helper: **standard axioms only** (the audit's
  R50/R51 become class M). Their proofs read only definitions (`reduction`, `levelReduction`, `challengeDist`, the
  encodings), never a 6b target.
- `indCPA_of_dlwe`, `leveledINDCPA_of_dlwe`: standard, plus `sorryAx` only through `indCPA_of_dlweAssumption` and
  `leveledINDCPA_of_dlweAssumption` (and their own allowed traces, U18-U19 brief) while EF1 lacks those fills.

## Checks and evidence (in addition to COMMON C1–C13)

- **C3.** decls2 on the facade: only the two imports and its docstring; the new files only ADDED. A `StmtDump` of
  every new public constant.
- **EF-P1 encryption probes:** `encryptStr` against `encodeCiphertext P (encrypt P pk μ R)` for `q ∈ {2, 3, 5, 8}`,
  `n ≤ 2`, `m ≤ 3`, `ℓ` minimal and minimal + 1, both bits, by kernel `decide` where it terminates, else `#eval`;
  malformed inputs total.
- **EF-P2 machine semantics:** for a toy family (`n = 1`, `m = 3`, `q = 5`, bit noise) and a toy `D`, `#eval` that the
  realiser's run on encoded challenges equals the fixed-coin reduction, for the phase-5 form and one level index.
- **EF-P3:** `#print axioms` of the four theorems, in the evidence.
- `REPORT.md` states, per predicate, the advice (contents and its length bound as a `PolyExpr`), the coin layout of
  `D'`, the averaging and worst-index steps, and the route taken for the `ofFamily` transport.

## Size and split

Series 1: 300–500; series 2: 400–700; total 700–1,200. Lead: series 2 and the integration. Sub-agent `enc`:
`EncryptPoly.lean`. Sub-agent `lev` (optional): the leveled string lemmas, in a section of `ReductionMachines.lean`
handed to the lead as a patch (the lead owns the file). Checkpoint 1: series 1 compiled with EF-P1, and
`reductionEfficient` proved.

**Not yet ready to dispatch — `EF-R1/base.md` is PENDING: EF-R2-R3's toolkit (series 1) must be accepted first, and
Q-6BF-1, Q-6BF-4 to Q-6BF-7 ruled** (README).
