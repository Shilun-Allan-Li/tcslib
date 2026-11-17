# gsw-6b-statements · final (Claude, lead + 2 sub-agents)

**Heads (full hashes).**
- Series 1 `owner/o2-decode`: **`5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd`** (1 commit, O2).
- Series 2 `stmt/gsw-6b`: **`8f92fe7d53967bc488a4075fb38210e7d40b9031`**, five commits on O2:

| # | Commit | Content |
|---|---|---|
| 1 | `7a8145468202f908f6a1e41638fc793c2313b850` | `GSW/Branching` (G1–G3), `GSW/DecryptFormula` (G5–G8) |
| 2 | `dd9f00f484a7e89390ce8a68b19cac773fb6f9b1` | `GSW/Bootstrap` (G9–G13, G18), `GSW/Circular` (G14–G15) |
| 3 | `1378740f5f516f8047fd9cf83e56414091dde8af` | `GSW/Leveled` (L1–L3), `GSW/LeveledSecurity` (L4–L5) |
| 4 | `5c8f81cdd83aca13d737cea3fd0d03fb37d9f9b8` | `LWE/Ratio`, `GSW/PolyRatio` (G16–G17), `GSW/Asymptotic` (A1–A3) |
| 5 | `8f92fe7d53967bc488a4075fb38210e7d40b9031` | facades `GSW.lean`, `LWE.lean` |

- Base **`3e51b5f28900db6190f1eb2e6d207d27ee15d541`** (tree `b69a66a385ca3439d56af1d6b9791b5847984fde`), unchanged.
- Checkpoint 1 (exchange `1e0647b99de8ee4d11722b5bad862fe40837a2ce`) had O2 at `dd84941f…` and the statement head
  `57815173…`. Both series were **rebuilt after the maintainer's checkpoint review** (§ *Checkpoint review*):
  the O2 commit was amended and the statement series rebased; the earlier heads are superseded.

## 1. Base, inputs, records tip

- `tools/mkbase.sh` (fresh clone; `land/gsw-6a-statements` and `land/gsw-6a-readers` at their pinned heads):
  `STEP1 04947bcf35e08ed5f3a4902b2637a77482fd32d2 tree 8eca961769fef59d5a22fd1b46dc821a614daf06`,
  `BASE 3e51b5f28900db6190f1eb2e6d207d27ee15d541 tree b69a66a385ca3439d56af1d6b9791b5847984fde`
  (`evidence/logs/mkbase.log`).
- Pack: `SHA256SUMS` 25/25, `inputs/SHA256SUMS` 8/8. Records inputs at `e913abe549843088a6cddf541b24e94a2d316f23`
  match the brief (`evidence/records/SHA256-at-e913abe5.txt`). The records branch notes **Q-6B-1 ruled A
  (reader-only)**, applied here.
- **Records tip at delivery** `523c1c5517cfd418214a3e6a5a894569e1664749` (#347 and #355 merged since staging).
  `git merge-tree --write-tree 523c1c55… 8f92fe7d…` is clean, tree `ac7ce43159d2c73572ea75e7c4e157f23fd73e14`
  (information only; the job stayed on the issued base, as instructed).

## 2. Checkpoint review (maintainer, PROCEED WITH NOTES) and what changed

| Finding | Resolution |
|---|---|
| **G6B-C1-F01 (major)** O2's `habs` re-proved Mathlib's `ZMod.valMinAbs_natAbs_eq_min` | `habs` deleted; the proof rewrites with `ZMod.valMinAbs_natAbs_eq_min` (Mathlib/Data/ZMod/ValMinAbs.lean:160) and `omega` handles `min`; sketch updated. The remaining step (the representative of `v − ⌊q/2⌋` by cases) has no two-case Mathlib lemma for `ZMod` (only `ZMod.val_sub` under `b.val ≤ a.val`; the two-case facts exist for `Fin` only): searched and recorded (`evidence/dup/dup-table.md`, *O2*). O2 amended to `5bd5ada5…`; all O2 evidence re-run; series 2 rebased. Listed in *Overlap and reuse*. |
| **G6B-C1-F02** G15 sketch | now names `acceptProb_def`, `acceptProb_comp_equiv` and the marginalization lemma `uprob_fst` (`Foundations/Probability.lean:175`). |
| **G6B-C1-F03** G6 prerequisite | not restated in a 6b file. G6's sketch cites the owner-side `decrypt_eq_decode_dotProduct : decrypt P s C = LWE.BitEncoding.decode P.lwe (secretVector P s ⬝ᵥ decryptColumn P C)` as MISSING (to land owner-side in `GSW/Scheme.lean` before the fill, ruling Q-C1); the reader census lists it MISSING beside `hybridPlant`. `Scheme.lean` untouched. Probe P4 checks the proposed lemma by kernel `decide` on two toy parameter sets. |
| **G6B-C1-F04** admissions must reach the new modules | § 7: compiled `sorry` warnings of all 1,452 modules (the new ones included) against `base-sorries.txt` + the 24 targets: 313 in 63 modules, 0 differing modules. |

One further docstring fix after the review: G16's sketch named `Nat.clog_le_self`, which does not exist in the pinned
Mathlib (found by the probe sub-agent); it now names `Nat.clog_le_iff_le_pow` and `Nat.lt_two_pow_self`. A
`#check` sweep over all 216 backticked identifiers of the docstrings found no other dangling lemma name
(`evidence/citations/names/TRIAGE.md`). No declaration changed after checkpoint 1 (decls2 and the StmtDump are
identical to the pre-review head's).

## 3. Environment, pool, who did what

- **Preflight**: `nproc` 4; cgroup v1 limit 13.35 GiB, in use 0.20 GiB, headroom **13.15 GiB**; disk 23.4 GB free
  (ext4) after the exchange worktree was made sparse (`evidence/logs/preflight.log`).
- **Cache**: store absent before the first fetch. Prefix roots (105): 2,345 files, 0 failed. Root build roots: the
  pack's `roots.txt` lists 385 entries of which 5 are not Mathlib/Batteries modules (`Std.Sat.CNF` is core; three
  PFR modules, built locally; and `the`, a token from a comment line), and the first attempt with them failed
  (`unknown module prefix 'Std'`, nothing fetched); the fetch used the 380 Mathlib/Batteries roots plus the 14
  Mathlib roots of the PFR modules that `roots.txt` lacks (394, `evidence/logs/mathlib-roots-root-fetch.txt`):
  1,262 downloaded, 3,607 decompressed, 0 failed. Both fetches ran **alone**, holding every pool slot
  (`hold_pool.py`, `HOLD`/`UNHOLD` in `pool.log`). Packages match the manifest after both (ABSENT: `doc-gen4`,
  `UnicodeBasic`, `BibtexQuery`, `MD4Lean`); no empty olean.
- **PFR**: the 31 PFR modules TCSlib imports were compiled with `lean -o` into the lead's tree (the 6a precedent),
  31/31 rc 0 (`evidence/build/pfr/`).
- **Pool** (`evidence/logs/pool.log`, 2,021 acquisitions): 3 slots (`min(4, 13.15/4)`) until 20:39Z, then **2**: a
  probe (`P2b`, kernel `decide` at `q = 256`) was OOM-killed at 20:34:26Z (rc 137, 13.2 GB), a shortage under the
  addendum, so the pool was shrunk; nothing else failed. Lowest MemAvailable at an acquisition 12.0 GB; peak RSS
  of any other process 5.7 GB (a probe), 4.7 GB in the root build (`Build/ZoneRebalance`), 2.85 GiB in the seals.
- **Who did what.** The lead wrote O2 and all nine statement files and the facades, made every commit, ran the
  builds, decls2, StmtDump, axioms, admissions, frozen check, lint, sizes, citations and reproduction. Sub-agent
  **`seal`** (own worktree and olean tree): Rule 10 seals, controls, unfold scans (`evidence/subagents/seal/`).
  Sub-agent **`probe`**: probes P1–P8, reader census, clash/shadow scans, duplication searches
  (`evidence/subagents/probe/`); it stopped on a usage limit before its last two long `#eval`s, which the lead
  re-ran (§ 10). The brief's suggested `lev`/`asy` split was not used: with every file reading the previous files'
  definitions, the lead wrote the statements and delegated verification. Sub-agent trees were seeded by copying
  the lead's TCSlib oleans after a source-identity check (`evidence/subagents/seed*-check.txt`; at the final head
  1,452/1,452 bound, `evidence/build/root-final/summary.txt`).

## 4. Statements: row map, definitions, decls2

- **decls2** vs the base (`evidence/stmt/decls2-final-r2.txt`): **136 ADDED, 0 CHANGED, 0 REMOVED** over the 12
  files; `BitEncoding.lean` exactly O2's five. With the `simps` projections (`fheView_fst`, `fheView_snd`,
  `Parameters.ofFamily_lwe`, `_width`) there are 140 new names (`evidence/clash/new-names.tsv`). StmtDump:
  `evidence/stmt/StmtDump-r2.log` (every new constant, full name and type).
- **Row map** (`evidence/stmt/rowmap.tsv`):

| Row | Delivered | Kind |
|---|---|---|
| G4 (O2) | `LWE.BitEncoding.decode_iff_mem_Ico` | proved |
| G1 | `GSW.Encrypts.select` | target |
| G2 | `GSW.encrypts_homEvalPBP` | target |
| G3 | `GSW.encrypts_homEvalFormula` | target |
| G5 | `GSW.vecMul_secretVector_eq_sum` | target |
| G6 | `GSW.decryptFormula_eval` | target |
| G7 | `GSW.nandFormula_eval` | target |
| G8 | `GSW.depth_nandFormula_le`, `GSW.maxFanin_nandFormula_le`, `GSW.decDepth_le` | 3 targets |
| G9 | `GSW.encrypts_bootNAND` | target |
| G10 | `GSW.decrypt_fheEval` | target |
| G18 | `GSW.decrypt_fheEvalCircuit` | target |
| G11 | `GSW.encrypts_evalKey` | **citation, proved** (`encrypts_encrypt`) |
| G12 | `GSW.decrypt_keygen_fheEvalCircuit` | target |
| G13 | `GSW.bootNoise_le` | target |
| G14 | `GSW.weakCircularSecure_iff` | reader-only (Q-6B-1 A) |
| G15 | `GSW.distAdv_fheView_noEvk_le` | target |
| L1 | `GSW.encrypts_levelKey` | **citation, proved** (`encrypts_keygen_encrypt`) |
| L2 | `GSW.encrypts_leveledEval` | target |
| L3 | `GSW.decrypt_keygen_leveledEvalCircuit` | target |
| L4 | `GSW.distAdv_levelHybrid_le` | target |
| L5 | `GSW.distAdv_leveledView_le` | target |
| G16 | `GSW.bootRatio_le_poly` | target |
| G17 | `GSW.decrypt_fheEval_of_ratio`, `GSW.decrypt_leveledEval_of_ratio` | 2 targets (split) |
| A1 | `GSW.indCPA_of_dlweAssumption` | target |
| A2 | `GSW.weakCircularSecureFamily_iff` | reader-only (Q-6B-1 A) |
| A3 | `GSW.leveledINDCPA_of_dlweAssumption` | target |

  **24 admitted targets** (23 + the G17 split), 2 proved citations, 2 reader-only rows, O2 proved. Per file: Branching 3,
  DecryptFormula 6, Bootstrap 5, Circular 1, Leveled 2, LeveledSecurity 2, PolyRatio 3, Asymptotic 2; none in
  `LWE/Ratio`, `BitEncoding` or the facades.
- **Definitions and readers** (`evidence/stmt/definitions-readers.txt`; every reader proved, `rfl`/`Iff.rfl` or one
  line): O2 `decodeLo`/`decodeHi` (`_eq`); `select`, `homEvalPBP`, `homEvalFormula`, `keyBits`, `decConstants`,
  `decryptFormula`, `nandFormula`, `decDepth`, `bootNoise`, `bootNAND`, `fheEval`, `fheEvalCircuit`, `evalKey`,
  `levelKey`, `leveledEval`, `leveledEvalCircuit`, `leveledView`, `levelHybrid`, `levelMsgs`, `levelAssemble`,
  `levelReduction`, `levelTerm`, `challengeDist`, `challengeTerm`, `pBoot`, the four encodings (`_eq`; the
  encodings also `_length`, proved from `encodeMatrix_length`/`encodeChallenge_length`); `bootGate` (case readers
  `_of_args_eq_nil`/`_singleton`/`_cons_cons`), `levelGate` (`_of_lt`/`_of_le`), `literalCts` (`_eq`, `_castAdd`,
  `_natAdd`); `fheView` (`_eq` and non-simp `simps` `fst`, `snd`); `Parameters.ofFamily` (non-simp `simps` `lwe`,
  `width`); predicates `WeakCircularSecure`, `WeakCircularSecureFamily`, `ReductionEfficient`,
  `LeveledReductionEfficient`, `LWE.Family.RatioBounded` (`_iff`); the type abbreviations `PublicKey`, `Secret`,
  `Coins`, `KeySeed`, `FheView`, `Seeds`, `LevelCoins`, `LeveledSeeds`, `LeveledView` (`_eq`); the instance
  `Parameters.neZero_columns` (a `Prop`, proved). The only definition without a named reader is the compiler's
  matcher `bootGate.match_1`.
- Computable as r3 requires: `select`, `homEvalPBP`, `homEvalFormula`, `bootNAND`, `bootGate`, `fheEval`,
  `fheEvalCircuit`, `leveledEval`, `leveledEvalCircuit` compile without `noncomputable` and are `#eval`ed by the probes.
  `levelTerm`, `challengeTerm` are `noncomputable` (real-valued `decisionAdvantage`).

## 5. Statement changes against r3

Names and shapes kept unless listed. Every change below keeps r3's meaning; the ones that touch
a constant or a hypothesis are also raised as questions (§ Questions).

| # | Row / item | r3 sketch | Delivered | Reason |
|---|---|---|---|---|
| 1 | G1 | implicit `P`, bounds | `Encrypts.select P hC hU hV hb` with `P` explicit, as phase 5's `Encrypts.*` | phase-5 convention |
| 2 | G5 | `secretVector P s ⬝ᵥ c` | `c` written as `decryptColumn P C` | `c` was informal |
| 3 | G8 | `decDepth P ≤ 9⌈log₂ N⌉ + 2⌈log₂(P.width + …)⌉ + 21` | `… + 2 * Nat.clog 2 (P.width + Nat.clog 2 P.columns + 3) + 21` | *(fix)* settled: F10's form with `⌈log₂ q⌉ ≤ ℓ` |
| 4 | G11 | `encrypts_evalKey : Encrypts P (secretVector P s) … (evalKey P pk s R i)` with an honest `pk` left informal | `pk = (A, noisyValues P.lwe A s e)` with `he : ∀ i, |e i| ≤ B`, the hypotheses of `encrypts_encrypt` | makes "honest" explicit; proved citation |
| 5 | G12, L3, G17 | honest keys `…` | key-generation seeds `rg` / `rgs`, keys `Regev.keygen P.lwe χ rg`; inputs `encrypt pk (x j) (R' j)` | explicit sampling, as `decrypt_keygen_encrypt` |
| 6 | G12 | `hsep` only | same: the input condition `2·(ℓ·mB) < ⌊q/2⌋` follows from `hsep` (`mB ≤ bootNoise P (mB)`) | none |
| 7 | G13 | `4^c₀·N^(2c₁+1)·(ℓ+⌈log₂N⌉+3)^(2c₂)·(2β)` | `c₀ = 33, c₁ = 9, c₂ = 2` | *(fix)* settled (derivation in § Constants) |
| 8 | G14, A2 | theorems `distAdv_fheView_le`, `fheView_negligible` | none: the readers `weakCircularSecure_iff`, `weakCircularSecureFamily_iff` | ruling Q-6B-1 A |
| 9 | G15 | `distAdv_fheView_noEvk_le …` | over `fun r => ((fheView P χ μ r).1, (fheView P χ μ r).2.2)` with phase 5's bound | brief: not over `realView` (G45-01) |
| 10 | L1 | `encrypts_levelKey (hχ) … (levelKey P pks ss R d j)` | seeds `rgs`, `pks = keygen(rgs ·).1`, `ss = keygen(rgs ·).2`; noise `m·B` | explicit honesty; proved citation of `encrypts_keygen_encrypt` |
| 11 | levels | `evk_d`, `1 ≤ d ≤ L`, encrypts `s_{d−1}` under `pk_d` | `levelKey … (d : Fin L)` encrypts `s_d` under `pk_{d+1}` (r3 §H5.13's own signature: `ss d.castSucc` under `pks d.succ`) | 0-based `Fin L` |
| 12 | `leveledEval` | gate at level `d` uses `levelKey ⟨d − 1, _⟩` | new helper `levelGate P lk δ g cts` (`bootGate` with `lk ⟨δ − 1, _⟩` if `δ − 1 < L`, else `0`), the level read as `Cc.depthAt` of the vertex index `vs.length` | totality; readers `levelGate_of_lt`, `_of_le` |
| 13 | L2 | `(hdepth : Cc.depth ≤ L) …` | explicit `ss`, `lk`, `hk`, `hin`, both separation conditions; index `⟨Cc.depth, Nat.lt_succ_of_le hdepth⟩` | the `…` made explicit |
| 14 | L4 | `distAdv_levelHybrid_le …` (shape open) | `distAdv (levelHybrid P χ L μ (e + 1)) (levelHybrid P χ L μ e) D ≤ ∑ j, levelTerm P χ L μ e j D`, `e : Fin L`, with the new hybrid `levelHybrid` | r3 left the hybrid implicit |
| 15 | `levelReduction` | `(P χ L d j μ D)`, `d j : ℕ` | `(P χ L μ e j b D)`, `e : Fin L`, `j : Fin N`, side `b`; coins `Coins P × ((Fin (N−1+1) → Coins P) × (LeveledSeeds × ρ))`; helpers `levelMsgs`, `levelAssemble` | the two DLWE terms are the two sides `b`; `hybridPlant` indexes by `Fin (q+1)` |
| 16 | `levelTerm` | `levelTerm P χ L d j D` | `levelTerm P χ L μ e j D` | the reduction must simulate the challenge `Enc_{pk_0}(μ)`, so the term depends on `μ` |
| 17 | L5 | `≤ 2 * ∑ d ∈ Icc 1 L, ∑ j ∈ range N, levelTerm … + challengeTerm P χ L D` | `≤ ∑ e : Fin L, ∑ j : Fin N, (levelTerm μ₀ e j D + levelTerm μ₁ e j D) + challengeTerm P χ L μ₀ μ₁ D`, with `challengeDist`, `challengeTerm` defined | consequence of 16 (the two chains differ); `challengeTerm` was named but not defined in r3 |
| 18 | G16 | `4·ℓ·bootNoise … ≤ pBoot·B` | `8 * (ℓ * bootNoise …) ≤ pBoot.eval κ * B κ`, `pBoot` constant `2^70` | **question G6B-W1**: with `4`, G17's `pBoot·B < q` does not give the floor condition `2·(ℓ·β) < ⌊q/2⌋` when `q = 4ℓβ + 1` |
| 19 | G17 | one lemma "pure and leveled" | split: `decrypt_fheEval_of_ratio`, `decrypt_leveledEval_of_ratio` | allowed by `targets.txt` ("24 if G17 is split") |
| 20 | A4 leveled | `LeveledReductionEfficient F L`: `∀ D μ, ∃ D', ∀ κ, ∀ d ≤ L κ, ∀ j < N, levelDLWEAdvantage … ≤ advantageAt D' κ` | `∀ e : Fin (L κ), ∀ j b, …` **and** `∀ μ', decisionAdvantage (reduction P_κ μ' (challengeDist …)) ≤ advantageAt D' κ`; no separate `levelDLWEAdvantage` name | **question G6B-W2**: A3 needs the challenge step dominated too |
| 21 | encodings | `encodeView (P) : View P → List Bool` | `encodeView P : PublicKey P × Ciphertext P → List Bool` (phase 5's view type) | no `View` type in phase 5 |
| 22 | `RatioBounded` | `∀ κ, (F.noise κ).Bounded (B κ) ∧ q κ ≤ p.eval κ · B κ` | the same with `q κ = (F.parameters κ).modulus` | — |

New public definitions beyond r3 §H4's list, each with readers: the type abbreviations `PublicKey`,
`Secret`, `Coins`, `KeySeed`, `FheView`, `Seeds`, `LevelCoins`, `LeveledSeeds`, `LeveledView` (the brief's
"types r3 names loosely"); `levelGate`; `levelHybrid`, `levelMsgs`, `levelAssemble`, `challengeDist`,
`challengeTerm`; the instance `Parameters.neZero_columns`.


## 6. Constants settled (r3 *(fix)*), with derivations

- **`decDepth_le`**: `decDepth P ≤ 9⌈log₂ N⌉ + 2⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21`. `decDepth P = modSumDepth N q`
  (F10's bound for `N` summands), F10's closed form `9⌈log₂ M⌉ + 2⌈log₂(⌈log₂ q⌉ + ⌈log₂ M⌉ + 3)⌉ + 21` at `M = N`,
  and `⌈log₂ q⌉ ≤ ℓ` from `q ≤ 2^ℓ`. No term linear in `ℓ` (P7: `decDepth` grows by 7–11 per doubling of `ℓ` up to
  `ℓ = 4096`; 1,746 parameter sets, 0 violations).
- **`bootNoise_le`**: `bootNoise P β ≤ 4^33·N^19·(ℓ + ⌈log₂ N⌉ + 3)^4·(2β)` (`c₀ = 33, c₁ = 9, c₂ = 2`). With
  `a = ⌈log₂ N⌉`, `X = ℓ + a + 3`, `b = ⌈log₂ X⌉`: `decDepth + 1 ≤ 9a + 2b + 22`; for `y ≥ 1`, `2^⌈log₂ y⌉ < 2y`, so
  `4^⌈log₂ y⌉ ≤ 4y²`; hence `4^(decDepth+1) ≤ 4^22·(4N²)^9·(4X²)^2 = 4^33·N^18·X^4`, times `2Nβ`. P7: 6,984 checks,
  0 violations; each step checked separately.
- **`pBoot F`** `= 2^70·r·((d+1)·r)^19·(r + (d+1)·r + 3)^4·s` (`d, s, r` the family's dimension, sample and
  residue-width bounds): `8·ℓ·bootNoise(m·B) ≤ 8ℓ·4^33·N^19·X^4·2mB` with `N ≤ (d+1)r`, `X ≤ r + N + 3`, `m ≤ s`,
  `8·4^33·2 = 2^70` (r3 §H6: `c < 2^70`). P7: 124 checks, 0 violations; G17's hypothesis `pBoot(κ)·B < q(κ)` is
  satisfiable (first at `κ = 600` for the sample family F1).

## 7. Builds and admissions (checks 1, 2, 4)

- **Bootstrap** of `prefix.txt` at the base: 288/288 rc 0, 0 errors in both forms; its `sorry` warnings equal
  `base-sorries.txt` restricted to the prefix: 99 in 17 modules, name for name (`evidence/admissions/bootstrap-vs-base.txt`).
- **O2 head** `5bd5ada5`: the 18 `DOWN` modules 18/18 rc 0, 0 errors, 0 `sorry` (`evidence/build/sweep-o2-r2/`).
- **Root build** (`evidence/build/root/`, then `sweep-final-r2/`): `order-final.txt` (1,452 = 1,443 + the 9 new
  modules, inserted after their imports, the GSW facade after its children). The 1,155 modules not in the prefix
  were built at `a855e111` (the pre-review head; the run was resumed once after the tool's 2-hour limit stopped it at
  1,038 modules, all passed; the interrupted module was rebuilt), then every module whose source differs at the final
  head and its downstream closure (12 modules) was rebuilt at `8f92fe7d` together with the brief's final sweep (the
  18 `DOWN` + 9 new + root: 28/28 rc 0). **Binding** (`evidence/build/root-final/summary.txt`): every one of the
  1,452 modules has its last successful build from exactly `git show 8f92fe7d:<module>.lean`, **1,452/1,452 bound**,
  rc 0, 0 errors in both forms; the root `TCSlib` included. Not marked incomplete.
- **Admissions, exact** (`evidence/admissions/final-vs-expected.txt`): the compiled `sorry` warnings of all 1,452
  modules against `base-sorries.txt` plus the 24 delivered targets: **313 = 289 + 24 in 63 = 55 + 8 modules, 0
  differing modules**, name for name. The syntactic scan (`tools/graph.py`) agrees: base = O2 head = 289, final 313
  (`evidence/admissions/graph/`).

## 8. Axioms and dependency trace (check 5)

`evidence/stmt/AxiomProbe-r2.log`, summary `axioms-summary-r2.txt`: 176 constants (153 declarations, 23 auxiliary)
of the 12 modules. Only `propext`, `Classical.choice`, `Quot.sound`, except `sorryAx` in exactly **28**: the 24 targets,
each tracing only to itself, and
- `fheEvalCircuit`, `fheEvalCircuit_eq` via 6a's N2 `BoolCircuit.nandGadget_correct` only;
- `leveledEvalCircuit`, `leveledEvalCircuit_eq` via N2, N12 `DAGCircuit.layerGates_acyclic`, N13
  `DAGCircuit.layerOutput_lt` only.

The trace walks each constant's closure across all TCSlib modules and stops at constants whose own type or value
mentions `sorryAx`. No other definition or reader reaches `sorryAx`; every statement mentioning
`fheEvalCircuit`/`leveledEvalCircuit` is itself a target. O2's 24 constants: standard axioms only.

## 9. Rule 10 (check 6)

Sub-agent `seal`, at O2 `5bd5ada5` and final `8f92fe7d` (`evidence/rule10/r2/`, one command `run_heads.sh`; tools in
`evidence/tools/seal/`, every change in the tools' headers). All seals over the full TCSlib import closure with
`-DmaxErrors=0`; every probe rc 0, 0 errors, install and EOF records `requested = verified`; **no failing
declaration**; no chunking needed.

| Owner | A | B | coe-A | coe-B |
|---|---|---|---|---|
| `LWE/BitEncoding` (O2 head and final head) | 9 | 9 | 9 | 9 |
| `LWE/Ratio` | 947 | 948 | 946 | 947 |
| `GSW/Branching` | 199 | 199 | 199 | 199 |
| `GSW/DecryptFormula` | 374 | 374 | 373 | 373 |
| `GSW/Bootstrap` | 437 | 437 | 436 | 436 |
| `GSW/Circular` | 457 | 457 | 456 | 456 |
| `GSW/Leveled` | 467 | 467 | 466 | 466 |
| `GSW/LeveledSecurity` | 1,549 | 1,550 | 1,548 | 1,549 |
| `GSW/PolyRatio` | 1,382 | 1,383 | 1,381 | 1,382 |
| `GSW/Asymptotic` | 1,641 | 1,642 | 1,640 | 1,641 |
| `GSW.lean` (facade) | 1,650 | 1,651 | 1,649 | 1,650 |
| `LWE.lean` (facade) | 966 | 967 | 965 | 966 |

B = A + 1 where `PolyExpr.eval` is in the closure; coe = strict − 1 where the `FinDist` coercion is. Request sets equal
the pre-review runs at `a855e111` (52 probes compared, 0 different). **Paired controls** (`controls/summary.tsv`,
`ALL_OK`): on `decodeLo`, `RatioBounded`, `select`, `decDepth`, `bootNoise`, `WeakCircularSecure`, `levelKey`,
`challengeDist`, `pBoot`, `encodeCiphertext`: unsealed body read 0 errors; sealed (strict and coe) exactly 1 error, in the
example; read through the published reader 0 errors. The facades define nothing (no pair). **Notation never sealed**:
`Parameters.columns`, `Ciphertext` and the nine new abbreviations, `PolyExpr.eval` (only in B variants), projections,
the `FinDist` coercion (only in strict variants); `unexpected = 0`. **Explicit-unfold scan**: 0 foreign (BitEncoding 52
hits; the other files 49 hits, including the own-file `unfold bootGate` ×3 and `unfold levelGate` ×2); a Lean-resolved
check of every `simp`/`rw`/`unfold` argument finds no core, Mathlib or foreign TCSlib definition.

**Reader census** (`evidence/census/reader-census.md`, sub-agent `probe`, Lean-resolved): 89 foreign definitions read by
a definition body, a target statement or a target sketch, each with its readers. **MISSING (fill prerequisites for
Seyoon, never worked around):**
1. `TCSlib.Cryptography.hybridPlant` (`Encryption/PublicKey/EnsembleSecurity.lean:110`): read as a term by
   `levelReduction` and by L4's sketch; proposed one-line owner-side reader `hybridPlant_apply` (`rfl`), text in the
   census.
2. `decrypt_eq_decode_dotProduct : decrypt P s C = LWE.BitEncoding.decode P.lwe (secretVector P s ⬝ᵥ decryptColumn P C)`,
   proposed for `GSW/Scheme.lean` (checkpoint review G6B-C1-F03); needed by G6's fill.

## 10. Probes (check 7)

`evidence/probes/README.md` has every probe with parameters, method and outcome; sources and raw logs beside it. Kernel
`decide`/`rfl` where the kernel reduces, otherwise `#eval` (evidence only); **no `native_decide`**. `#eval` probes run
probe-local strict evaluators **proved equal** to the library definitions through their readers, so the library
definitions themselves are evaluated. **No statement was found false**; negative controls fail as expected.
- P1 selector: noise-free identities by kernel `decide` (`q ∈ {4, 5, 8}`); G1's bound on explicit error vectors
  (`q = 256`, `N = 16`) by `decide` of a witness check proved sound; worst case reaches `N·β` (bound loose by about `N·β`).
- P2 PBP and formula: G2 noise-free by kernel `decide` (width-3 program); G2 with noise by `#eval` (12 cases, noise 5–12
  ≤ 96); G3 noise-free on 7 formulas × 4 inputs: coordinate `σ 0` encrypts `c.eval x`, coordinate 0 its complement.
  G3's numeric noise part was stopped for time (G1/G2's noise bounds are probed).
- P3 O2: kernel `decide` for every `2 ≤ q ≤ 63` (62 theorems, standard axioms), `#eval` for `64 ≤ q ≤ 2000`: 0
  mismatches; negative control (wrong ends) refuted.
- P4 decryption formula: G5 and the proposed `decrypt_eq_decode_dotProduct` by kernel `decide` (two toy sets); G5, G6,
  G7, G8 by `#eval` over 6 parameter sets (up to `q = 8`, `ℓ = 3`): 0 mismatches; observed depth ≤ `decDepth + 1`.
- P5 bootstrapping (at `n = 0, m = 2, q = 2, ℓ = 1`; one bootstrapped gate is a 49,024-instruction Barrington program):
  `bootNAND` on all 4 pairs gives `(!(dec C₁ && dec C₂))•G`. `fheEval` on a padded XOR circuit (fan-in 0 and 1 gates):
  **partial**: the input `(true, false)` gives `(Cc.eval x)•G` and decrypts
  to `Cc.eval x`; the run (uncapped, by the lead) was killed by a container restart after that input, and one input
  took over an hour, so the other three were not re-run. The gate function `bootGate` with its padding is covered by
  P5a and by P6b's full run.
- P6 leveled: `literalCts` and `levelKey` by kernel `decide` at `n = 1` (distinct keys: inputs decrypt wrongly under
  `s₁`, the level key correctly); the level-1 gate's formula computes NAND on all inputs. `leveledEval` on the layering
  of `NAND(x₀, NAND(x₁))` (a parity twin; layered, depth 2): all 4 inputs give `(Cc.eval x)•G` under the output level's
  key and decrypt to `Cc.eval x` (uncapped run by the lead, 52 minutes); the layering facts (`IsLayered`,
  `IsNANDForm`, depth 2) by `decide`. The XOR and odd-gap circuits of 6a's P9 were not run (cost).
- P7 constants: § 6. P8 types: every asymptotic definition and statement elaborates at two sample families; `ofFamily`'s
  readers used as stated; `RatioBounded` proved for a sample through its reader.

## 11. Frozen files, lint, sizes, citations (checks 8–10)

- **Frozen check** (`evidence/headers/`, `tools/lead/frozen_check6b.py`): at the O2 head and the final head **0
  violations**: `BitEncoding.lean`'s 12 base declarations identical, its 5 additions allowed, other text insertions only;
  the facades change only imports and module-docstring lines. Controls: one altered character in `decode_eq`'s header →
  exactly 1 difference; deleting `codepoint_eq` → exactly 1 removal (both heads). `git diff --stat` base..final: exactly
  the 9 new and 3 changed files (+2,170/−1).
- **Lint**: `style_lint` 0 findings in the 12 files; `campaign_style_lint TCSlib/Cryptography --check8b` 92 FAIL / 104 WARN
  at base and final (529 → 538 files), FAIL/WARN line sets identical (`evidence/lint/`).
- **Sizes** (`evidence/sizes/sizes-r2.txt`): widths ≤ 99 characters; lines Branching 179, DecryptFormula 220, Bootstrap 351,
  Circular 146, Leveled 283, LeveledSecurity 351, PolyRatio 174, Asymptotic 324, Ratio 59, BitEncoding 200, facades 57/40;
  with r3 §H7's upper fill estimates every file stays below 1,000 (largest projection Bootstrap 791). The statement
  surface (about 2,090 lines in the nine new files) is above the brief's 1,300–1,800 estimate, mostly docstrings
  (formulas, deviations, sketches) and the reader/abbreviation layer.
- **Citations** (`evidence/citations/`): 119 anchors in 127 citations, each present in its tag's ingest; no `[Gen09]`;
  the leveled docstrings (`Leveled`, `LeveledSecurity`, `PolyRatio`'s leveled lemma, `Asymptotic`'s leveled items) carry
  the P6-Q19 B disclosure. Quotations checked (`quotes.txt`: 4 exact, 3 rendering-different). BV14's "[BV11, Lemma 4.1]"
  is cited as [BV11, Lemma 4.5] with BV14's numbering noted.

## 12. Clash and shadow scans (check 11)

`evidence/clash/` (sub-agent `probe`): (a) 140 new full names, **0 clashes** with TCSlib/`audits` at the base (34,838
names), #355's head `d3c7cb00…` (33,256) and the GF-W1 reserved names; no private declaration. (b) New short names that
exist elsewhere: `Coins` (`NUPPT.Coins`, `LWE.Noise.Coins`, …), `select` (`Turing.Cfg.select`,
`Randomness.Rejection.select`, a private field; Mathlib `WittVector.select`), `PublicKey` (`RSA.PublicKey`), all in other
namespaces. (c) No `DOWN` module's unqualified use changes resolution: only the facades `GSW`, `Homomorphic`,
`AdvancedEncryption` (and `LWE` for `Ratio`) reach the new modules, and they contain only imports; token scan: 0 hits on
in-scope new names outside the defining file.

## 13. Overlap and reuse (check 12)

Searches: by name (TCSlib, #355, Mathlib, Batteries, core), by shape (46 patterns), and by reading the brief's
near-relatives (`evidence/dup/dup-table.md`, `searches.txt`). **No exact restatement.** Notable rows:
- **Proved citations**: G11 `encrypts_evalKey` = `encrypts_encrypt` (`Scheme.lean:161`) through `evalKey_eq`; L1
  `encrypts_levelKey` = `encrypts_keygen_encrypt` (`:186`) through `levelKey_eq`, `evalKey_eq` (LE-g45 precedent).
- **Specializations admitted as targets**: `decDepth_le` is F10's `modSumDepth_le` (`ModSum.lean:179`, admitted in 6a) at
  `M = N` with `ℓ` for `⌈log₂ q⌉` (weaker), behind `decDepth`; r3 G8 asks for the `ℓ`-form and `targets.txt` lists it as a
  target. Disclosed; it could instead be a citation proved in a few lines once F10 is proved.
- **O2**: uses Mathlib `ZMod.valMinAbs_natAbs_eq_min` (`Mathlib/Data/ZMod/ValMinAbs.lean:160`), `ZMod.val_sub`,
  `ZMod.val_natCast_of_lt`; does not re-prove `decode_codepoint_add` (different statement). The case split for
  `(v − ⌊q/2⌋).val` has no Mathlib `ZMod` lemma (G6B-C1-F01).
- **G15** transports phase-5 `distAdv_encrypt_le` (`Security.lean:248`) along the coin regrouping; stated over `fheView`'s
  projection, not `realView` (G45-01).
- **Reuse, not copies**: `levelKey` is `evalKey` at chain indices; `literalCts` uses phase-5 `homNot`; `homEvalPBP` is the
  host `evalWith` (H18); `fheEval`, `leveledEval` run the host `runWith` (H19); `levelReduction` composes `hybridPlant` and
  phase-5 `reduction` as terms; L4/L5 sketches use `distAdv_multi_le_sum` and `abs_sub_le_sum_hybrids` (no local hybrid
  lemma); encodings reuse `LWE.encodeChallenge`, `Encoding.Modular.encodeMatrix`.
- **Near-relatives confirmed different** (brief's list): phase-5 `eval_encrypts`/`decrypt_keygen_eval` (leveled
  multiplicative evaluation, depth-dependent noise) vs G10/G12; `homGate` vs `bootGate`; `Encrypts.nand` (leveled NAND) vs
  `nandFormula`; `vecMul_secretVector_augmented`, `gadget_mulVec_decomposeVec` used by G5's sketch, not restated;
  `Regev.extractionError` reused in `levelTerm`/`challengeTerm`; the three `polyExpr_mul` copies: sketches cite
  `EnsemblesLemmas.lean:377`'s, no fourth added.
- **Inline general facts** in the proofs written here (O2, readers, `_length`, G11, L1): none re-derives a library lemma
  (`dup-table.md`, last section).

## 14. Scope requests, process notes

**Scope requests: none.** No frozen file was edited; both missing readers are listed for Seyoon (§ 9).
Process notes: (1) early on, the lead stopped its own stray `git clone` with `pkill -f` rather than by recorded PID
(handoff rule 4); nothing else was affected. (2) The first root fetch attempt failed on `roots.txt`'s non-module entries
(§ 3). (3) The OOM shortage and pool shrink (§ 3). (4) The root build's first run was stopped by the tool's 2-hour limit and
resumed (§ 7). (5) The probe sub-agent stopped on a usage limit; its last two `#eval` runs were re-run by the lead (§ 10). (6) A
container restart killed the lead's P5b run (recorded in `pool.log` and `probes/P5b_FheEval.progress`).

## 15. Reproduction (check 13)

`evidence/repro-final.log`: in a scratch clone at the base, `git am` of `patches/o2` then `patches/stmt` with each row's
committer name, email and date from `COMMITS.tsv`, signing off, reproduces all six hashes (`5bd5ada5…`, `7a814546…`,
`dd9f00f4…`, `1378740f…`, `5c8f81cd…`, `8f92fe7d…`); `src/` (12 files) and `src-o2/` equal the heads' files byte for byte.
All commits unsigned (signing column `none`).

## 16. Questions for Seyoon

- **G6B-W1 (G16's factor).** r3 sketched `4·ℓ·bootNoise ≤ pBoot·B`. With `4`, G17's hypothesis `pBoot(κ)·B(κ) < q(κ)` gives
  only `4y + 1 ≤ q` (`y = ℓ·bootNoise`), while decryption needs `2y < ⌊q/2⌋`, i.e. `4y + 2 ≤ q` (fails at `q = 4y + 1`).
  - **A (recommended; delivered)**: G16 states `8·(ℓ·bootNoise) ≤ pBoot·B` (constant `2^70`, inside r3's `c < 2^70`), and
    G17 keeps r3's `pBoot·B < q`.
  - **B**: G16 with `4` as r3, and G17's hypothesis `pBoot·B + 2 ≤ q`.
- **G6B-W2 (`LeveledReductionEfficient`).** r3 states domination for the level reductions only; A3's bound (via L5) also
  contains the challenge step's two DLWE advantages.
  - **A (recommended; delivered)**: the hypothesis also dominates `reduction P_κ μ' (challengeDist …)` for both `μ'`.
  - **B**: a separate hypothesis for the challenge step, or reuse `ReductionEfficient` with a challenge distinguisher.
- **G6B-W3 (L4/L5 shape).** The level reduction must simulate the challenge `Enc_{pk₀}(μ)`, so `levelTerm` depends on `μ`
  and L5's bound is the sum over both chains (`∑ (levelTerm μ₀ + levelTerm μ₁) + challengeTerm μ₀ μ₁`) instead of r3's
  `2·∑ levelTerm + challengeTerm`. **A (recommended; delivered)**: accept. **B**: state L5 with `2·∑ max_μ levelTerm`.
- **Fill prerequisites** (not questions): the two MISSING owner-side readers of § 9.

## 17. Evidence

`evidence/SHA256SUMS` covers every evidence file; the top-level `SHA256SUMS` every delivered file (paths equal, no `./`).
Layout: `logs/` (preflight, cache, packages, pool, mkbase), `build/` (bootstrap, sweeps at each head, root, PFR,
`root-final` binding, `order-final.txt`), `stmt/` (decls2, StmtDump, AxiomProbe with trace, row map, definitions),
`admissions/`, `headers/` (frozen check and controls), `rule10/` (seal sub-agent; `r2/` canonical), `probes/`, `census/`,
`clash/`, `dup/`, `citations/`, `lint/`, `sizes/`, `records/`, `subagents/` (both sub-agents' notes and logs; seed
checks), `tools/` (`lead/`, `seal/`, `probe/`, `records/decls2.py`), `repro-final.log` (checkpoint 1's own
evidence stays on the exchange at `1e0647b9`).

