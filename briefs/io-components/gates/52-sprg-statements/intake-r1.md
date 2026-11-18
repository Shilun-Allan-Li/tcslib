# io-sprg checkpoint 0: maintainer intake r1 (static)

Static intake of the io-sprg checkpoint-0 (M0 statements) delivery. No Lean, `lake` or build was
run; the Lean checks are Gate 52's (`pack.md`). Prepared 2026-11-18 on the records branch at
`2f9f95ffd703779faa016b92d5f687d17605905e`.

| Item | Value |
|---|---|
| Delivery | `exchange/pass-shelat-ch5-8` at `15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`, path `inbox/fills/io-sprg/`, subject "fill io-sprg: checkpoint 0 (M0 statements)", unsigned, parent `1e77173a7032b57aa22260787711c6c7a1b7596e` (the io-phfe checkpoint 0) |
| Source HEAD (worker's local `fill/io-sprg`) | `d10a560b34d58919bc1a5206ce66a444613f94c7` (15 commits, `patches/COMMITS.tsv`; delivered also as `bundle/io-sprg.bundle`). The head is an empty marker commit "io-sprg: M0 statements (all proofs sorry)"; the last source change is `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3` |
| Base | `iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` |
| Records pin of the dispatch | `dbea2807532392781304e004715f3b0190025f5e` |
| Pack | `briefs/io-components/sprg/` (rulings.md > dispatch-prompt-r3 > design-r3 > design-r2 > design-r1) |
| Source | `jls26.pdf`, SHA-256 `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` (checked in `$SP/io-sources`; PDF page *k* = article page 1:*k*) |

Everything in the delivery was read as data. Paths below without a prefix are under
`inbox/fills/io-sprg/`; `SS/` is `src/TCSlib/Cryptography/Obfuscation/StructuredSeed/`.
Line numbers are at the source HEAD.

## Verdict

**Checkpoint 0 accepted for Gate 52; no blocker.** The delivery is complete, integral and in scope.
The statements follow the pack and JLS26 closely: Defs 2.3, 3.1–3.4, the construction (IdSamp′,
SdSamp′, 1SdSamp, G⁽¹⁾–G⁽⁴⁾), Claims 4.1–4.2, Lemma 4.2, Proposition 4.1 and Theorem 4.1 are
all stated, with the ruled deviations disclosed. The rule-15 split (raw bundles, efficiency fields,
targets T1–T6, assembly) is in place. Unlike the io-phfe checkpoint (Gate 51 F01), no sPRG
interface is stateful and no efficiency field leaves a run unbounded (F09). The Rule 10 suite was
actually run at M0. Three pre-M0 statement choices rest on chat rulings or on the "best judgment"
authorisation (SP-W1 rational δ, SP-W2, SP-W3; F10). The one major (F01) is payload hygiene,
as in Gate 51 (F02), and the payload is larger.

| Severity | Count | IDs |
|---|---:|---|
| blocker | 0 | — |
| major | 1 | F01 |
| minor | 7 | F02–F08 |
| note | 9 | F09–F17 |

## 1. Integrity

- **SHA256SUMS** verifies 2648/2648: every listed path is delivered, none is unlisted, 0 mismatches;
  `evidence/SHA256SUMS` verifies 2606/2606 likewise. Hashes were streamed from the commit's blobs
  (`git cat-file --batch`; the Gate 51 script). No `.pdf`, page image or PDF excerpt anywhere
  (path scan, and `git grep` of the commit for three distinctive source sentences: no hit).
- **Delivery commit scope.** All 2,649 changed paths are under `inbox/fills/io-sprg/`, insertions
  only (`git diff --shortstat`: 2649 files, +12,545,998 lines; 1,185.6 MB of blobs). Layout as
  prompt §11 requires: `REPORT.md`, `SHA256SUMS`, `patches/` (15 + `COMMITS.tsv`),
  `bundle/io-sprg.bundle`, `src/` (23 files), `evidence/`.
- **`src/` is exactly base + patches.** `git bundle verify` passes (prerequisite the base; head
  `refs/heads/fill/io-sprg` = `d10a560b`); the 15 bundle commits are exactly `COMMITS.tsv`, all
  unsigned; `git format-patch --full-index --no-signature` of `base..d10a560b` reproduces the 15
  delivered patches byte for byte; every `src/` file equals its blob at `d10a560b` and the
  path sets agree. (Checked in a scratch bare repository with the records objects as alternates;
  nothing was written to the repository.)
- **Additive over the base.** 22 new files (5,911 lines, 146 `sorry`; REPORT's counts confirmed)
  and one modified existing file, permitted by prompt §3: `TCSlib.lean` +1 line,
  `import TCSlib.Cryptography.Obfuscation`, right after `…AdvancedEncryption`.
- **Paths.** `TCSlib/Cryptography/Obfuscation.lean`, `Obfuscation/StructuredSeed.lean` and 20
  modules under `Obfuscation/StructuredSeed/` (design-r3 §4 plus a disclosed `Encoding.lean`
  split; no `Realization.lean`, no `SamplerEfficiency.lean`).
- **Static checks recounted.** 0 lines over 100 characters (maximum 100), 0 files over 1,000
  lines (largest `SS/Samplers.lean`, 529); no `@[simp]` or `attribute`, no `native_decide`,
  `admit` or `axiom`; every `sorry` is in a `theorem`; no `Fintype.equivFin`, `Finset.toList` or
  `Classical.choose` outside the `PrimeSchedule.nonempty` proof; no local `RealizesOn`,
  `SamplesEfficiently`, `DrawSamplable` or `CoreComputable`; no bare `∃ A : NUPPT, A.Computes f`.
- **Imports.** `CoinSampling.Contract` only in `Defs`, `BoolPRG`, `LPN`, `Targets` (no other
  `CoinSampling` module, no `Games.Closeness`, nothing under `Programs/` or `RAMSimulation/`);
  `Asymptotic.Realization` only in `Reductions/{LPN,PRG}`. Two layering imports: F04.
- **Build binding.** `evidence/build/summary.txt`: the 22 owners rc 0, both error forms 0,
  `HEAD_match=True` at `d10a560b`; closure order 127 modules (`evidence/logs/order.txt`,
  `import-order-current-binding.json`). decls2 670 ADDED / 0 / 0
  (`evidence/checks/m0-sp-w3/decls2.log`).

## 2. Checkpoint-0 contents (design-r3 §4 M0; prompt §6)

| Required | Status |
|---|---|
| Every file of design-r2 §2.2 as amended, module docstrings with References | Present (20 modules + 2 facades). The facade `## Contents` lines are placeholders (F07) |
| Every definition final with readers: `LPNFamily.Raw`/`LPNFamily`, `BoolPRG`, `SPRG.Raw`/`SPRG`, degrees, `PolyTerms`, `PrimeParam`/`PrimeSchedule`, `Params`, buckets, sparse factor, G⁽¹⁾–G⁽⁴⁾, draws and cores, encodings, `jlsSPRG_raw`, `errProb`, hybrids, advice and encodings, `lpnPre`/`prgPre`, `lpnRed`/`prgRed`, realisability, T1–T6, `Targets`, assembly | All present; readers by `rfl`/`Iff.rfl`; `PrimeSchedule.nonempty` proved (`SS/Defs.lean:82`) |
| Every theorem stated with `sorry` under a **Proof sketch.** | 146 obligations, all with sketches (`evidence/statements/proof-obligations-current.tsv`) |
| REPORT: fidelity table | REPORT.md:146–208 (plus an exhaustive inventory, `evidence/statements/fidelity-current.tsv`) |
| REPORT: rule-15 table | REPORT.md:211–265 |
| REPORT: helper plan, non-vacuity table, size re-estimate | REPORT.md:287–352, 267–285, 449–514 (F11) |
| M0 checks | elaboration (§1); decls2; StmtDump (948 public types); axioms (511 public prints; 146 direct holes, 265 transitive `sorryAx` dependents, no other axiom); **coe-A/B and strict seals run: 88 seal and 96 paired-control probes, 0 failing declarations, ALL_OK True**; unfold scan clean; style 0; campaign lint no new line; sk15 one triaged false positive; clash 0 |

## 3. Fidelity spot-check against JLS26

The PDF hashes as pinned. Read: pp. 8–11 (§2, Defs 2.1–2.3, the multilinear-representation
paragraph, Defs 3.1–3.4, Theorem 4.1) and pp. 14–21 (overview end, construction, 1SdSamp,
G⁽³⁾ box, Claim 4.1, Proposition 4.1, Claim 4.2, Lemma 4.2).

**𝒟_r(p) and Def 2.3** (pp. 9–10). `lpnNoise p W` (`SS/LPN.lean:49`): a uniform
`(a, x) : Fin W × ZMod p` gives `x` if `a = 0`, else 0 — exactly 𝒟_{1/W}(p) ("0 w.p. 1 − r and a
random element of ℤ_p w.p. r"; a triggered error may be 0, as in the source; ERR is
`{i | e_i ≠ 0}`, `SS/Samplers.lean:58`, as on p. 16). `LPNFamily.Raw` (`SS/LPN.lean:79`) reuses
`LWE.Family` with rows as samples (the transpose of `s·A + e`, a bijection of the uniform matrix),
and `Assumption := LWE.DLWEAssumption` (`:175`). The construction's family
`Params.lpnFamily_raw π` (`SS/Params.lean:339`) is indexed by its own dimension L: samples
`L^D`, modulus `(π (κOf L)).p` (a prime of `κOf L + 1 ≈ L^{1/E}` bits, i.e. η_p = 1/E,
η_n = D), rate `1/W(L)` with `W = (max 1 ⌊L^{δ/2}⌋)² ≤ L^δ` (noisier than ℓ^{−δ}). This is
Q-S1 (A): LPN for the construction's own ℓ-indexed family; no literal Def 2.3 bridge. Faithful.

**Defs 3.1–3.2** (p. 10). `SPRG.Raw` (`SS/Defs.lean:97`): one parameter κ (C1/Dv1), seeds
`Fin`-indexed ℤ_p vectors (Dv2/Dv15), `IdSamp`/`SdSamp` as core ∘ uniform draw (Dv17),
deterministic `eval`. `game` (`:234`) gives the adversary `⟨p, ⟨I, ⟨P, z⟩⟩⟩` with z the real
output or uniform — Def 3.2's `(I, P, Eval(I, sd))` vs `(I, P, r)` with p prepended (Dv9; Q-S12).
Def 3.2's "for every n = n(λ) ≥ λ" becomes the fixed schedule n = κ^{E·D} with E free (C1,
disclosed). `HasPolyStretch` (`:285`) is "∃ τ > 1, eventually κ ≤ seedBits ∧ seedBits^τ ≤ outLen"
(Remark 3.1/3.2's polynomial expansion in the actual seed length; the κ ≤ seedBits conjunct is
SP-W3, F10). Faithful.

**Def 3.3** (p. 10), Q-S4. `HasComplexity S dPub dPriv` (`SS/Defs.lean:298`): for every κ and
every index (stronger than "in the support"), polynomials Q_j over `Fin pubLen ⊕ Fin privLen`
with `pubDegree ≤ dPub`, `privDegree ≤ dPriv` (weighted total degrees, `SS/Degree.lean:45`, `:56`)
that equal `Eval` as 0/1 in ℤ_p on every `SdSamp(I)` output. This is the composite form ruled in
Q-S4 ("one polynomial over both seed parts"); it is equivalent to Process_I = the degree-≤ d
monomials of P with Q_I of degree 1 in P̄ and 2 in S. `HasComplexityEff` (`:352`) adds Q_I's
efficient generation from I by one map f before κ, as explicit term lists (`PolyTerms`). "p an
efficiently computable function of λ" is replaced by "every schedule, p public" (Dv9, Q-S2
refined). Faithful.

**Def 3.4** (p. 11). `BoolPRG` (`SS/BoolPRG.lean:50`) indexed by seed length n, uniform σ,
`HasStretch τ : ∀ n, n^τ ≤ outLen n` (Dv5); `MultilinearRep` (`:217`): multilinear ℤ-polynomials
of total degree ≤ d equal to the output bits on {0,1}ⁿ; `HasLocality` (`:234`) reads locality on
the representation's variables (Dv4; unique multilinear representation makes this the semantic
notion). Faithful.

**Parameters** (p. 15). `Params` (`SS/Params.lean:50`): d ≥ 1, **δ : ℚ** in (0, 1) (SP-W1, F10),
E ≥ 1, G, R; no prime. ℓ = κ^E, D = ⌈d/2⌉, n = ℓ^D (so ℓ = n^{1/⌈d/2⌉}), m = G.outLen n,
w = max 1 ⌊ℓ^{δ/2}⌋, W = w², t = κ, √c = rc = t·w, c = cap = rc², B = max 1 ⌈m t / W⌉,
Γ = ⌊m log₂ n / W⌋ (`:64–151`). Side conditions "λ > log n" and "log n large" are
`Γ_le_B` (`:381`) and `le_log_n` (`:387`), eventually in κ; `le_n` (`:375`). p is a (κ+1)-bit
prime (`PrimeParam`, `SS/Defs.lean:48`: 2^κ ≤ p ≤ 2^{κ+1}), i.e. the paper's λ-bit prime with
λ = κ + 1, and t = κ = log p − O(1). Matches design-r2 §3 C1–C14.

**IdSamp′, SdSamp′, 1SdSamp** (pp. 15–16). `IdDraw` (`SS/Encoding.lean:135`) = G's draw ×
φ_bkt ∈ [B]^[m] × A ∈ ℤ_p^{n×ℓ} (transposed); φ_ind is derived (`Buckets.indexMap`, `Option`
valued, `none` when overfull or when the grid is empty at κ = 0, disclosed; the paper's constant
(1, 1) case only arises with flag = 0). `Draw` (`:147`) = σ and κ independent (s, noise-seed)
pairs, all sharing σ and A, as SdSamp′ runs 1SdSamp(I′, σ) κ times. `oneFlag`
(`SS/Samplers.lean:82`) is the three conditions (|BAD| ≤ Γ, no bucket over c, no bucket with
> t bad outputs); BAD (`:69`) uses `vars` of R's polynomial; `corr` (`:97`) = y − y′ with y′ the
ℤ_p evaluation at σ + e; `oneSd` (`:140`) gives b = A s + e + σ, S₁ = s̄^{⊗D} (entries
∏ s̄_{α_r}), and (U_i, V_i) = sparse factors when flag = 1, else 0. `sdCore` (`:236`): first
successful k (ordered search), err = no success, P′ = (b⁽ᵏ⁾, err), S′ = (flag⁽ᵏ⁾, S⁽ᵏ⁾,
flag⁽ᵏ⁾·S⁽ᵏ⁾) with later flags zeroed. The sparse factorisation is the paper's "M_i = U_i V_i"
made deterministic (row-major listing; the paper only asserts existence by rank ≤ t). Faithful.

**G⁽¹⁾–G⁽⁴⁾ and degree d, not d + 1** (pp. 14, 16–17). `halfForm`/`prgPoly`
(`SS/Polys.lean:169`, `:189`): each monomial's sorted support is padded with constants to 2D slots
and split in halves, each half `Σ_α ∏ c_{i_r}(α_r) · X(S₁ α)` with c_i = (−a_iᵀ ‖ b_i) — Equation
(3)'s ⟨⊗ c_i, ⊗ s̄⟩ (the paper's "assume every monomial has degree exactly d by including 1 in
σ"). `G2 = G1 + U·V` at (φ_bkt(j), φ_ind(j)) (`:241`); `G3` reads one factor of every quadratic
term from the precomputed flag·S copy (`:253`), so G3 = flag·G2 on the seeds (Equation (4)) with
private degree 2; `G4 = Σ_k G3⁽ᵏ⁾`, renamed to `Fin` coordinates (`:277`). `G4_degrees` (`:343`)
claims public degree ≤ d, private ≤ 2: the p. 17 formal construction and Theorem 4.1, **not**
p. 14's "degree d + 1" (the campaign-open row; design S3/Dv10). The docstrings say so
(`SS/Polys.lean:40–41`, `SS/Samplers.lean:311–312`). `G4_eval_eq` (`SS/Correctness.lean:232`):
G4 = (1 − err)·Eval_I(σ) on every sampled seed. Faithful.

**Claim 4.1** (p. 18). `jls_hasPolyStretch` (`SS/Stretch.lean:122`) under `E ≥ E0 d δ τ =
⌊max(10/δ, 5/(τ−1))⌋ + 1` and G's stretch τ; `seedBitsAt_le` (`:82`) is the paper's
|sd| = O((n + m/ℓ^{δ/2})·λ⁵) with explicit rounding. Checked by hand: E·δ/2 > 5 and
E·(τ − 1) > 5 suffice. Faithful (C10).

**Proposition 4.1 and Lemma 4.2** (pp. 18–19). `hyb` (`SS/Hybrids.lean:112`) is H₀–H₃ (err
published as 0 in H₁/H₂, output y or r; buckets included, Dv8). `chainGame A tail i`
(`:86`) is Lemma 4.2's D_i with tail y or uniform. `lemma42` (`SS/Security.lean:62`) bounds
D₀ → (uniform vectors, uniform tail) by κ LPN advantages + 1 PRG advantage; `prop41` (`:84`):
for every schedule π and adversary A there are advice families such that every pair of
`RealizesOn` realisers satisfies, at every κ,
`adv ≤ 2κ·adv_LPN(ℓ κ) + adv_PRG(n κ) + 2·errProb κ (π κ)` — the paper's γ = O(λε) with the
2^{−λ} slack left exact (S8). The 2κ counts both LPN chains (tail y forward, tail r backward).
The hop reductions take the LPN challenge (A, b) unchanged (`lpnEnc` = `LWE.encodeChallenge`),
keep A challenge-supplied and hardwire I, φ, σ, the other instances' (s, e), the tail and the
uniform vectors (`SS/Reductions/LPN.lean:135`, `:321`); the PRG hop hardwires φ, A and the
uniform vectors (`SS/Reductions/PRG.lean:93`, `:248`). The paper's D_i writes `s·A` without the
superscript (k); the instances use fresh secrets as in D₀ and SdSamp′ — the Lean is right.
SP-W2's acceptance-level equalities (`SS/Hybrids.lean:157`, `:167`) are the correct form (F10).

**Claim 4.2** (pp. 19–21). `errProb` (`SS/Claim42.lean:93`) is the exact Pr[err = 1];
`claim42` (`:155`): `∃ κ₀, ∀ κ ≥ κ₀, ∀ pp, errProb κ pp ≤ 2^{−κ}` (κ₀ before pp, as ruled).
`Cond1–3` (`:45–73`) are the paper's; the decomposition (`:139`) is p. 21's. The sketch
conditions on the generator index before multiplying the κ Cond1 probabilities — the paper's
"independent for every k" holds only given I (BAD depends on I through Vars_j); the Lean avoids
that gap. The binomial bound C(n, k) ≤ (e n / k)^k and bucket tails (`SS/Claim42/Load.lean`)
replace "Stirling's approximation". Faithful.

**Theorem 4.1** (p. 11). On the raw bundle (`SS/Security.lean:102–193`): `jls_secure`,
`jls_subexpSmall` (exponent `min(E·cL, min(E·D·cG, 1))/2`, LPN reindexed along ℓ = κ^E, PRG
along n = κ^{E·D}, slack exponent 1), `jls_subexpSecure`, `theorem41`, `theorem41_subexp`,
`exists_sprg_raw(_subexp)`, all under `P.Realizable π` (Phase B, Dv14), G's security in its seed
length and LPN for the own family. On the primitive (`SS/Targets.lean:319–357`):
`theorem41_of_targets`, `exists_sprg_of_targets(_subexp)` with `hT : ∀ P, P.Targets`, delivering
`Secure ∧ HasComplexityEff d 2 ∧ HasPolyStretch` with modulus = the given schedule.
Subexponential security goes only through `SubexpSmall`/`SubexpHard` (wrappers
`SPRG.Raw.SubexpSecure := SubexpHard S.adv`, `BoolPRG.SubexpSecure`, each with `_iff`). The
"constant locality" premise is `hLoc`; "stretch τ > 1, degree d over ℤ" are `hs`, `R`. Faithful;
the δ ∈ ℚ restriction is F10.

No clause read as vacuous. Advice types are inhabited at every parameter (hop index in
`Fin (κOf L + 1)`; all-zero PRG advice), `PrimeSchedule` is inhabited, the reductions are stated
for every realiser over the shared `RealizesOn`, and SP-W3 removes the constant-length vacuity of
the existence statements. The non-vacuity table does not exhibit a `BoolPRG` (F15).

## 4. Rule 15

| Check (design-r3 §5 item 2; prompt §2) | Result |
|---|---|
| `SPRG`, `BoolPRG`, `LPNFamily` carry their honest algorithms' efficiency as fields, uniform form | Yes. `SPRG.eval_eff` (`SS/Defs.lean:398`, one `PolyTimeComputable` map before κ, p on the input); `SPRG.idSamp_eff`, `sdSamp_eff` (`:399–404`), `BoolPRG.idSamp_eff` (`SS/BoolPRG.lean:99`) and `LPNFamily.sample_eff` (`SS/LPN.lean:402`) are the shared `SamplesEfficiently` with the parameter word on the input; `BoolPRG.eval_eff` (`:94`) |
| No bare `∃ A : NUPPT, A.Computes f`; no per-κ constant; nothing computes p | Yes (grep; `evidence/boundary/bare-computes.log`). `PrimeFind` unused; Bertrand only in `PrimeSchedule.nonempty` |
| **Gate 51 F01's class** (unbounded state or a per-κ escape) | **None found** (F09). No interface is stateful. Inputs of the deterministic fields are bounded (`encIdx_length_le`, `pubLen_le`/`privLen_le` ≤ `seedBound`, `outLen_le`). Draw encodings carry no explicit length field but are bounded through `DrawSamplable` (the `UniformSampler`'s `raw` is polynomial-time and writes `enc` of every outcome; exact on success with failure ≤ 2^{−κ} < 1 for κ ≥ 1). Every witness (f, U, c) is chosen before κ and the public input; T6 chooses one U, c, f before every dimension and schedule (`P := fun _ => PrimeSchedule`) |
| Advice only in reductions and adversaries | Yes: `LPNAdvice`/`PRGAdvice` start with the prime; honest algorithms take `pp` as input |
| Raw bundles carry correctness and security; primitives read them through `toRaw` | Yes: `prop41`, `jls_*`, `theorem41*` on `jlsSPRG_raw`/`lpnFamily_raw`; `SPRG.Secure := S.toRaw.Secure` etc. with `_iff`/`_eq` |
| Values of `SPRG`/`LPNFamily` only from the assembly | Yes: `jlsSPRG` (`SS/Targets.lean:301`) and `Params.lpnFamily` (`:279`), readers `jlsSPRG_toRaw`, `lpnFamily_toRaw` by `rfl`; T1 → `eval_eff`, T3 + T5 → both sampler fields (`SamplesEfficiently.intro` on one draw each), T6 → `sample_eff` |
| Targets named `Prop`s with readers and the Phase B docstring; together inhabit every primitive | Yes: T1 `evalTarget`, T2 `qGenTarget`, T3 `coreTarget`, T4 `lpnPreTarget`/`prgPreTarget`/`ReductionTargets`, T5 `drawSamplerTarget`, T6 `lpnSamplerTarget`, `Targets` (`SS/Targets.lean:72–223`); each map before κ, pp, the schedule and the advice |
| Reductions in the shared `RealizesOn` form; Q-S11 link | Yes: `LPNRealizable`, `PRGRealizable` (`SS/Reductions/LPN.lean:413`, `SS/Reductions/PRG.lean:288`), `prop41`; `realizable_of_targets` (`SS/Targets.lean:232`) is planned through `exists_realizesOn_of_preTarget` with `κOf`/`κOfN`, `.var`, the advice bounds (`lpnAdviceBound`, `prgAdviceBound`) |
| Contract limits: one draw type per field, no product sampler, no `Fintype` binder | Yes |
| Plausibly true targets (a false target makes the primitive headlines vacuous) | Plausible for every `P` (F15): T1–T4 compute G4, the cores and the pre-processing from G's evaluator (R is the unique multilinear representation, recoverable by interpolation in n^d evaluations); T5/T6 need a product `UniformSampler` (Phase B) and ⌊ℓ^{δ/2}⌋ computable — the reason for SP-W1 |

REPORT's rule-15 table (REPORT.md:211–265) matches the source. The ruled Phase A scope holds: no
machine, sampler or RAM program is built; T1–T6 are written, not proved.

## 5. Duplication

See `dup-sweep.md` for the full sweep. Summary: every must-reuse item of the r2/r3 sweeps is used
(LWE family/noise/encodeChallenge, `RealizesOn` and its link, the sampler contract,
`Foundations/Subexponential`, `Encoding.Modular`, `BoolCircuit.encodeList`, `finFunctionFinEquiv`
and friends, `Nat.exists_prime_lt_and_le_two_mul`, `exists_expect_sample_le`). No local
`RealizesOn` or sampler predicate, no subexponential notion of the job's own, no `foldr pairEncode`
re-implementation. Findings: F03 (`κOf`/`κOfN` repeat `PadQuad.nu`), F04 (layering imports),
F05 (two parallel sets of canonical equivalences inside the job). The `weightedTotalDegree`
closure lemmas and `binomial_bound` are the disclosed Mathlib-shaped helpers the sweep foresaw
(F16).

## 6. Process compliance

- **Cache.** Four `lake exe cache get` runs, each with explicit Mathlib roots (80, 81, 82, 83) under
  `lean-slot.sh -k 3` (`evidence/host/slots-io-sprg.log`, 09:11, 09:33, 10:46, 11:23 UTC), the
  reruns after added roots (`evidence/logs/floor-root-addition.json`, `cache-get-*.log`). No
  unfiltered fetch, no `lake build` (0 occurrences in the slot log).
- **Slots.** 675 ACQUIRE, 674 RELEASE, 1 REAP (a seal run whose wrapper died; reaped before the next
  acquisition), all tagged `io-sprg`, at most one held at a time, `k = 1` except the four fetches,
  nothing left held (`evidence/host/slot-summary.json`). The log shows only wrapped runs.
- **Host.** Host addendum and `lean-slot.sh` hash as pinned (`evidence/logs/host-hashes.json`).
  The memory floor first failed (3.92 GiB) and passed on the retry (4.37 GiB), as the addendum
  prescribes.
- **Team limit.** A third sub-agent ran against the prompt's limit of two; it was stopped on
  discovery and ran no Lean (F08).
- **Sources.** The hash was checked before reading; no PDF, image or excerpt in the payload. The
  source folder named in the chat is inside an exchange checkout (F17).
- **Chat rulings recorded only in the payload** (`evidence/route-requests/`, `scope-request/`): F10.

## 7. Findings

### For the worker (relay into the running chat, ruling Q-S8)

Statement-prose changes (F02, F03, F05's merge, F07) are held for Gate 52 so that one
`statements r1` commit carries them with the gate's findings. The payload and REPORT items
(F01, F06) can be relayed now.

**SPRG-C0-F01 · major · the payload is 1,186 MB / 12.5 M lines, about half superseded copies.**
2,649 files. `evidence/rule10/` 728 MB and `evidence/probes/` 287 MB hold two complete Rule 10
passes: the superseded `rule10/m0` (224.5 MB) and `probes/io_sprg_m0` (146.9 MB) beside the current
`rule10/m0_final` (503 MB) and `probes/io_sprg_m0_final` (140 MB), with the seal sources stored
twice in each pass (`rule10/*/seals/` and `probes/*/seals_*`). Also three 13.2 MB `StmtDump.jsonl`
(`evidence/axioms/m0`, `m0-sp-w2`, `m0-sp-w3`), three 33.6 MB `CensusKernel.log`
(`evidence/meta/*/mods/`), 56 MB of failed pretests and a 38 MB log archive
(`rule10/m0_final/failed-implicit-pretest/`, `log-archive/`), 176 untested proof-candidate files
(`evidence/proof-candidates/`) and a byte-identical copy of `REPORT.md` (`evidence/REPORT.md`).
Unlike io-phfe, the seal runs were executed, so the current pass is evidence. The superseded copies
are not, they are permanent in the exchange history (now ≈ 2 GB per clone with io-phfe), and
later checkpoints would repeat them. *Fix:* from the next checkpoint, deliver the current pass only
(logs of executed runs, generators with hashes, not the generated probe sources twice), keep one
copy of a regenerated artifact, compress large JSONL/logs, and move proof candidates out of the
evidence. Do not rewrite history (Q-G52-1, as Q-G51-1).

**SPRG-C0-F02 · minor · campaign labels in Lean docstrings.** `SP-W1`/`SP-W2`/`SP-W3` (22
occurrences, e.g. `SS/Params.lean:47` "SP-W1: δ is rational data, per the user's ruling",
`SS/Defs.lean:283`, `SS/Hybrids.lean:152`, `:162`), "pre-M0"/"M0"
(`SS/LPN.lean:30`, `:359`, `:384`, `SS/BoolPRG.lean:48`, `SS/Encoding.lean:27`). Library
docstrings should state the deviation and its reason in words ("δ is rational so that the rounded
noise schedule is computable by one uniform machine"), not cite worker questions, rulings or
milestones. (The `Dv1`–`Dv18` tags were required by the prompt: F13.) Gate repair.

**SPRG-C0-F03 · minor · `κOf`/`κOfN` repeat `PadQuad.nu`.** `Params.kappaOf P L :=
Nat.findGreatest (fun κ => κ ^ P.E ≤ L) L` and `kappaOfN` (`SS/Params.lean:155`, `:164`) are
`PadQuad.nu P.E L` and `PadQuad.nu (P.E * P.D) N` (base
`Asymptotic/UniversalPadding/Parameter.lean:36`), whose `nu_le`, `nu_pow_le`, `le_nu`,
`lt_succ_nu_pow` (`:43–61`) give `kappaOf_le`, `kappaOfN_le` and the `_pow`/`_n` readers. The
module is imported (`SS/Params.lean:7`, commit "reuse existing bounded power inverse API") but no
Lean text uses it at M0, and REPORT does not say that the definition duplicates `nu`. *Fix:*
`def kappaOf (P : Params) (L : ℕ) : ℕ := PadQuad.nu P.E L` (and `kappaOfN` likewise), readers
unchanged in meaning; or keep the body and disclose the duplicate with the plan to prove the
readers from `nu_*` (gate repair).

**SPRG-C0-F04 · minor · two layering imports.** `SS/Claim42/Load.lean:9` imports
`OneWayFunctions.Basic` for `uprob_pi_forall` (base `OneWayFunctions/Basic.lean:118`, cited only
in the `bucket_tail` sketch), and `SS/Params.lean:7` imports the Levin-padding module
`Asymptotic/UniversalPadding/Parameter` (F03), so the obfuscation area depends on the OWF and
universal-padding areas for two generic lemmas. Neither module is in cleanup Stage 2's scope (the
prompt's "do not import OneWay" is `Asymptotic/OneWay`), so the imports are allowed. Keep them for
Phase A; disclose both in REPORT § Overlap and reuse, and request promotion of `uprob_pi_forall`
to `Foundations/Probability` and of `nu` to a neutral home in a later owner PR (Q-G52-4, as
Q-G51-5).

**SPRG-C0-F05 · minor · two parallel sets of canonical equivalences.** `LPNFamily.Raw.residueEquiv`,
`vectorEquiv`, `matrixEquiv`, `noiseSeedEquiv`, `noiseVectorEquiv` (`SS/LPN.lean:214–267`) and
`ConstructionEncoding.residueEquiv`, `vectorEquiv`, `matrixEquiv`, `noiseSeedEquiv`,
`noiseVectorEquiv` (`SS/Encoding.lean:50–107`) are the same compositions of `ZMod.finEquiv`,
`finFunctionFinEquiv` and `finProdFinEquiv`, once at `F.modulus ℓ` and once at `pp.p`;
undisclosed. *Fix:* one set stated for an arbitrary modulus `q` with `[NeZero q]`, used by both
(gate repair; definitions only, no statement of a theorem changes).

**SPRG-C0-F06 · minor · REPORT mixes stale sub-agent text with the lead's results.** REPORT.md:216
("this reviewer ran no Lean …"), :307, :475–476 ("The lead is collecting those M0 gate artifacts
and must fill the validation table"), :485–490 ("Lead-owned … pending report integration")
contradict the "Current checks" table (:29–44); the fidelity, rule-15 and overlap tables are dated
to snapshot `1a941e8f` "with line references remapped"; REPORT.md:333 cites a host path outside
the payload (`/private/tmp/io-sprg-proof-notes/README.md`). The next checkpoint's REPORT must drop
the superseded text, bind every table to its head, cite only delivered files, and name the
checkpoint-0 commit `15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`.

**SPRG-C0-F07 · minor · facade contents are placeholders.** `Obfuscation/StructuredSeed.lean`
`## Contents`: "`LPN`: the lpn component.", "`BoolPRG`: the boolprg component.", … (19 of 20
lines); both facades' `## Main definitions`/`## Main results` say only "the imported modules
provide …". Write one real line per child (gate repair or landing).

**SPRG-C0-F08 · minor · team limit exceeded.** A child sub-agent started a third research
descendant against the prompt's "at most 2" (prompt §5); it was interrupted on discovery, ran no
Lean, Lake, cache or push, and its duration is unknown (REPORT.md:89–99,
`evidence/host/team-limit-correction.json`). Disclosed and corrected; record it, no further
action.

### Notes (no action, or for the gate)

**SPRG-C0-F09 · note · no analogue of Gate 51 F01.** No sPRG interface threads state between
calls, and every efficiency field's input is polynomially bounded: directly for indices, seeds and
outputs; through the shared `DrawSamplable` for the draw encodings, which carry no length field
(an encoding equals `U.enc` of an outcome the polynomial-time `U.raw` writes; every outcome occurs
for κ ≥ 1 because the sampler is exact on success and fails with probability ≤ 2^{−κ} < 1). At
κ = 0 the failure bound is vacuous, which is harmless for asymptotic efficiency. The gate confirms
this reading of `UniformSampler` (`CoinSampling/Efficiency.lean:93`) or proposes explicit
`encIdDraw`/`encSdDraw` length fields.

**SPRG-C0-F10 · note · chat rulings recorded only in the payload.** (i) SP-W1 (E-ROUTE): T5 cannot
hold for an arbitrary real δ (a uniform sampler of `Fin W` would compute ⌊ℓ^{δ/2}⌋), so
**δ : ℚ** — Seyoon's answer "Use rational δ throughout, coercing it to real values for analysis"
(`evidence/route-requests/SP-W1.txt`). This changes design-r2 §4.6's `δ : ℝ` and restricts
Theorem 4.1's "δ ∈ (0, 1) arbitrary" to rationals; no generality is lost in substance (δ-LPN
implies δ′-LPN for δ′ < δ, since 𝒟_r and 𝒟_{r′} noise compose exactly), but the Lean has no such
bridge and the docstrings do not say why it is harmless. (ii) SP-W2: two hybrid identities
restated as equalities of acceptance probabilities (the free `OracleComp` programs differ by an
unused query; correct). (iii) SP-W3: `HasPolyStretch` gains `κ ≤ seedBits` (a real vacuity: a
zero-length "sPRG" met the old form). (iv) the AGENTS.md override for slot-wrapped Lean
(`evidence/scope-request/lean-check-approval.txt`). (ii)–(iii) were taken under "use your best
judgment" (`judgment-authorization.txt`). All are pre-freeze and disclosed; they belong in
`rulings.md` (Q-G52-2, as Q-G51-3).

**SPRG-C0-F11 · note · size.** M0 is 5,911 lines against an M0 estimate of 2,100–3,200;
REPORT.md:462–467 re-estimates the job at 8,500–11,500 lines against the pack's 4,950–8,450
(Q-G52-3).

**SPRG-C0-F12 · note · the two jobs' prime schedules differ.** The sPRG uses
`PrimeSchedule := (κ : ℕ) → PrimeParam κ` with 2^κ ≤ p ≤ 2^{κ+1} (`SS/Defs.lean:48–72`); io-phfe
uses `p : ℕ → ℕ` with `hp : ∀ κ r, (G.inst κ r).order = p κ` and no width bound
(`Pairing/MatrixDH/Parameters.lean:135` at io-phfe's `70b85f9b`). JLS26 Theorem 5.1 composes both
at one λ-bit p, so a consumer needs `p κ = (π κ).p` and the width. (Gate 51's dup-sweep S6 assumed
the sPRG used the pairing groups; it does not.) Q-G52-5.

**SPRG-C0-F13 · note · `Dv` tags and `[PS10]`.** 334 docstring occurrences of `Dv1`–`Dv18` refer to
the design note, which is not in the library; the prompt required them, and almost every
occurrence also states the deviation in words. Every module cites [PS10, Def 26.8] for NUPPT,
including modules with no adversary (`Degree`, `PolyTerms`, `Buckets`, `SparseFactor`,
`Claim42/Load`), as the prompt asked. For the landing: keep the words, drop or footnote the tags.

**SPRG-C0-F14 · note · `sorryAx` in definitions through named field theorems.** `lpnFamily_raw`
(`noiseDenAt_pos`, `lpnModulus_le_pow`), `jlsSPRG_raw` (`primeWidthBound`, the injectivity and
length theorems), the instances `instWNeZero`/`instBNeZero` (`W_pos`, `B_pos`), the default
`PRGAdvice` (`B_pos`) and the assembly depend on sorried theorems (265 transitive dependents).
Allowed at M0 (prompt §6), disclosed (REPORT.md:310–312, :388–391); must be empty at the final.

**SPRG-C0-F15 · note · plausibility of the targets and of the inputs.** `exists_sprg_of_targets`
assumes `∀ P : Params, P.Targets`, over every `BoolPRG` and representation. T2 needs R's term lists;
`MultilinearRep.TermsEfficient` (`SS/BoolPRG.lean:245`) is defined but used nowhere, which is
consistent because a multilinear representation is unique and computable by interpolation from
`eval_eff`. The non-vacuity table covers advice and schedules but exhibits no `BoolPRG` (needing
`eval_eff` and a `UniformSampler`); a trivial generator plus the contract's
`samplesEfficiently_residue` should give one. The gate assesses both.

**SPRG-C0-F16 · note · duplication evidence is partly textual at M0.** The Rule 10 seals, controls and
unfold scan were run; the `exact?`/`apply?` probes of the overlap plan were not (REPORT.md:347–352).
The new `Internal.weightedTotalDegree_*` closure lemmas (`SS/Degree.lean:70–110`; absent from
Mathlib at the pin) and `Internal.binomial_bound` (`SS/Claim42/Load.lean:54`; only private or
inline copies in TCSlib) are the disclosed helpers the sweep anticipated; upstream candidates.

**SPRG-C0-F17 · note · process.** The source folder the worker used,
`…/tcslib_all_branches/tcslib-exchange/sources` (`evidence/route-requests/SP-W1.txt`), sits inside
an exchange checkout, where a careless `git add -A` would stage the PDF (as Gate 51 F16); Gate 52
uses `~/tcslib-sources`. One wrapper reaped without RELEASE; the memory preflight passed on retry.

## 8. Questions for Seyoon (multiple choice, recommended first)

- **Q-G52-1 (F01, payload size; the same question as Q-G51-1).** (A, rec.) Accept checkpoint 0 as
  delivered and relay F01, so that later checkpoints carry the current pass, generators, hashes and
  executed logs only. (B) Also ask for a follow-up commit deleting the superseded `rule10/m0`,
  `probes/io_sprg_m0`, the duplicate dumps and the proof candidates from the tip (the history keeps
  the 1.19 GB). (C) No action.
- **Q-G52-2 (F10, chat rulings; as Q-G51-3).** (A, rec.) Confirm SP-W1 (δ ∈ ℚ), SP-W2, SP-W3 and the
  AGENTS.md override, and have them recorded in `sprg/rulings.md`. (B) Confirm SP-W2, SP-W3 and the
  override, but revisit SP-W1 through the gate (for example real δ with a separate computable
  rational approximation in `Params`).
- **Q-G52-3 (F11, size; as Q-G51-2).** (A, rec.) Continue: a checkpoint per milestone and a
  re-estimate at each; a PARTIAL final with the remaining obligations listed is acceptable.
  (B) Pause for a scope cut.
- **Q-G52-4 (F04, layering; as Q-G51-5).** (A, rec.) Keep both imports for Phase A, with the
  disclosed request to promote `uprob_pi_forall` and `PadQuad.nu` in a later owner PR. (B) Ask for
  private local copies now (disclosed duplicates) and drop the imports.
- **Q-G52-5 (F12, prime schedules).** (A, rec.) Unify at landing: one shared prime-schedule notion
  (the sPRG's `PrimeParam`/`PrimeSchedule` moved to a neutral home, the PHFE generator stated
  against it); no change now in either job. (B) Relay a statements repair to io-phfe now, adding
  the width bound to its schedule. (C) Leave them separate; the Theorem 5.1 consumer bridges them.
- **Q-G52-6 (Gate 52 Mathlib packages; as Q-G51-6; see `dispatch.md`).** (A, rec.) The gate's
  worktree links its `.lake/packages` read-only to the io-sprg worktree's (same base, same
  manifest) and never runs `lake`. (B) One narrowed `lake exe cache get` for the gate under
  `lean-slot.sh -k 3`, which waits until all three slots are free.
