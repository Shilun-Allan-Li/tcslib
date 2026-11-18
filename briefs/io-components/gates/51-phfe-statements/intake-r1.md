# io-phfe checkpoint 0: maintainer intake r1 (static)

Static intake of the io-phfe checkpoint-0 (statements) delivery. No Lean, `lake` or build was run;
the Lean checks are Gate 51's (`pack.md`). Prepared 2026-11-18 on the records branch at
`8be2c0fa47b3fd3d8654eebead034f6a68efb791`.

| Item | Value |
|---|---|
| Delivery | `exchange/pass-shelat-ch5-8` at `1e77173a7032b57aa22260787711c6c7a1b7596e`, path `inbox/fills/io-phfe/`, subject "fill io-phfe: checkpoint 0 (statements)", unsigned, parent `b11b9408b830b855b220ee1c3c80429abea6830c` |
| Source HEAD (worker's local `fill/io-phfe`) | `70b85f9ba83f27393d98fa5bf88505aea3d22a8d` (25 commits, `patches/COMMITS.tsv`) |
| Base | `iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` |
| Records pin of the dispatch | `dbea2807532392781304e004715f3b0190025f5e` |
| Pack | `briefs/io-components/phfe/` (rulings.md > dispatch-prompt-r3 > design-r3 > design-r2) |

Everything in the delivery was read as data. Paths below without a prefix are under
`inbox/fills/io-phfe/`; `FE/` is `src/TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/`.
Line numbers are at the delivery commit.

## Verdict

**Checkpoint 0 accepted for Gate 51, with one blocker to repair through the gate.** The delivery is
complete, integral and in scope. The statements follow the pack closely: GJLS21 Def. 4.3 is derived
from Wee20's semi-adaptive notion by an exact game identity, the raw/efficient split of rule 15 is in
place, and the vacuity and R-DLOG rules are respected. The blocker (F01) is a gap in the efficient
simulator interfaces: their per-call efficiency does not bound the simulator's state, so it does not
make the simulator PPT. Its fix is mechanical. It changes frozen statement text, so it goes through
Gate 51 as a statements repair (ruling Q-S8). One major (F02) is about payload hygiene, not Lean.

| Severity | Count | IDs |
|---|---:|---|
| blocker | 1 | F01 |
| major | 1 | F02 |
| minor | 8 | F03–F10 |
| note | 9 | F11–F19 |

## 1. Integrity

- **SHA256SUMS** verifies 1739/1739: every listed path is delivered, none is unlisted, 0 mismatches.
  Hashes were streamed from the commit's blobs (`git cat-file --batch`; script
  `$SP/g51/scripts/verify_sums.py`). No `.pdf` anywhere in the payload.
- **Delivery commit scope.** All 1,740 changed paths are under `inbox/fills/io-phfe/`, insertions
  only (`git diff --shortstat`: 1740 files, +24,269,210 lines). Layout as the prompt §10 requires:
  `REPORT.md`, `SHA256SUMS`, `patches/` (25 patches + `COMMITS.tsv`), `src/` (76 files), `evidence/`.
- **`src/` is exactly base + patches.** Applying the 25 patches in order to the base's two facades
  reproduces `src/` byte for byte (`diff -r` empty). The patches create only new files apart from the
  two facades (two renames inside new files, patch 0020).
- **Additive over the base.** 74 new modules (13,745 lines, 144 `sorry`; REPORT's counts confirmed
  independently) and two modified existing files, both permitted by prompt §3:
  - `TCSlib/Cryptography/Pairing.lean`: 3 import lines, 3 Contents bullets, 5 References entries;
  - `TCSlib/Cryptography/AdvancedEncryption.lean`: 1 import line, 1 Contents bullet, 5 References
    entries.
  No other base file changes (`evidence/logs/m0-frozen-scope-final.txt` agrees).
- **Paths.** All new files are under `Pairing/{Exponents,Linear,MatrixDH}.lean`, `Pairing/MatrixDH/**`,
  `AdvancedEncryption/FunctionalEncryption.lean` and `FunctionalEncryption/**`, as prompt §3 allows.
  The layout is finer than design-r3 §3's table (F15).
- **Static checks recounted.** 0 lines over 100 characters, 0 files over 1,000 lines, no `@[simp]` or
  `attribute`, no `native_decide`, `admit` or `axiom`; every `sorry` is in a `theorem` (none in a
  definition or instance); no campaign labels, dates, gate numbers or records paths in Lean text.
- **Build binding.** `evidence/build/summary.tsv`: 285 modules, rc 0, both error forms 0. 274 rows
  were checked at `1e247f3f` and rebound to `70b85f9b` (byte-equal); the 11 rows checked at
  `70b85f9b` are exactly the facades changed by the last patch, and no non-facade module imports a
  changed facade, so the rebinding is sound.

## 2. Checkpoint-0 contents (design-r3 §6 M0; prompt §6)

| Required | Status |
|---|---|
| Every file with definitions and readers; raw bundles, efficient interfaces, targets, assembly | Present. Readers are proved (`rfl`/`Iff.rfl`); the 144 `sorry`s are all substantive theorems |
| Theorems stated with `sorry` under sketches | Present; `dev/sk15` passes (`evidence/logs/m0-sk15-final.log`) |
| Reduction functions with role, game and slack in docstrings | Present (`red0`, `red1`, `red2`, `red3`, `dlinToMddh`, `toLinear`, `toQuadratic`, `TwoStage.toSA`); REPORT.md:516–590 tabulates them |
| Fidelity tables, GJLS21 first | REPORT.md:46–120 (Defs 4.1, 4.2, 4.3 with Remarks 4.3/4.5/4.6, 4.6, §9) |
| Then Wee20 §2.2 and the Wee20/AGW20/IW14 table | REPORT.md:121–321 (notion, algorithms, Games 0–4, Π, Lemmas 2–5, W1–W5 and R1–R4, AGW20 (28)–(32), IW14 Def 1, Thm 3, §4.2) |
| Rule-15 table | REPORT.md:369–405 |
| Facade lines | Present (§1) |
| Size re-estimate | REPORT.md:718–722: 13.7k lines of statements now, final "roughly 20k–30k" (F14) |
| M0 checks | Elaboration (§1); decls2 ADDED 1171 / 0 / 0; StmtDump; axioms (1,933 standard-only, 292 sorryAx-dependent, 0 other); lint, widths, clash scan. Rule 10 seals are prepared, not run (allowed at M0; F17) |

## 3. Fidelity spot-check against the PDFs

All five PDFs hash as `sources-r3.md` §1 / `rulings.md` (checked in `$SP/io-sources`).

**GJLS21 Def 4.1** (printed p. 19). `FEScheme.Raw` (`FE/Defs/Raw.lean:74`) has pp-dependent
types, core-plus-draw Setup/Enc/KeyGen and a deterministic `dec … → Option DecOut`; Enc takes
`pk, x, y` and no msk; the ciphertext excludes `x`, which Dec takes separately. Faithful. PPGen
draws a group description and a uniform g ∈ G* (`Pairing/MatrixDH/Parameters.lean:56`, `:118`); this
needs the extra efficiency field `pubGen_eff` (`FE/Defs/Efficient.lean:48`), a deviation from
design-r3 §1E.1 ("no new field") that the worker reports as approved in chat (F12).

**Def 4.2** (p. 19). `Correct` (`FE/Defs/Correctness.lean:122`) is perfect correctness on every
honest outcome and every wire `x, y, f`; `CorrectExcept` (`:134`) is the probabilistic form;
`Correct.correctExcept_zero` is proved. Stronger than the source; faithful.

**Def 4.3** (pp. 19–20), ε = 1, Remarks 4.3 and 4.6. `simGame` (`FE/Simulation/Games.lean:145`)
draws A₁'s coins and runs it on 1^κ before pp, then the real view (`:100`: pp, Setup, Enc, ordered
KeyGen) or the ideal view (`:121`: pp, Sim.setup, Sim.enc on ω, Sim.key per index, state threaded);
A₂ gets ⟨st, pp, pk, keys, x*, ct*⟩. ω carries x*, the functions and their values in ℤ_p (Q1 A,
justified by Thm 9.2's proof, Hybrid 1, printed p. 61 = PDF 65, where ω carries the scalars vᵢ;
checked). `SimSecure` (`FE/Simulation/Security.lean:58`) is ∃ efficient `Simulator`, ∀ `TwoStage`,
∀ q, negligible. Faithful, with two remarks:
- the efficient `Simulator` interface does not make the simulator PPT (**F01**);
- Def 4.3 literally places "∃ negl" before "∀ λ, all polynomials prmtr"; the Lean reads it per
  scheme instance (ℓ, n, d fixed), which is the only sensible reading but is not recorded (F03).

**Def 4.6** (p. 22). `LinearEfficient G` (`FE/Wee20/Targets/LinearEfficiency.lean:84`): one `FinTM`
and one polynomial before all numeric ℓ, n, d, κ and every typed pk, x, y and draw, time
(ℓ+n)·q(κ) when 0 < ℓ+n. Stronger than the source (uniform machine, all keys), modulo the TM-to-
circuit overhead, which is O(T log T) for multi-stack machines and is absorbed because ℓ, n are
polynomial in κ. The 0 < ℓ+n guard is disclosed (REPORT.md:105). It is a target, carried by the
headline from `hT.linear` (F19).

**§9 class** (printed pp. 57–58). `phfeClass ℓ n w d` (`FE/Classes.lean:315`) evaluates
Σ_{j,k} f_{j,k}(x) y_j y_k with each f_{j,k} a degree-≤ d polynomial in x̂ = (x, 1), coefficients on
padded tuples (`PolyTensor`, `:62`), over the drawn order, values embedded into G_T by the scheme.
Constant d covers arithmetic NC⁰ (constant degree); separate ℓ, n generalize the common n′.
`pad_one` (`:560`) states the bidegree-(d, 2) completeness. Faithful.

**Wee20 §2.2** (p. 5). `saGame` (`FE/SemiAdaptive/Games.lean:225`): pp, then Setup or Sim.setup;
the adversary gets (pp, mpk), commits (x*, z*) once, gets ct*, then queries keys adaptively
(rejected before the challenge); the ideal key handler gives Sim.key exactly (x*, f, f(x*, y*)).
`SASimulator.Raw` (`FE/SemiAdaptive/Simulator.lean:48`) threads state from Enc* to KeyGen*, which
Wee20 needs (its KeyGen* uses Enc*'s y₁, y₂, §3.2 p. 7). Faithful; F01 applies here too.

**Def 4.3 from §2.2.** `TwoStage.toSA` (`FE/SemiAdaptive/FromTwoStage.lean:220`) asks the
challenge, then the q committed keys in order (budget q + 1, coins A₁ ‖ A₂), and `toSim` (`:55`)
restricts the simulator; `simAdv_eq_saSimAdv` (`:271`) is stated exactly, not as an abstract
implication. The query log is oldest-first (`Games.buildComp` appends), so `saNext`'s `e :: es`
reads the challenge answer first, as intended.

**AGW20 Lemma 2** (p. 12) and **App. A (28)–(32)** (pp. 37–38). `PartialGarbling.Raw`
(`FE/PartialGarbling/Defs.lean:181`): L₁ : (TIdx ⊕ Fin n′) × (Fin ℓ × MIdx), L₀ : (TIdx ⊕ Fin n′) ×
MIdx, i.e. (m + n′ − 1) × ℓm and (m + n′ − 1) × m, matching (32) ("n matrices of size
(m+n′−1)×m"); the printed shapes in Lemma 2 are swapped (W1; confirmed). `pgbCore`/`pgbStarCore`
are (z − t̲, tᵀ(L₁(x ⊗ I) + L₀)) and (−t̲, … + µe₁), as Lemma 2. `rec_spec` (`:234`) holds for every
t; `privacy` (`:238`) is an exact equality of laws (IW14 Def 1, "identically distributed"; R4).
The layered instance's L₁/L₀ (`FE/PartialGarbling/Layered.lean:181`, `:198`) satisfy `rec_spec` and
the translation by hand (forward values cancel every internal row; the shift by backward values
leaves µ at the root; d = 0 included). Faithful.

**Wee20 Π** (§4.2, pp. 9–10; App. B pp. 12–14). Shapes A 2×3, W 3×z, U 3×2ℓ, V 3×2, T 3×t, R 2×m
and T̄ = the n′ output columns match. Π's simulator's printed "full rank with probability 1 − 1/p"
is wrong for unconditioned uniform (A|c); the delivery uses the exact
F(p) = p⁻¹ + p⁻² − p⁻⁴ − p⁻⁵ + p⁻⁶ (checked; F(2) = 43/64), but this misprint is not in the W table
(F04).

No clause read as vacuous. Core inequalities are stated for every typed adversary; the realisability
`Prop`s (`FE/Wee20/PHFE/Security.lean:126`, `:173`) quantify only over `toSAAdv A q` and
`A.toSA q`, as the vacuity rule requires.

## 4. Rule 15

| Check (design-r3 §6 gate order, item 2) | Result |
|---|---|
| `FEScheme`, `Simulator`, `SASimulator`, `PartialGarbling` carry efficiency fields, uniform form | Yes: `SamplesEfficiently` (shared contract) for every sampler; `∃ a, PolyTimeComputable a ∧ …` before κ for Dec, lgen, rec. **But the simulator fields do not bound the state (F01)** |
| No bare `∃ A : NUPPT, A.Computes f` | None (grep; `evidence/static-m0-final/summary.json`) |
| No per-κ constants; modulus from pp | Yes: `orderParam` from the drawn group; PG takes p on the input, quantified after the witness |
| Advice only in reductions and adversaries | Yes; reduction advice is `ZMod (p κ)`, cast by `ZMod.ringEquivCongr` |
| Raw bundles carry correctness and security | Yes; raw headlines take `hPG`, `hR`, `hM`, `h` and no target |
| Values of the four interfaces built only by the assembly | Yes: only `FE/Wee20/Targets/Assembly.lean` (`layeredPG`, `wee20PHFE`, `wee20Sim`, `wee20SASim`, with `_toRaw` readers by `rfl`) |
| Targets are named `Prop`s with readers and the Phase B docstring | Yes: `SchemeTargets`, `SimTargets`, `PGTargets`, `LinearEfficient`, `MddhPreTargets`, `Targets` (F05 on `MddhPreTargets`) |
| Reductions in the shared `RealizesOn` form | Yes (60 uses; no local variant); `mddhRealizable_of_preTarget` is proved through `exists_realizesOn_of_preTarget_id` |
| Contract imports only where allowed | `CoinSampling.Contract` in `Defs/Efficient`, `SemiAdaptive/Simulator`, `Wee20/Targets/Scheme` only; no other `CoinSampling` module, no `Games.Closeness` |

REPORT's "Efficiency targets are intentional Phase B obligations" (REPORT.md:29–30) matches the ruled
Phase A scope (*Strategy and uniformity* (1); rule 15 "in Phase A the targets are written, not
proved"). No machine, `PolyHandler`, RAM program or sampler is built.

## 5. Duplication

See `dup-sweep.md` for the full sweep. Summary: every must-reuse item of `duplication-sweep-r3.md`
is used (realisation API, sampler contract, oracle-game machinery, averaging, `Fin.snoc`,
`finFunctionFinEquiv`, `kroneckerMap`, `card_GL_field`, Subexponential API). No local
`RealizesOn`, `SamplesEfficiently`, `DrawSamplable` or `CoreComputable`; no DLIN/MDDH exists at the
base; no deterministic oracle interpreter exists at the base (`runDet` is new and disclosed). Findings:
F06 (Pairing → IBE import), F07 (disclosed GT near-copies), F08 (undisclosed `encodeList` pattern).

## 6. Process compliance

- **Cache.** Five `lake exe cache get` runs, every one with explicit Mathlib roots under
  `lean-slot.sh -k 3` (`evidence/logs/slots-io-phfe.log` lines 1, 55, 261, 377, 643; logs
  `cache-get*.log`, rc 0, "No files to download" from the third on); each rerun follows added roots
  (`mathlib-roots-added-{2,3,4}.txt`, `mathlib-roots-before-5.txt`). No unfiltered fetch, no
  `lake build`.
- **Slots.** 621 ACQUIRE/RELEASE pairs, all tagged `io-phfe`; at most one held at a time; `k = 1`
  except the five cache fetches; nothing left held. The log shows only wrapped runs, so it cannot
  prove the absence of unwrapped ones; REPORT.md:636–640 asserts none.
- **Host.** Host addendum and `lean-slot.sh` hash as pinned (`evidence/logs/host-sha256.txt`). The
  memory floor first failed (3.77 GiB) and passed on the scheduled retry (4.74 GiB), as the addendum
  prescribes.
- **Sources.** Hashes recorded before reading (`evidence/logs/sources-sha256.txt`); no PDF, page
  image or excerpt in the payload (the source reviews are paraphrases).
- **Claims without evidence in the payload:** the chat rulings (F12), and REPORT's prepublication
  lines (F10). Rule 10 and `exact?`/`apply?` probes are openly pending (F17).

## 7. Findings

### For the worker (relay into the running chat, ruling Q-S8)

Statement-text changes (F01, F05, F07's promotion, F09) are held for Gate 51 so that one
`statements r1` commit carries them with the gate's findings. The REPORT and payload items
(F02, F03, F04, F08, F10) can be relayed now.

**PHFE-C0-F01 · blocker · simulator state is unbounded, so the efficient simulators need not be
PPT.** `Simulator.Raw.St`/`encSt` (`FE/Defs/Simulator.lean:89–93`) and `SASimulator.Raw.St`/`encSt`
(`FE/SemiAdaptive/Simulator.lean:50–54`) have no width bound; `encSt` is only injective. The
efficiency fields (`FE/Defs/Simulator.lean:230–247`, `FE/SemiAdaptive/Simulator.lean:209–227`) give
one polynomial-time core per call, polynomial in the length of its input, which includes the
encoded state. A key core may double the state on every call, so after q(κ) adaptive key queries the
state and the running time are exponential, yet every field holds. Hence `SimSecure` and
`SASimSecure` (∃ efficient simulator) are weaker than GJLS21 Def 4.3 and Wee20 §2.2, which require
a PPT simulator, and a consumer that runs the simulator inside a reduction (GJLS21 Thm 9.2's
hybrids) cannot use them. The concrete Wee20 simulators have fixed-width state, so no theorem about
them changes. *Fix:* give both raw simulators a `stLen : PolyExpr` and a fixed-width injective
`encSt : St κ pp → Fin (stLen.eval κ) → Bool` (inputs/outputs via `List.ofFn`), carried by `toSim`;
or add an explicit `(encSt κ pp s).length ≤ stLen.eval κ` field. Apply as a gate repair.

**PHFE-C0-F02 · major · the payload is 812 MB / 24.3 M lines, almost all unexecuted inputs.**
`evidence/rule10-m0-final/seals/` holds 604 files, 742 MB, of prepared seal sources and requests
for the four variants; `evidence/rule10-m0-final/STATUS.md` says "All four Rule10 seal variants are
prepared but unexecuted". Also: three near-identical copies of the Rule 10 preparation
(`rule10-m0`, `rule10-m0-r2`, `rule10-m0-final`, 2.8–3.4 MB each besides the seals), the 17.9 MB
`statements/StmtDump.jsonl` and 17.5 MB of census logs. None of it is evidence of an executed check,
it is now permanent in the exchange history (812 MB per clone), and later checkpoints would repeat
it. *Fix:* from the next checkpoint, deliver generators with their hashes and the logs of runs
actually executed; keep only the final copy of a regenerated artifact; compress large JSONL. Do not
rewrite history (Q-G51-1).

**PHFE-C0-F03 · minor · Def 4.3 / 4.2 parameter-quantifier reading not recorded.** GJLS21 Def 4.3
(p. 20) reads "there exists a negligible function negl such that for all … λ, all polynomials
prmtr"; the Lean fixes (ℓ, n, d) in the scheme and takes negl per (A, q) (`FE/Simulation/
Security.lean:48`). Correct reading; add a row to REPORT.md:76–97 (and the Def 4.2 table).

**PHFE-C0-F04 · minor · Π's rank misprint missing from the misprint table.** REPORT.md:217–228
documents that Wee20's "full rank with probability 1 − 1/p" (p. 10) fails for the unconditioned
draws (exact F(p), F(2) = 43/64), but the W/R table (REPORT.md:243–255) lists only W1–W5. Add it
(W6), with the location.

**PHFE-C0-F05 · minor · `MddhPreTargets` has an unused machine binder.**
`FE/Wee20/Targets/MatrixDH.lean:44–45`: `∀ p hp d ℓ (_D : NUPPT), ∃ f …`. `_D` is unused, and the
witness may depend on (p, hp, d, ℓ). That is acceptable for an L1 reduction (advice allowed), but
the docstring says "the witness is chosen before κ, every advice value and every challenge" without
saying it follows d, ℓ and the schedule. Drop `_D` and say so (gate repair).

**PHFE-C0-F06 · minor · `Pairing/MatrixDH/SelfReduction.lean` imports an IBE machine module.**
`:11` imports `AdvancedEncryption.IdentityBased.BonehBoyenMachine.Draws` only for
`BB1Machine.order_le_two_pow` (base `…/BonehBoyenMachine/Draws.lean:156`), so a Pairing assumption
module now depends on an IBE construction (layering inversion). Disclosed with a promotion request
(REPORT.md:414). (`:9`'s `Lamport.Averaging` import is the must-reuse `exists_expect_sample_le`.)
Keep the import for now; promote the lemma to `Pairing/Group.lean` in a later owner PR (Q-G51-5).

**PHFE-C0-F07 · minor · disclosed GT near-copies.** `pow_val_add_GT`, `pow_val_neg_GT`
(`src/TCSlib/Cryptography/Pairing/Exponents.lean:182`, `:189`) mirror the base's source-group
`pow_val_add`, `pow_val_neg` (`Pairing/Group.lean:254`, `:260` at the base). Disclosed
(REPORT.md:410). The proofs must reuse `pow_mod_card`/`card_GT` as sketched; list them as a
requested promotion to `Pairing/Group.lean`.

**PHFE-C0-F08 · minor · undisclosed re-implementation of `encodeList`.** 21 sites spell
`(… ).foldr pairEncode []` (`FE/Simulation/Games.lean` ×4, `FE/Defs/Simulator.lean` ×2,
`FE/Wee20/WireDraws.lean` ×14, `FE/Wee20/PHFE/Simulator.lean` ×1). This is the base's
`Encryption.PrivateKey.EnsembleSecurity.encodeList` (`EnsembleSecurity.lean:103`). It is an
encoding, not a re-proved lemma, but it is not in REPORT § "Overlap and reuse". Disclose it, or
reuse `encodeList` where the statement allows.

**PHFE-C0-F09 · minor · Pairing facade cites papers no Pairing module uses.**
`src/TCSlib/Cryptography/Pairing.lean:44–48` adds [AGW20] and [IW14] to `## References`; no
`Pairing/**` file cites them. Drop them (gate repair).

**PHFE-C0-F10 · minor · REPORT is a prepublication snapshot.** REPORT.md:3 ("ready for the
authorized publication"), :25 ("Its receipt follows in the chat"), :601 ("no push yet") and :603
("Checkpoint0 / freeze / push | None claimed; first push remains pending") are stale at the delivery
commit. The next checkpoint's REPORT must name the checkpoint-0 commit
`1e77173a7032b57aa22260787711c6c7a1b7596e` and the start of the freeze.

### Notes (no action, or for the gate)

**PHFE-C0-F11 · note · the machine adapter is not under `Complexity.NUPPT`.** Design-r3 §4.5
sketched `_root_.Complexity.NUPPT.toSAAdv`; the delivery defines `FunctionalEncryption.toSAAdv`
(`FE/SemiAdaptive/Data.lean`), disclosed at REPORT.md:649. This keeps the job out of another area's
namespace; accept.

**PHFE-C0-F12 · note · chat rulings are recorded only in the payload.**
`evidence/logs/rulings.json`: (i) Lean route through the slot wrapper; (ii) **include g in PPGen,
add `pubGen_eff` and its target** (a deviation from design-r3 §1E.1); (iii) best judgment while
Seyoon was away. These belong in `rulings.md` / the decision log (Q-G51-3).

**PHFE-C0-F13 · note · `PGSound` hypothesis.** The raw correctness and security theorems take
`hPG : PHFE.PGSound PG` (`FE/Wee20/PHFE/Data.lean:63`: `PG.eval = polyTensorEval`), where design-r3
§1E.3 said "any `PartialGarbling.Raw`". The hypothesis is necessary (the class evaluates
`polyTensorEval`), disclosed (REPORT.md:43) and discharged for the layered instance
(`PHFE.layeredPG_sound`) in the primitive headlines. Accept.

**PHFE-C0-F14 · note · size.** Checkpoint 0 is 13,745 lines against an M0 estimate of 2,500–3,700;
REPORT.md:718–722 projects 20k–30k lines in all against the pack's 8,800–16,100 (Q-G51-2).

**PHFE-C0-F15 · note · layout.** 74 modules against design-r3 §3's 18–22 + facade: `Defs/`
(Raw, Correctness, Simulator, Efficient), `Simulation/`, `SemiAdaptive/`, `PartialGarbling/Defs`,
`Wee20/PHFE/`, `Wee20/Targets/`, `Wee20/Wire*`, `Pairing/MatrixDH/Parameters`. All are in the
permitted trees, every file is under 600 lines, and `PublicParams` lives in the Pairing namespace.
The sPRG job builds over the same groups: the two jobs' public-parameter types should not diverge
(for the gate and the landing).

**PHFE-C0-F16 · note · process.** Compliant (§6). Two remarks for Seyoon: before the source folder
was supplied, the worker ran filename-only searches under `~/phd_experiments`, `~/Downloads`,
`~/Documents`, `~/Desktop`, `~/.codex` and `/private/tmp`
(`evidence/logs/source-status-initial-historical.txt`); and the source folder it then used sits
inside the exchange checkout (`…/tcslib-exchange/sources`, REPORT.md:619), where a careless
`git add -A` would stage the PDFs. A folder outside every checkout (`~/tcslib-sources`) is safer.

**PHFE-C0-F17 · note · duplication evidence is textual at M0.** Rule 10 seals, controls, the
explicit-unfold scan and the `exact?`/`apply?` probes were not run (`evidence/rule10-m0-final/
STATUS.md`; REPORT.md:825–829). Allowed at M0 (prompt §6), but the reuse claims rest on text search
until the final.

**PHFE-C0-F18 · note · encryption draws depend on the private input.** `FEScheme.Raw.EncDraw`
(`FE/Defs/Raw.lean:112`) is indexed by `pk, x, y` (and `KeyDraw` by `msk, f`). General and harmless
(the draw is internal; the sampler's parameter word carries `y`); the concrete scheme's draw is
fixed.

**PHFE-C0-F19 · note · `LinearEfficient` is about `G`, not about the instance.** It quantifies over
numeric ℓ, n, d and the `PHFE.encCore` of each; `wee20PHFE_gjls21` returns `hT.linear` unchanged
(`FE/Wee20/PHFE/Headlines.lean:125`). As designed for Phase A; the gate should confirm the
(ℓ + n)·q(κ) time target implies Def 4.6's circuit bound (overhead O(T log T), absorbed since
ℓ, n ≤ poly(κ)).

## 8. Questions for Seyoon (multiple choice, recommended first)

- **Q-G51-1 (F02, payload size).** (A, rec.) Accept checkpoint 0 as delivered and relay F02 so that
  later checkpoints carry generators, hashes and executed logs only. (B) Also ask for a follow-up
  commit deleting `evidence/rule10-m0*/seals/` and the duplicate Rule 10 copies from the tip (the
  history keeps the 812 MB). (C) No action.
- **Q-G51-2 (F14, size).** (A, rec.) Continue under Q4 (A): PARTIAL final allowed, order M0, M2, M3,
  M1, M4, M5, a checkpoint per milestone, and the worker re-estimates at each. (B) Split now into two
  jobs (generic FE + garbling + Π; quadratic layer + headlines). (C) Pause for a scope cut.
- **Q-G51-3 (F12, chat rulings).** (A, rec.) Confirm the three chat rulings (slot-wrapped Lean;
  `pubGen_eff` with its target; best judgment, disclosed) and have them recorded in `rulings.md`.
  (B) Revert `pubGen_eff`: keep PPGen as design-r3 states and state g's sampling efficiency as a
  separate target outside `FEScheme`.
- **Q-G51-4 (F01, timing).** (A, rec.) Hold F01 for Gate 51, which grades it, and relay it with the
  gate's findings in one `statements r1` commit. (B) Relay F01 now as its own statements repair, and
  let the gate audit r1.
- **Q-G51-5 (F06).** (A, rec.) Keep the BB1 import for Phase A, with the disclosed request to promote
  `order_le_two_pow` to `Pairing/Group.lean` in a later owner PR. (B) Ask the worker for a private
  local copy now (a disclosed duplicate) and drop the import.
- **Q-G51-6 (Gate 51 Mathlib packages; see `dispatch.md`).** (A, rec.) The gate's worktree links
  its `.lake/packages` read-only to the io-phfe worktree's (same base, same manifest) and never runs
  `lake`. (B) One narrowed `lake exe cache get` for the gate under `lean-slot.sh -k 3`, which waits
  until all three slots are free.
