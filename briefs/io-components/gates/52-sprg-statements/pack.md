# Gate 52 · io-sprg statements gate (checkpoint 0) · round 1

The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). It runs
in a local checkout on Seyoon's Mac, because it needs the source PDF from a local folder and one
Lean slot.

This is the **statements gate** of the io-sprg job (design-r3 §5; prompt "Two separate audits gate
the job"). It audits the job's checkpoint 0, the M0 statements commit: the structured-seed PRG of
[JLS26, §2–§4] (Defs 2.3, 3.1–3.4; the construction; Claims 4.1–4.2, Lemma 4.2, Proposition 4.1,
Theorem 4.1), Phase A, as JLS26 Theorem 5.1 consumes it. The proofs gate on the final delivery is
separate.

## Pins

All hashes are full; take them from this file, never retype them.

| Item | Pin |
|---|---|
| Delivery | `exchange/pass-shelat-ch5-8` at **`15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`**, path `inbox/fills/io-sprg/` ("fill io-sprg: checkpoint 0 (M0 statements)") |
| Audited source | the worker's local `fill/io-sprg` at **`d10a560b34d58919bc1a5206ce66a444613f94c7`** (an empty marker commit on top of `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3`), delivered as `src/` (23 files), 15 format-patches and `bundle/io-sprg.bundle`; not pushed anywhere. `src/` equals the bundle head and base + patches byte for byte (maintainer check) |
| Base | `iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (#374, #378, the sampler contract, #380) |
| Records pin of the job's dispatch | `dbea2807532392781304e004715f3b0190025f5e` (`briefs/io-components/sprg/`) |
| Records pin of this pack | the commit on `cryptography/pass-shelat-ch2-4` that files `briefs/io-components/gates/52-sprg-statements/`; the dispatch prompt names it (a pack cannot name its own commit) |
| Host tools | exchange `bc9d982b83cb35ea351e2fb373752e8688945b1c`: `outbox/fills/codex-host-2026-11-15/host-addendum.md` (SHA-256 `02a6af16284cf5d6676caf3df58a31b3d640cc8e59febd51e0682d7ba455124c`), `lean-slot.sh` (`ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a`) |
| Lean / Mathlib | Lean 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

`source-head.json` lists every audited file with its SHA-256, lines, width and `sorry` count, the
15 source commits and the bundle hash.

## Source (local folder; nothing staged)

No PDF is in the repository, the exchange or this pack (pairing ruling Q12 (A); `sprg/rulings.md`
§ Sources). Seyoon names a local folder in the dispatch. Verify the file before reading it; read it
in place; never copy, commit or push a PDF, a page image or an excerpt.

| File | SHA-256 | Pages to read (PDF page *k* = article page 1:*k*) |
|---|---|---|
| `jls26.pdf` | `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` | §2 pp. 8–10 (Def 2.1, Remark 2.1, the multilinear-representation paragraph on p. 8, 𝒟_r(p) and Def 2.3); §3 pp. 10–11 (Defs 3.1–3.4, Remarks 3.1–3.2); Theorem 4.1 p. 11; overview pp. 11–15 (Equation (1), the boxed G⁽³⁾ and "degree d + 1" on p. 14); construction pp. 15–17 (parameters, IdSamp′, SdSamp′, 1SdSamp, Equation (2), G⁽¹⁾–G⁽⁴⁾, Equations (3)–(4)); Claim 4.1 p. 18; Proposition 4.1 pp. 18–19; Claim 4.2 pp. 19–21; Lemma 4.2 p. 19; Theorem 5.1 p. 21 |

A missing file or a wrong hash: read nothing from it, say so in the findings, and audit what does not
need it.

## Rulings in force

`briefs/io-components/sprg/rulings.md` at `dbea2807532392781304e004715f3b0190025f5e` takes
precedence over the r3 prompt, then design-r3, then design-r2, then design-r1. In short:
- **standing rule 15**: every primitive (`SPRG`, `BoolPRG`, `LPNFamily`) carries its honest
  algorithms' efficiency as structure fields in uniform form; the construction is a raw bundle;
  primitives are assembled from targets T1–T6, written not proved in Phase A;
- *Campaign opened*: non-uniform PPT throughout; degree d (Theorem 4.1, p. 17), not p. 14's d + 1;
- *sPRG design inputs*: rounding by the maintainer (design-r2 §3, C1–C14); exact finite laws;
- *Strategy and uniformity*: Phase A only; one algorithm for all κ, no per-κ constants; advice only
  in reductions and adversaries; p an input, every statement for every prime schedule;
- Q-S1 (A) LPN for the construction's own ℓ-indexed family (no literal Def 2.3 bridge); Q-S2 (A,
  refined) fixed schedule p(κ), p an input; Q-S4 (A) Def 3.3 only for degree-d public / degree-2
  private, one polynomial over both seed parts; Q-S5, Q-S8 (A);
- Q-S9 (A) the shared `Complexity.NUPPT.RealizesOn`; Q-S10, Q-S11, Q-S12 (A); Q-E1 (A) the shared
  sampler contract `CoinSampling/Contract.lean`;
- subexponential security only through `Foundations/Subexponential` (`SubexpSmall`,
  `SubexpHard`).

Chat rulings the worker records only in its payload (intake F10; `evidence/route-requests/`,
`evidence/scope-request/`): **SP-W1 δ ∈ ℚ** (Seyoon: "Use rational δ throughout, coercing it to real
values for analysis"); SP-W2 (two hybrid identities as acceptance equalities) and SP-W3
(`HasPolyStretch` requires κ ≤ seedBits eventually), both under "use your best judgment"; the
AGENTS.md override for slot-wrapped Lean. Treat them as rulings pending Seyoon's confirmation (intake
Q-G52-2); audit them like any other statement.

## Scope

**In scope:** every statement and definition of the 22 new files and the `TCSlib.lean` import line;
the REPORT's fidelity, rule-15 and non-vacuity tables and its Phase B target list.

**Out of scope:** proofs. The 146 `sorry`s are expected; grade a `sorry` only if it sits in a
definition (none found) or makes a statement unprovable. Phase B (machines, RAM programs, samplers,
proofs of T1–T6). The io-phfe job and Gate 51, except where the two jobs' interfaces must agree
(intake F12; dup-sweep S6).

## Questions for the audit, in the binding order

`SS/` is `TCSlib/Cryptography/Obfuscation/StructuredSeed/`. Line numbers are at `d10a560b`.

### A. Fidelity to [JLS26] Definition 3.3 and Theorem 4.1 (first)

1. **Def 3.3** (p. 10) under Q-S4. `SPRG.Raw.HasComplexity` (`SS/Defs.lean:298`), `pubDegree`,
   `privDegree` (`SS/Degree.lean:45`, `:56`; weighted total degrees), `HasComplexityEff`
   (`SS/Defs.lean:352`) with `PolyTerms` (`SS/PolyTerms.lean`). Is the composite form (one
   polynomial over `Fin pubLen ⊕ Fin privLen`, public degree ≤ d, private ≤ 2, equal to Eval on
   every `SdSamp(I)` output) equivalent to "(deg d, deg 2): Process_I of degree d, Q_I of degree 1
   in P̄ and d′ = 2 in S"? Is "for every index" (not only the support) acceptable? Does
   `HasComplexityEff` capture "Q_I efficiently generated from I" (one map before κ, p on the
   input, term lists denoting Q_I)? Is the replacement of "p an efficiently computable function of
   λ" by "every schedule, p public" (Dv9, Q-S2) disclosed where it applies?
2. **Defs 3.1–3.2** (p. 10). `SPRG.Raw` (`SS/Defs.lean:97`), `idSamp`/`sdSamp` (`:179`, `:188`),
   `challengeStr` (`:218`), `game` (`:234`), `adv`, `Secure`, `SubexpSecure` (`:251–270`),
   `seedBits`, `HasPolyStretch` (`:274–292`). The single index κ in place of (λ, n) with
   "n = n(λ) ≥ λ" (C1/Dv1); seeds as `Fin`-indexed ℤ_p vectors (Dv2, Dv15); p in the challenge
   (Dv9); `HasPolyStretch` as polynomial expansion in seed bits, with SP-W3's κ ≤ seedBits. Does
   this deliver what Theorem 5.1 consumes ("structured-seed PRG with stretch 1 + τ and complexity
   (deg d, deg 2) over ℤ_p", p. 21)?
3. **Theorem 4.1** (p. 11). On the raw bundle (`SS/Security.lean:102–193`): `jls_secure`,
   `jls_subexpSmall` (exponent `min(E·cL, min(E·D·cG, 1))/2`), `jls_subexpSecure`, `theorem41`,
   `theorem41_subexp`, `exists_sprg_raw(_subexp)`; on the primitive (`SS/Targets.lean:319–357`):
   `theorem41_of_targets`, `exists_sprg_of_targets(_subexp)`. Check each premise against the
   theorem's ("constant locality Boolean PRG with stretch τ > 1 and multilinear degree d over ℤ";
   "δ-LPN_F holds"; "if both assumptions are subexponentially secure"): G's security in its seed
   length, LPN for the own family in its dimension (Q-S1, Remark 2.1), realisability as the Phase B
   hypothesis (Dv14), `E ≥ E0` for the stretch only. Check the conclusion: (deg d, deg 2) over
   ℤ_{p(κ)}, polynomial stretch, security; the subexponential exponent fixed before the adversary.
   **SP-W1:** δ ∈ ℚ (`SS/Params.lean:53`) restricts "δ ∈ (0, 1) arbitrary". Is the restriction
   necessary for rule 15 (T5/T6 must compute ⌊ℓ^{δ/2}⌋ uniformly) and harmless (δ-LPN implies
   δ′-LPN for δ′ < δ by adding exact 𝒟 noise)? Should the docstrings say so (intake F10)?
4. **Degree d, not d + 1** (pp. 14, 16–17; campaign-open row). `G1`–`G4`, `G4_degrees`
   (`SS/Polys.lean:229–345`), `eval'` (`SS/Samplers.lean:313`): public degree ≤ d through the
   padded half-split of each monomial's support; flag·S precomputed (Equation (4)). Is the bound
   true (support of a multilinear degree-≤ d monomial ≤ d ≤ 2⌈d/2⌉), and is the p. 14 discrepancy
   noted in one docstring sentence?
5. **The definitions Theorem 4.1 rests on.** Def 2.3 and 𝒟_r(p) (pp. 9–10): `lpnNoise`,
   `lpnNoise_law`, `LPNFamily.Raw`, `toLWE`, `adv`, `Assumption` (`SS/LPN.lean:49–184`) and
   `Params.lpnFamily_raw` (`SS/Params.lean:339`): own ℓ-indexed family (Q-S1), samples L^D,
   modulus `(π (κOf L)).p` (η_p = 1/E), rate 1/W(L) ≥ L^{−δ} (noisier; Dv3), transposed
   orientation. Def 3.4 (p. 11): `BoolPRG`, `game`, `Secure`, `HasStretch`, `MultilinearRep`,
   `HasLocality` (`SS/BoolPRG.lean:50–239`; Dv4, Dv5). Def 2.1 / Remark 2.1: negligible and
   subexponential advantage against NUPPT, each assumption in its own parameter (Dv13).

### B. Definitions carry efficiency (rule 15; second)

1. `SPRG` (`SS/Defs.lean:397–404`), `BoolPRG` (`SS/BoolPRG.lean:94–101`), `LPNFamily`
   (`SS/LPN.lean:400–406`): every honest algorithm's efficiency is a field, uniform form only
   (`PolyTimeComputable` with the map before κ and the public parameter; samplers through the shared
   `SamplesEfficiently` with the parameter word on the input); no bare `∃ A : NUPPT, A.Computes f`;
   no per-κ constant; nothing computes p.
2. **The Gate 51 F01 class.** Is there any unbounded state, unbounded input encoding or per-κ escape?
   The intake found none (intake F09): no stateful interface; draw encodings (`encIdDraw`,
   `encSdDraw`, `encDraw`) carry no length field and are bounded only through `DrawSamplable`
   (`CoinSampling/Efficiency.lean:93`: `raw` polynomial-time, exact on success, failure ≤ 2^{−κ}).
   Confirm or refute that reading; if refuted, give the repair (explicit length fields).
3. Do the encodings make the fields and targets satisfiable and meaningful? Injectivity fields
   (`encIdx_injective`, `encIdDraw_injective`, `encSdDraw_injective`) and their sorried proofs
   (`SS/Encoding.lean:464–518`, `SS/LPN.lean:358–391`); the parameter words `idWord`, `sdWord`,
   `sampleWord` (prime first, unary κ or L); no `Fintype.equivFin` or chosen enumeration
   (C13).
4. No value of `SPRG` or `LPNFamily` outside the assembly (`SS/Targets.lean:279`, `:301`); the
   `toRaw` readers by `rfl`; T1 → `eval_eff`, T3 + T5 → the sampler fields on one draw each, T6 →
   `sample_eff`; `BoolPRG` is an input, never constructed.
5. Raw bundles carry correctness, stretch and security; no target is a hypothesis of a raw theorem.
6. T1–T6 (`SS/Targets.lean:72–223`): named `Prop`s with `_iff` readers and "Phase B obligation; not
   proved in this development"; each map before κ, `pp`, the schedule and the advice; T6 one `U, c,
   f` before every dimension and schedule (`P := fun _ => PrimeSchedule`). **Are they plausibly true
   for every `P`?** `exists_sprg_of_targets` assumes `∀ P : Params, P.Targets` (a false target makes
   the primitive headlines vacuous; intake F15): T2 needs R's term lists (R is unique and computable
   by interpolation from `eval_eff`; `MultilinearRep.TermsEfficient` is unused); T5 needs a product
   `UniformSampler` (Phase B) and ⌊ℓ^{δ/2}⌋ for rational δ.
7. Reductions: every realiser hypothesis uses the shared `RealizesOn`; `realizable_of_targets`
   (`SS/Targets.lean:232`) is a pure application of `exists_realizesOn_of_preTarget` with
   `κOf`/`κOfN`, `.var` and the advice bounds; advice only in reductions.

### C. The remaining statements

1. **Parameters and rounding** (p. 15; design-r2 §3): `Params` and `D, ℓ, n, m, noiseWidth, W, t,
   rc, cap, B, Γ, kappaOf, kappaOfN, pubLen, privLen, SVar, Priv, Pub` (`SS/Params.lean:50–271`);
   side conditions `Γ_le_B` (λ > log n), `le_log_n`, `le_n` (`:375–388`); `W_le_ell_add_one`
   (`SS/Encoding.lean:425`). Are ℓ, B, c, √c, Γ rounded as ruled, in the safe direction, and are the
   side conditions true eventually?
2. **The construction** (pp. 15–17): `IdDraw`, `Draw`, encodings (`SS/Encoding.lean:135–403`);
   `noiseValue`, `errSet`, `badSet`, `oneFlag`, `corr`, `lpnVector`, `oneSd`, `firstGood`,
   `packSeed`, `sdCore`, `idCore`, `idSamp'`, `sdSampFull`, `sdSamp'`, `eval'`, `challengeStr`,
   `jlsSPRG_raw` (`SS/Samplers.lean:45–437`); `Buckets` (`indexMap` with `Option`, `none` when
   overfull or at κ = 0), `SparseFactor` (deterministic, row-major). Same σ and A for all κ runs,
   fresh s, e per run; S⁽ᵏ⁾ stored unscaled for every k with flag·S separately; err = no success.
3. **Claim 4.1** (p. 18): `E0`, `seedBitsAt_le`, `jls_seedBits_le`, `jls_hasPolyStretch`
   (`SS/Stretch.lean:51–124`). Is `E ≥ ⌊max(10/δ, 5/(τ−1))⌋ + 1` sufficient (Eδ/2 > 5 and
   E(τ − 1) > 5 with m ≤ poly(n))?
4. **Claim 4.2** (pp. 19–21): `Cond1–3`, `jointLaw`, `errProb`, `badSet_expect_le`,
   `cond1_prob_le`, `errProb_le_decomposition`, `claim42` (κ₀ before every pp) (`SS/Claim42.lean`);
   the bucket tails and `binomial_bound` (`SS/Claim42/Load.lean`). The paper treats Cond1⁽ᵏ⁾ as
   independent across k; they are independent given the generator index only. Are the Lean
   statements true as written?
5. **Proposition 4.1 and Lemma 4.2** (pp. 18–19): `HybridStage`, `publicSeed`, `chainPublic`,
   `chainGame`, `hyb`, `hyb_real_eq_raw`, `hyb_random_eq_raw`, `hyb_prg_accept_eq_chain_zero`,
   `hyb_uniform_accept_eq_chain_zero` (SP-W2), `hyb_real_prg_le`, `hyb_uniform_random_le`
   (`SS/Hybrids.lean`); `lemma42`, `prop41` (`SS/Security.lean:62`, `:84`); the reductions
   (`SS/Reductions/LPN.lean`, `SS/Reductions/PRG.lean`): `LPNChal`/`lpnEnc` = the LWE challenge
   unchanged, `LPNAdvice` (hop in `Fin (κOf L + 1)`), `encLPNAdvice` (prime first) and its bound,
   `lpnPre` (guarded, off-image `[]`), `lpnRed`, `lpn_hop`; the PRG analogues and `prg_hop`. Is the
   2κ·LPN + PRG + 2·errProb inequality true at every κ (κ = 0 included) for every realiser, with
   the advice chosen before the realisers? Are the program equalities `hyb_real_eq_raw`,
   `hyb_random_eq_raw` true as equalities of `ProbComp` programs (cf. SP-W2)?

### D. Well-formedness and vacuity

1. Vacuity: advice types inhabited at every parameter; `PrimeSchedule` inhabited; realisability
   (`LPNRealizable`, `PRGRealizable`, `Realizable`) satisfiable in Phase B (advice of polynomial
   encoded length; pre-processing computable from the encoded inputs); SP-W3 closes the
   constant-length existence; is `BoolPRG` inhabited (intake F15)?
2. Any statement false as written (e.g. an encoding injectivity or length bound, a degree bound, a
   reader), provable for a trivial reason, or too weak for its consumer.
3. `sorryAx` in definitions through named field theorems (intake F14): allowed at M0; is any such
   field theorem false (which would make a definition rest on a false proof)?

### E. Readers and Rule 10 (statement level)

Every public definition has its readers (`_eq`, `_iff`, case and projection lemmas, `toRaw`); no
`@[simp]`, no global attribute; statements read foreign TCSlib definitions only through published
lemmas. The worker ran the coe-A/coe-B/strict seals and paired controls at M0
(`evidence/rule10/m0_final/`, `complete-runtime-check.json`); spot-check one owner's seal result
against its log, and grade the reliance of `PrimeSchedule` (an `abbrev`) and `SPRG.Raw.Seed` on
being notation.

### F. Duplication

`dup-sweep.md` (S1–S11). Grade S1–S3, confirm or refute the rest, and look for what the sweep
missed, with `exact?`/`apply?` probes under your one slot where useful (dup-sweep §3).

### G. Attribution and docstrings (`policy.md`)

Every source-derived declaration's docstring states the claim in words, then a tag with a precise
location, then any deviation and its reason. Check the tags against the PDF (no fabricated page,
equation or item number). Module docstrings and `## References`; the facade `## Contents`
placeholders (intake F07); campaign labels in Lean text (`SP-W*`, "pre-M0", "M0"; intake F02); the
prompt-mandated `Dv` tags (intake F13).

### H. The intake findings

Grade `intake-r1.md`'s SPRG-C0-F01 to F17 in a separate table: agree, regrade, or reject, with
reasons.

## Lean on this host (one slot; wait for a free one)

At most 3 Lean processes run on the Mac across all jobs. The io-phfe and io-sprg jobs hold one slot
each, and Gate 51 holds the third while it runs. **This gate holds at most one**, through
`lean-slot.sh` with `LEAN_SLOT_TAG=g52-sprg`, one module or probe per call, in the foreground; the
wrapper blocks until a slot is free, so while Gate 51 is running this gate waits. Never bypass the
wrapper to start Lean early, and never run Lean while Gate 51 and both jobs hold all three slots.
No `lake build`, ever; no `lake exe cache get` unless the dispatch's option B is chosen. Never touch
another job's or gate's worktree, olean tree, slot or process; kill only processes you started, by
PID. Run Python as `python3 -I`.

Suggested checks (the dispatch gives the commands):
1. Re-elaborate the 127-module closure in `evidence/logs/order.txt` order at the audited source,
   into your own olean tree: every module rc 0, 0 errors in both forms.
2. Probes in a scratch file outside `TCSlib/` (never committed): `#print axioms` of the headlines
   (`sorryAx` expected); `#check` of the statements you grade; `exact?`/`apply?` for dup-sweep §3.
3. Record every command, its rc and its slot lines.

## Evidence in the delivery

Read through `git show 15946b52d0615fda8afad9ed3c57cfaf5beaaa8d:inbox/fills/io-sprg/<path>` (the
payload is 1.19 GB; do not check it all out). Most useful: `REPORT.md`; `patches/`; `bundle/`;
`evidence/statements/` (`decls2.tsv`, `fidelity-current.tsv`, `proof-obligations-current.tsv`);
`evidence/checks/m0-sp-w3/`; `evidence/build/summary.txt`; `evidence/logs/order.txt`;
`evidence/host/`; `evidence/boundary/`; `evidence/route-requests/`; `evidence/rule10/m0_final/*.json`.
Skip `evidence/rule10/m0/`, `evidence/probes/io_sprg_m0/` (a superseded pass), the seal sources
and the census logs.

## Severities (`workflow.md` §3)

- **blocker:** a later phase (the proofs, Phase B, the consumer) would build on a wrong statement:
  a false, vacuous or unusable statement or definition; a definition too weak for its consumer
  (for example an "efficient" interface that admits non-PPT algorithms); a missing or wrong
  efficiency field; a scope violation.
- **major:** fixable but materially misleading: a mis-stated source correspondence, a fabricated tag
  or locator; an undisclosed or unaccepted restatement or re-derivation of a public lemma; a
  definition that depends on an admitted theorem beyond a proof field; necessary evidence that does
  not bind to the audited commit; a payload or process defect that misleads.
- **minor:** documentation or API defects: an inaccurate docstring, deviation note, disclosure,
  sketch or citation; a missing reader.
- **note:** anything else.

## Findings delivery (as Gate 51)

Return **`findings-r1.md`** as Markdown in the chat. If you have evidence files (probe sources and
logs, slot lines), return a ZIP with `findings-r1.md` at its root. Write nothing to the exchange or
the records branch, and push nothing: the maintainer files the findings verbatim, with their SHA-256,
at `briefs/io-components/gates/52-sprg-statements/findings-r1.md`, and Seyoon relays the statement
repairs into the worker's chat (Q-S8).

| # | Severity | File · declaration | Claim | Evidence (source page / Lean line / probe) | Proposed fix |
|---|---|---|---|---|---|

Number findings **G52-01, G52-02, …**, in the order A–G. Put the grading of SPRG-C0-F01..F17 in a
separate table. Report the audited commits, the PDF hash you verified, the Lean checks run, the
counts by severity, and a verdict: **CLEAR** (zero blockers and zero majors) or **HOLD**. For each
blocker or major that changes a statement, give the replacement statement text, so that it can be
relayed as one `statements r1` commit.
