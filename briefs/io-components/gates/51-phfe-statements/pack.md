# Gate 51 · io-phfe statements gate (checkpoint 0) · round 1

The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). It runs
in a local checkout on Seyoon's Mac, because it needs the five source PDFs from a local folder and
one Lean slot.

This is the **statements gate** of the io-phfe job (design-r3 §6; prompt §6 "Two separate audits
gate the job"). It audits the job's checkpoint 0, the statements commit: degree-2 public-key PHFE
from DLIN [Wee20], to the notion of [GJLS21, Def. 4.3] as JLS26 Thm 5.1 consumes it. The proofs gate
on the final delivery is separate.

## Pins

All hashes are full; take them from this file, never retype them.

| Item | Pin |
|---|---|
| Delivery | `exchange/pass-shelat-ch5-8` at **`1e77173a7032b57aa22260787711c6c7a1b7596e`**, path `inbox/fills/io-phfe/` ("fill io-phfe: checkpoint 0 (statements)") |
| Audited source | the worker's local `fill/io-phfe` at **`70b85f9ba83f27393d98fa5bf88505aea3d22a8d`**, delivered as `src/` (76 files) and 25 format-patches; not pushed anywhere. `src/` equals base + patches byte for byte (maintainer check) |
| Base | `iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (#374, #378, the sampler contract, #380) |
| Records pin of the job's dispatch | `dbea2807532392781304e004715f3b0190025f5e` (`briefs/io-components/phfe/`) |
| Records pin of this pack | the commit on `cryptography/pass-shelat-ch2-4` that files `briefs/io-components/gates/51-phfe-statements/`; the dispatch prompt names it (a pack cannot name its own commit) |
| Host tools | exchange `bc9d982b83cb35ea351e2fb373752e8688945b1c`: `outbox/fills/codex-host-2026-11-15/host-addendum.md` (SHA-256 `02a6af16284cf5d6676caf3df58a31b3d640cc8e59febd51e0682d7ba455124c`), `lean-slot.sh` (`ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a`) |
| Lean / Mathlib | Lean 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

`source-head.json` lists every audited file with its SHA-256, lines, width and `sorry` count, and the
25 source commits.

## Sources (local folder; nothing staged)

No PDF is in the repository, the exchange or this pack (pairing ruling Q12 (A), `rulings.md`).
Seyoon names a local folder in the dispatch. Verify each file before reading it; read in place;
never copy, commit or push a PDF, a page image or an excerpt.

| File | SHA-256 | Pages to read |
|---|---|---|
| `gjls21.pdf` | `481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed` | Defs 4.1–4.3, Remarks 4.3–4.6 (printed pp. 19–20); Def 4.6 (p. 22); §9 class (pp. 57–58); Thm 9.2 proof, Hybrid 1 (p. 61); Def 3.3 (p. 18); Thms 10.3–10.4 (pp. 63–64). Printed page = PDF page − 4 |
| `wee20.pdf` | `d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a` | §2.1 (p. 4), §2.2 (p. 5), §3.1–3.3 (pp. 6–8), §4.1 Lemma 1 (p. 8), §4.2 (pp. 9–10), App. B Thm 1, Lemmas 2–5 (pp. 12–14). Printed = PDF |
| `jls26.pdf` | `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` | §1.1 (PDF p. 3), §1.4 (PDF pp. 7–8), Thm 5.1 (PDF p. 21) |
| `agw20.pdf` | `b74c2ac906cf3f40eb5882abb3921433beebdb9fb020ba09ce8a10035b55d11f` | §4.1–4.2, Lemma 2 (pp. 11–12); App. A (28)–(32) (pp. 37–38); App. B (pp. 38–39). Printed = PDF |
| `iw14.pdf` | `ef6c7c6a0103dfea1d8d9d369e3a7de3a0902fa6138a6bedc4c4df4996e65e77` | Def 1 (pp. 6–7), Thm 3 (p. 8), §4.2 (pp. 9–11). Printed = PDF |

A missing file or a wrong hash: read nothing from that file, say so in the findings, and audit the
rest.

## Rulings in force

`briefs/io-components/phfe/rulings.md` at `dbea2807532392781304e004715f3b0190025f5e` takes
precedence over the r3 prompt, then design-r3, then design-r2. In short:
- target [GJLS21, Def 4.3], ε = 1, many-key, for the §9 class, with Defs 4.1, 4.2, 4.6;
- Q1 (A): the simulator's ω carries µ ∈ ℤ_p (disclosed deviation; Thm 9.2 proof, Hybrid 1);
- Q2 (A): partial garbling as an interface plus the proved layered instance, exact privacy;
- Q3: Wee20's semi-adaptive notion for both layers; Def 4.3 derived by `simAdv_eq_saSimAdv`;
- Q4 (A): one job, PARTIAL final allowed; Q5 (A): the shared `Complexity.NUPPT.RealizesOn`;
- Q-E1 (A): the shared sampler contract `CoinSampling/Contract.lean`, must-reuse;
- Q-S2: a fixed prime schedule `hp`; honest algorithms read the modulus from pp;
- *Strategy and uniformity*: Phase A writes efficiency as targets; uniform honest algorithms;
  advice only in reductions and adversaries;
- **standing rule 15**: every interface carries its efficiency as fields; constructions are raw
  bundles; primitives are assembled from targets;
- Q-S8: Codex continues after checkpoint 0; gate findings that change statements are relayed into
  the worker's chat and applied as one disclosed `statements r<k>` commit.

Chat rulings the worker records only in its payload (`evidence/logs/rulings.json`; intake F12): the
Lean route through the slot wrapper; **g ∈ G\* in pp with the extra field `pubGen_eff` and its
target**; best judgment while Seyoon was away. Treat them as rulings pending Seyoon's confirmation
(intake Q-G51-3); audit `pubGen_eff` like any other field.

## Scope

**In scope:** every statement and definition of the 74 new modules and the facade lines of
`Pairing.lean` and `AdvancedEncryption.lean`, and the REPORT's fidelity and rule-15 tables.

**Out of scope:** proofs. The 144 `sorry`s are expected; grade a `sorry` only if it sits in a
definition (none found) or makes a statement unprovable. Phase B (machines, RAM programs, samplers,
proofs of the targets). The parallel io-sprg job, except where its interfaces must agree with this
job's (dup-sweep S6).

## Questions for the audit, in the binding order (design-r3 §6)

`FE/` is `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/`. Line numbers are at
`70b85f9b`.

### A. Fidelity to [GJLS21] Defs 4.1–4.3, 4.6 and the §9 class (first)

1. **Def 4.1.** `FEScheme.Raw` (`FE/Defs/Raw.lean:74`), `PublicParams` and `publicParamsGen`
   (`Pairing/MatrixDH/Parameters.lean:56`, `:118`): PPGen, Setup, public-key Enc returning the
   ciphertext with x separate, KeyGen, deterministic Dec with ⊥. Is anything missing or
   strengthened in a way the consumer cannot meet?
2. **Def 4.2.** `Correct`, `CorrectExcept` (`FE/Defs/Correctness.lean:122`, `:134`): every wire input,
   every honest draw; G_T output via the injective `embed`.
3. **Def 4.3**, ε = 1, Remarks 4.3, 4.5, 4.6. `simGame`, `realView`, `idealView`
   (`FE/Simulation/Games.lean:100–145`), `Commitment`, `TwoStage`, `Omega`, `Simulator.Raw`
   (`FE/Defs/Simulator.lean:52`, `:87`), `SimSecureWith`, `SimSecure`, `SubexpSimSecure`
   (`FE/Simulation/Security.lean:48–77`). Check the order (A₁ before pp), A₂'s view, the ideal
   experiment's inputs (ω = x*, functions, values; Setup~ independent of the challenge), one
   simulator before all A and q, the many-key quantifier, the subexponential form (one exponent
   before A and q). Check the Q1 (A) deviation against Thm 9.2's Hybrid 1 (p. 61). Check the
   "∃ negl … for all polynomials prmtr" quantifier reading (intake F03).
4. **Def 4.6.** `LinearEfficient` (`FE/Wee20/Targets/LinearEfficiency.lean:84`): one `FinTM`, time
   (ℓ+n)·q(κ) for 0 < ℓ+n, all typed keys and draws. Is it at least as strong as the circuit-size
   bound (TM-to-circuit overhead), and is the guard acceptable (intake F19)? Is the target
   plausibly **true** for `PHFE.encCore` (a false target makes every primitive headline vacuous)?
5. **§9 class.** `phfeClass`, `PolyTensor`, `polyTensorEval`, `phfeEval_sum`, `pad_one`
   (`FE/Classes.lean:62–315`, `:560`): Σ_{j,k} f_{j,k}(x) y_j y_k, f_{j,k} of constant degree, over
   the drawn order, output in G_T; polynomial description length for constant d; the wire decoding
   (residues mod p; aliases kept).
6. **The derivation.** `TwoStage.toSA`, `SASimulator.Raw.toSim`, `expect_simGame_eq_saGame`,
   `simAdv_eq_saSimAdv` (`FE/SemiAdaptive/FromTwoStage.lean:55`, `:220`, `:261`, `:271`): is the
   identity true as stated (coin split, q + 1 calls, oldest-first query log, ideal values)?
7. **Headlines.** `wee20PHFE_gjls21`, `wee20PHFE_simSecure` and the SA/subexp forms
   (`FE/Wee20/PHFE/Headlines.lean`); the raw `wee20PHFE_simAdv_le`, `wee20PHFE_saSimAdv_le` and
   their DLIN-composed forms (`FE/Wee20/PHFE/Security.lean`). Do they deliver what GJLS21 Thms
   10.3/10.4 and JLS26 Thm 5.1 consume?

### B. Definitions carry efficiency (rule 15; second)

1. `FEScheme` (`FE/Defs/Efficient.lean:46`), `Simulator` (`FE/Defs/Simulator.lean:230`),
   `SASimulator` (`FE/SemiAdaptive/Simulator.lean:209`), `PartialGarbling`
   (`FE/PartialGarbling/Defs.lean:450`): every honest algorithm's efficiency is a field, in uniform
   form only (`SamplesEfficiently`; `∃ a, PolyTimeComputable a ∧ ∀ κ …` with the witness before κ
   and the group); no bare `∃ A : NUPPT, A.Computes f`; no per-κ constant; the modulus read from the
   input.
2. **Intake F01.** The simulators' state type and encoding are unbounded
   (`FE/Defs/Simulator.lean:89–93`, `FE/SemiAdaptive/Simulator.lean:50–54`), so per-call
   polynomial time in the input length does not bound the total time over q(κ) stateful calls.
   Confirm or refute, grade it, and give the repair (a fixed-width `stLen` or a length-bound field).
   Look for the same gap anywhere else (e.g. variable-length draw or output encodings).
3. Do the fields' encodings make the targets satisfiable? A non-injective or lossy parameter word
   (e.g. `encMSK`, the draw encodings, `Omega.encode`) could make a target false and the primitive
   headlines vacuous; a too-rich one could hide work in the encoding. Check `wee20PHFE_raw`'s
   concrete encodings.
4. No value of `FEScheme`, `Simulator`, `SASimulator` or `PartialGarbling` outside
   `FE/Wee20/Targets/Assembly.lean`; the assembly attaches target proofs only, and `_toRaw` readers
   show the laws are the raw bundle's.
5. The raw bundles carry correctness and security; no target is a hypothesis of a raw theorem.
6. The targets (`SchemeTargets`, `SimTargets`, `PGTargets`, `LinearEfficient`, `MddhPreTargets`,
   `Targets`) are named `Prop`s with `_iff` readers and the "Phase B obligation" docstring, and
   together inhabit every primitive built. `MddhPreTargets` has an unused `_D` binder and a witness
   chosen after (p, d, ℓ) (intake F05): acceptable for an L1 reduction?
7. `pubGen_eff`: is it the right home for g ← G\*'s efficiency (it depends on G only)?
8. Reductions: every realiser hypothesis uses the shared `RealizesOn`; `mddhRealizable_of_preTarget`
   is a pure application of `exists_realizesOn_of_preTarget_id`.

### C. Fidelity to [Wee20], [AGW20], [IW14]

1. Wee20 §2.2: `saGame`, `saImpl`, the real/ideal handlers, `SAAdv`, `toSAAdv`, `SASimSecure`
   (`FE/SemiAdaptive/*`). Is threading state from Enc\* to KeyGen\* justified by §3.2?
2. The quadratic scheme and simulator (§3.1–3.2), Games 0–4 (§3.3), Π (§4.2) and its simulator,
   Theorem 1 and Lemmas 2–5 (App. B): shapes, the per-key group M (R2), the four MDDH hops and their
   dimensions ((1,3), (ℓ, mBound·q), (1, n), (1, n)), the slack (`linearSlack` charged once; no
   garbling term), Lemma 3's change of variables replacing random guessing.
3. Misprints W1–W5 and readings R1–R4 (REPORT.md:243–255), and the Π rank estimate (REPORT.md:
   217–228; intake F04): verify each against the page.
4. AGW20 Lemma 2 and App. A (28)–(32); IW14 Def 1, Thm 3, §4.2: `PartialGarbling.Raw`
   (`FE/PartialGarbling/Defs.lean:181`), `pgbCore`, `pgbStarCore`, `rec_spec`, `privacy`; the
   layered instance (`FE/PartialGarbling/Layered.lean`): MIdx/TIdx, L₁/L₀, m and t depending on
   (ℓ, d, n′) only, `mBound`. Are `rec_spec` and `privacy` true for the instance, d = 0 included?
5. DLIN (JLS26 §1.1; GJLS21 Def 3.3) and MDDH (Wee20 §2.1): `Pairing/Linear.lean`,
   `Pairing/MatrixDH/*`; `dlinToMddh`'s loss d·DLINAdv + 4d/p and the canonical-vs-matrix
   discrepancy.

### D. Well-formedness and vacuity

1. Vacuity rule: core inequalities for every typed adversary; `Wee20RealizableSA` and
   `Wee20Realizable43` (`FE/Wee20/PHFE/Security.lean:126`, `:173`) quantify only over `toSAAdv A q`
   and `A.toSA q`. Are they satisfiable in Phase B (advice families of polynomial encoded length;
   the derived adversaries computable)?
2. R-DLOG: no reduction, handler, simulator or honest algorithm inverts exponentiation; the one
   `pow_val_bijective` use (`FE/Wee20/PHFE/Embedding.lean:42`) is proof-only.
3. `hp`, `hpb`, `PGSound` (intake F13): consistent, not contradictory, discharged where claimed.
4. Any statement false as written, or provable for a trivial reason, or too weak for its consumer.

### E. Readers and Rule 10 (statement level)

Every public definition has its readers (`_eq`, `_iff`, case lemmas, `toRaw_*`); no `@[simp]`, no
global attribute; statements read foreign TCSlib definitions only through published lemmas. The
full Rule 10 suite is a final obligation (`evidence/rule10-m0-final/STATUS.md`), not this gate's.

### F. Duplication

`dup-sweep.md` (S1–S11). Grade S1–S3, confirm or refute the rest, and look for what the sweep
missed, with `exact?`/`apply?` probes under your one slot where useful (dup-sweep §3).

### G. Attribution and docstrings (`policy.md`)

Every source-derived declaration's docstring states the claim in words, then a tag with a precise
location, then any deviation. Check the tags against the PDFs (no fabricated page or theorem
number; Wee20's main scheme has no numbered theorem). Module docstrings and `## References`;
intake F09 (the Pairing facade cites AGW20 and IW14). No campaign labels in Lean text.

### H. The intake findings

Grade `intake-r1.md`'s PHFE-C0-F01 to F19 in a separate table: agree, regrade, or reject, with
reasons.

## Lean on this host (one slot)

At most 3 Lean processes run on the Mac across all jobs; the io-phfe and io-sprg jobs hold one each.
**This gate holds at most one**, through `lean-slot.sh` with `LEAN_SLOT_TAG=g51-phfe`, one module or
probe per call, in the foreground. No `lake build`, ever; no `lake exe cache get` unless the
dispatch's option B is chosen. Never touch another job's worktree, olean tree, slot or process;
kill only processes you started, by PID. Run Python as `python3 -I`.

Suggested checks (the dispatch gives the commands):
1. Re-elaborate the 285-module closure in `evidence/logs/order.txt` order at the audited source,
   into your own olean tree: every module rc 0, 0 errors (the worker took about 13 minutes).
2. Probes in a scratch file outside `TCSlib/` (never committed): `#print axioms` of the headlines
   (sorryAx expected); `#check` of the statements you grade; `exact?`/`apply?` for dup-sweep §3.
3. Record every command, its rc and its slot lines.

## Evidence in the delivery

Read through `git show 1e77173a7032b57aa22260787711c6c7a1b7596e:inbox/fills/io-phfe/<path>`
(the payload is 812 MB; do not check it all out). Most useful: `REPORT.md`; `patches/`;
`evidence/statements/written-declarations.tsv`, `native-declarations.tsv`, `axioms.jsonl`,
`sorry-traces.jsonl`; `evidence/logs/m0-decls2-final.tsv`, `order.txt`, `slots-io-phfe.log`;
`evidence/build/summary.tsv`; `evidence/static-m0-final/`; `evidence/source-reviews/`. The
`evidence/rule10-m0-final/seals/` tree (742 MB) holds unexecuted inputs; skip it.

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

## Findings delivery (as Gate 46)

Return **`findings-r1.md`** as Markdown in the chat. If you have evidence files (probe sources and
logs, slot lines), return a ZIP with `findings-r1.md` at its root. Write nothing to the exchange or
the records branch, and push nothing: the maintainer files the findings verbatim, with their SHA-256,
at `briefs/io-components/gates/51-phfe-statements/findings-r1.md`, and Seyoon relays the statement
repairs into the worker's chat (Q-S8).

| # | Severity | File · declaration | Claim | Evidence (source page / Lean line / probe) | Proposed fix |
|---|---|---|---|---|---|

Number findings **G51-01, G51-02, …**, in the order A–G. Put the grading of PHFE-C0-F01..F19 in a
separate table. Report the audited commits, the PDF hashes you verified, the Lean checks run, the
counts by severity, and a verdict: **CLEAR** (zero blockers and zero majors) or **HOLD**. For each
blocker or major that changes a statement, give the replacement statement text, so that it can be
relayed as one `statements r1` commit.
