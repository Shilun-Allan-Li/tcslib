# Gate 51 — io-phfe statements, round 1

**Verdict: HOLD.** Two blockers, one major and nine minors. The 285-module replay passes; elaboration does not resolve the specification defects below. Proof admissions are expected at this gate.

`FE/` denotes `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/`. Lean locations refer to the delivered source, without audit modifications.

| Audited item | Commit |
|---|---|
| Gate pack and records read | `8ba55910eafa03c02c39943729c606bb457be60f` |
| Delivery | `1e77173a7032b57aa22260787711c6c7a1b7596e` |
| Worker source, identified by the verified manifest and patches | `70b85f9ba83f27393d98fa5bf88505aea3d22a8d` |
| Base of the detached audit checkout | `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` |
| Job dispatch records pin | `dbea2807532392781304e004715f3b0190025f5e` |

The pack's four checksums pass. All 103 selected payload checksums pass: REPORT, 76 source files and 26 patch-directory files. All 76 source-head hashes agree. Applying the 25 patches to the base reproduces all 76 delivered files byte for byte. The source overlay changes only the two permitted facades and adds 74 modules: 13,745 lines and 144 direct `sorry`s. The delivered Lean bytes were not modified; no commit, push or PR was made.

## Findings, in A–G order

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G51-01 | minor | `FE/Simulation/Security.lean:48` · `SimSecureWith`; REPORT fidelity tables | The parameter-family quantifier reading is undisclosed. | GJLS21 Def. 4.3, printed pp. 19–20, places the negligible bound before the parameter-family quantifier. Lean fixes the scheme's polynomial dimensions first. Perfect correctness handles Def. 4.2, but does not explain this security reading. | State explicitly that negligibility is familywise; do not claim a single bound uniform over all polynomial parameter families. Reconcile the Defs. 4.2/4.3 rows. |
| G51-02 | major | `FE/Wee20/Targets/LinearEfficiency.lean:84` · `LinearEfficient`; `PHFE/Headlines.lean:118` · `wee20PHFE_gjls21` | The claimed correspondence with Def. 4.6 lacks a circuit-size specification or a bound-preserving bridge. | GJLS21 Def. 4.6, printed p. 22, bounds Boolean-circuit size. The target bounds multi-tape TM time by `(ℓ+n)q(κ)`. The usual `O(T log T)` conversion leaves a dimension-dependent logarithm; it cannot be absorbed uniformly in κ over the target's unrestricted numeric dimensions. Familywise asymptotic absorption needs a different quantifier/threshold statement. | Use replacement R1 below. The actual construction may have linear-size circuits; this finding does not assert a circuit lower bound. |
| G51-03 | blocker | `FE/Defs/Simulator.lean:89–93,230–247`; `FE/SemiAdaptive/Simulator.lean:50–54,209–227`; `FE/Defs/Raw.lean:56–64` | Per-call efficiency does not ensure a PPT simulator: both state and permitted value encodings lack polynomial length bounds. | A polynomial-time transition can duplicate its state after every query, producing length `2^q`. Independently, `FnClass` admits an injective encoding of a Boolean value of length `2^κ+1`; supplying that word makes polynomial-in-input-time insufficient. The corresponding growth and padded-class lemmas elaborate without `sorryAx` in `G51Probe/Probe.lean`. | Add the two bounds in R2 to both efficient simulator interfaces, matching targets and assembly. This confirms F01 and extends its repair to leakage words. |
| G51-04 | blocker | `FE/Defs/Efficient.lean:48–51` · `FEScheme.pubGen_eff`; `FE/Wee20/Targets/Scheme.lean:58–61` | The generator-sampling target omits κ from the sampler's parameter word and imposes an unintended restriction on valid group generators. | Shared `DrawSamplable` indexes both `U.Ω` and `U.enc` by `y` alone. Here `y=d.val`, although the draw and its encoding depend on κ. The kernel-checked `pubGen_width_separation` proves that this field forces equal group widths whenever reachable descriptions coincide across parameters. `BilinearGen` imposes no such condition. Even singleton draws with changing output width give a contradiction. These probe lemmas use only standard axioms. | Include κ in the sampler parameter word, as specified in R3. Update the matching targets/readers; retain the shared contract. |
| G51-05 | minor | `FE/Wee20/Targets/MatrixDH.lean:44` · `MddhPreTargets` | The unused `_D` binder obscures the actual witness order. | The preprocessing witness follows the fixed schedule and dimension pair, and precedes κ, advice and challenge. Its specification does not use `_D`. This order is acceptable for L1 preprocessing. | Drop `_D`, update the reader/link, and describe the order explicitly. |
| G51-06 | minor | `REPORT.md:217–255` · rank correction and W/R table | The corrected Π rank estimate is missing from the misprint table. | Wee20 §4.2 p. 10 and App. B Thm. 1 p. 12 use `1/p`. For unconditioned uniform 3×3 matrices the delivered correction is correct; exact enumeration gives 344 singular matrices out of 512 at p=2, hence `43/64`. | Add W6 with both source locations and the unconditioned-draw correction. |
| G51-07 | minor | `Pairing/MatrixDH/SelfReduction.lean:11` · import dependency | A Pairing assumption module imports an IBE machine module for a general group-width lemma. | It reuses `BB1Machine.order_le_two_pow`; the dependency is disclosed at REPORT:414. Dup-sweep S1 is confirmed. | Retain reuse within this scope; keep the requested promotion to the Pairing owner API on the landing ledger. |
| G51-08 | minor | `Pairing/Exponents.lean:182,189` · `pow_val_add_GT`, `pow_val_neg_GT` | The disclosed source/target-group near-copies need an explicit promotion disposition. | Base `Pairing/Group.lean:254,260` supplies the source-group laws. The GT variants are disclosed at REPORT:410; searches found no existing closing GT lemma. Dup-sweep S2 is confirmed. | Record promotion to `Pairing/Group.lean`; proofs should consume the existing power/cardinality laws. |
| G51-09 | minor | `FE/Simulation/Games.lean`, `Defs/Simulator.lean`, `Wee20/WireDraws.lean`, `PHFE/Simulator.lean` · nested list encodings | The repeated list-encoding pattern is absent from the reuse disclosure. | The `foldr pairEncode []` pattern matches the existing `Encryption.PrivateKey.EnsembleSecurity.encodeList`. This is encoding duplication, not an undisclosed proved theorem. Dup-sweep S3 is confirmed. | Disclose the overlap and its ownership/import constraint, or reuse the existing encoding where suitable. |
| G51-10 | minor | `TCSlib/Cryptography/Pairing.lean:44–48` · references | The Pairing facade cites AGW20 and IW14 although its children do not use them. | Their actual consumers are under functional encryption. | Remove those two facade entries. |
| G51-11 | minor | `REPORT.md:3,25,601–603` · publication status | The delivered report retains prepublication/freeze-pending wording. | The delivery commit is already the checkpoint-0 publication. | Record the actual delivery commit and freeze start, distinguishing the earlier report snapshot. |
| G51-12 | minor | Payload · `evidence/rule10-m0-final/seals/` | The reported 812 MB delivery contains excessive unexecuted/generated material. | Intake F02 identifies the bulk; the directly read STATUS explicitly says the four seal variants were unexecuted. This is delivery hygiene, not evidence of a falsely claimed passing check. | Future checkpoints should carry generators/hashes and executed logs, retain final artifacts only, and compress large census files. Do not rewrite history. Regrade F02 from major to minor. |

## Replacement specifications

**R1 — G51-02.** Add a named `CircuitLinearEfficient G : Prop`, with its reader and Phase B obligation docstring, specifying:

> There exists one polynomial bound, chosen before all numeric dimensions, degree and security parameters, such that for every supported public parameter and honest public key, and positive total message dimension, there is a Boolean encryption circuit. With pp and pk hardwired, the circuit takes the public/private input bits and the complete encoded encryption draw, returns exactly the encoded `PHFE.encCore` ciphertext, and has at most `(ℓ+n)` times that polynomial in κ gates.

Require this target in `Targets` and use `CircuitLinearEfficient G` as the third conjunct of `wee20PHFE_gjls21`. The present uniform TM target can remain an additional obligation. An alternative repair is an explicit conversion theorem with exactly the source's size bound and quantifiers; merely citing polynomial dimensions does not supply that statement. The positive-size guard and all-typed-key strengthening are otherwise acceptable, and the encryption core's linear-size data layout is plausible.

**R2 — G51-03.** Add the following proof fields to **both** `Simulator` and `SASimulator`, in their existing context `{C : FnClass} (S : FEScheme.Raw C)`:

```lean
state_bounded : ∃ b : PolyExpr,
  ∀ κ (pp : PublicParams S.G κ) (st : St κ pp),
    (encSt κ pp st).length ≤ b.eval κ
value_bounded : ∃ b : PolyExpr,
  ∀ κ (pp : PublicParams S.G κ)
    (v : C.Out κ (S.cprm κ pp)),
    (C.encValue κ (S.cprm κ pp) v).length ≤ b.eval κ
```

Add the matching concrete propositions to `SimTargets`, its reader and pure assembly. These bounds deliberately strengthen the generic interface; the concrete matrix/vector states have fixed polynomial width, and the concrete scalar encoding is bounded by the group width plus one. Raw algorithms and game laws need not change. A more general reachable-state resource invariant is possible, but must bound the whole polynomial-query run, rather than iterate a polynomial bound on the previous state length.

**R3 — G51-04.** Replace the parameter map in `pubGen_eff` by:

```lean
(fun κ (d : GroupDescription G κ) => NUPPT.advInput κ d.val)
```

Leave its draw encoding, output encoding and core unchanged, and make the identical replacement in `SchemeTargets.pubGen_eff` and its reader. Apply the same explicit κ-prefix to other sampler parameter maps unless their existing word is proved to determine κ and the required layout. In general, a current map `y` becomes `fun κ π => NUPPT.advInput κ (y κ π)` at the existing `SamplesEfficiently` application. Mirror changes through all targets and assembly; do not introduce a local sampler contract or compute a prime schedule.

## A–H audit coverage

| Question | Result |
|---|---|
| A | GJLS21 Defs. 4.1–4.3 and §9 were checked directly. Commitment precedes pp; ideal setup is independent; state, ordered keys, public input and ciphertext reach A₂ correctly. The scalar leakage deviation is ruled and matches Thm. 9.2 Hybrid 1. The class, padding and total modular decoding cover the required polynomial functionality. The q+1 coin-split/log-order derivation has the right statement. Def. 4.6 remains subject to G51-02; simulator efficiency to G51-03/04. |
| B | Uniform efficiency fields, raw/primitive separation, named targets and pure assembly are present. The L1 link applies the shared realisation theorem. Concrete secret/draw encodings retain their required data. G51-03/04 prevent certification of the efficiency contracts. The extra generator-sampling field is needed; its fact depends on G and can be shared. |
| C | Checked Wee20's two layers, per-key group matrix, Games 0–4 and Π's App. B sequence against the PDFs. The four MDDH dimensions are `(1,3)`, `(ℓ,mBound·q)`, `(1,n)`, `(1,n)`; one Π rank loss and no garbling loss are charged. W1–W5 and R1–R4 are supported. AGW/IW dimensions and exact privacy, including degree zero, agree with the layered specialization. Canonical versus matrix DLIN is correctly separated; the column reduction's `d·DLINAdv+4d/p` loss is disclosed. |
| D | Realisability ranges over the specified machine-derived adversaries; encoded advice is polynomially bounded. The fixed-order hypotheses are consistent restrictions. `PGSound` is necessary and supplied for the layered instance. The exponent-bijection use is proof-only; no algorithmic discrete logarithm was found. Raw inequalities do not assume efficiency targets. |
| E | Public readers and explicit target readers are present; no new simp/global attribute was found. Full Rule 10 seals/controls remain the disclosed final-gate obligation and were not run here. |
| F | S1–S3 confirmed as above. S4/S5 and S7–S11 have the disclosed/new-content dispositions; no additional substantive duplicate was found. For S6, require agreement on `PublicParams` with io-sprg before landing; this audit does not certify the separate job's unpublished interface. |
| G | Source locators checked against the PDFs; Wee20's main claim is correctly unnumbered and its numbered theorem is App. B Thm. 1. Remaining documentation defects are listed above. |
| H | All nineteen intake findings graded below. |

## Intake grading

| Intake ID | Grade | Reason / disposition |
|---|---|---|
| PHFE-C0-F01 | agree — blocker | G51-03; repair also bounds allowed-value words. |
| PHFE-C0-F02 | regrade — minor | G51-12; unexecuted status is explicit, so the pack's misleading-evidence major criterion is not met. |
| PHFE-C0-F03 | agree — minor | G51-01; record the familywise reading. |
| PHFE-C0-F04 | agree — minor | G51-06; the corrected rank calculation is sound. |
| PHFE-C0-F05 | agree — minor | G51-05; witness order is acceptable, binder is redundant. |
| PHFE-C0-F06 | agree — minor | G51-07; reuse retained, owner promotion recorded. |
| PHFE-C0-F07 | agree — minor | G51-08; disclosed near-copies, no closing existing GT lemma found. |
| PHFE-C0-F08 | agree — minor | G51-09; encoding overlap needs disclosure. |
| PHFE-C0-F09 | agree — minor | G51-10; remove unused facade citations. |
| PHFE-C0-F10 | agree — minor | G51-11; update delivered-state wording. |
| PHFE-C0-F11 | agree — note | The FE-local machine adapter is a disclosed namespace choice. |
| PHFE-C0-F12 | agree — note | Chat rulings are recorded in the payload; their records reconciliation remains with Seyoon. G51-04 separately repairs the field's specification. |
| PHFE-C0-F13 | agree — note | `PGSound` is necessary and discharged for the actual instance. |
| PHFE-C0-F14 | agree — note | The line-count overrun is real; PARTIAL continuation was explicitly allowed. |
| PHFE-C0-F15 | agree — note | Finer module splitting stays within scope; coordinate the common parameter interface at landing. |
| PHFE-C0-F16 | agree — note | No contrary process evidence found. This audit used the attached sources and the corrected cloud procedure. |
| PHFE-C0-F17 | agree — note | Full seals are pending as disclosed; this is allowed at M0. Audit search probes do not replace them. |
| PHFE-C0-F18 | agree — note | Input-dependent internal draws are legitimate; concrete draw layouts are fixed. |
| PHFE-C0-F19 | regrade — major | Guard, concrete layout and all-typed-key strengthening are acceptable. The asserted circuit-size correspondence needs R1. |

## Source verification

All five hashes were verified in the attachment folder **before reading**. PDFs were read in place; no PDF, page image or excerpt is included in the findings or evidence archive. No clause is marked UNVERIFIED-SOURCE.

| PDF | Verified SHA-256 | Locations read |
|---|---|---|
| gjls21.pdf | `481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed` | Printed pp. 17–20, 22, 57–58, 61, 63–64: DLIN distribution/Def. 3.3; Defs. 4.1–4.3/4.6 and remarks; §9; Thm. 9.2 Hybrid 1; Thms. 10.3–10.4. |
| wee20.pdf | `d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a` | pp. 4–10, 12–14: §§2.1–4.2; App. B Thm. 1 and Lemmas 2–5. |
| jls26.pdf | `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` | PDF pp. 3, 7–8, 21: §§1.1/1.4 and Thm. 5.1. |
| agw20.pdf | `b74c2ac906cf3f40eb5882abb3921433beebdb9fb020ba09ce8a10035b55d11f` | pp. 11–12, 37–39: §§4.1/4.2, Lemma 2; App. A (28)–(32); App. B shapes. |
| iw14.pdf | `ef6c7c6a0103dfea1d8d9d369e3a7de3a0902fa6138a6bedc4c4df4996e65e77` | pp. 6–11: Def. 1, Thm. 3 and §4.2. |

## Checks run

Lean 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Cloud correction applied: commands ran sequentially in the foreground, without a slot wrapper or linked worktree packages.

| Check | Result |
|---|---|
| Exactly one `env TAR_OPTIONS=--no-same-owner lake exe cache get` with the pinned `mathlib-roots.txt` arguments | rc 0. No unfiltered cache fetch or `lake build`. |
| `TCSLIB_OLEANS=$PWD/.lake/g51-oleans bash scripts/lean_check_tree.sh "$m"`, in the delivered order | 285/285 rc 0, zero errors, fresh oleans; 914 seconds total recorded module time. |
| `G51Probe/Probe` through the same checker | Final rc 0. Selected signatures checked; six headlines and the L1 link have only standard axioms plus expected `sorryAx`. All six audit lemmas about growth, padding and sampler collisions have only standard axioms. |
| Nine `exact?` and nine separate `apply?` probes | All 18 final processes rc 0. Each runs before the target declaration exists, avoiding self-matches. Only `forward_root` closes, by `rfl`: an acceptable reader of the new definition. Other exact searches use an explicit fallback admission; partial suggestions are not claimed proofs. |
| Exact finite algebra checks | Rank counts at p=2,3; canonical/matrix random-law comparison at p=2,3,5; 3,696 small layered-input cases and 621,828 draw cases, including degree/input/output zero and moduli 1,2,3,4. All assertions pass; these finite checks are not general Lean proofs. |
| Static/integrity checks | Counts and hashes above; zero width violations, simp attributes or forbidden declarations in the new source. |

The archive retains one initial main-probe transport error and nine initial generated-probe formatting failures, their corrected sources and final logs. These were audit-harness errors; library sources were unchanged. An optional payload-size command was interrupted (rc 130) when it initiated extra git-object retrieval; seal files were not extracted, inspected or executed. No full payload-size/hash replay or Rule 10 seal execution is claimed.

**Counts, numbered findings:** blockers 2; majors 1; minors 9; notes 0. **Intake grades:** blocker 1; major 1; minors 9; notes 8.

**Verdict: HOLD.** Resolve G51-02, G51-03 and G51-04 before clearing the statements gate.

Glossary: `FE/` is the functional-encryption directory above; κ is the security parameter; ℓ/n are public/private scalar dimensions; d is the public degree bound; p is the group order; q/b are polynomial bounds; T is TM running time; G is the bilinear-group generator; C/S are the surrounding function class/raw scheme; pp/st/v are public parameters/simulator state/function value; U is the shared uniform sampler; y in R3 is a parameter-word map. `CircuitLinearEfficient` is the proposed target defined in R1. Other Lean names retain their source meanings.
