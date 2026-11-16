# Gate 40 — pairing campaign statements, round 2

**CLEAR. Open findings: 0 blockers, 0 majors, 0 minors, 0 notes.**

All six round-1 findings are closed under the stated rulings. The supplemental canonical seals answer the pack’s merged-tree question affirmatively. No new undisclosed change, admission, axiom dependency, or duplication affecting this gate was identified.

| Audited item | Pin |
|---|---|
| Draft PR | [Shilun-Allan-Li/tcslib #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) |
| Lean head | `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| Campaign records | `b356e50b1b908b26c1379f2fa9e53d604dabfe41` |
| Exchange pack | `56eff06a8619dfbac945f37e5ccefb1f5e77c8db` |
| Supplemental records | `98a068069adf25d5cac64eb687e8a4163dbe8626` |
| PR base | `673a27158338437896c624df32bf5421c6ba45cf` |
| Round-1 Lean head | `110c2f9db810d243693b9a5e8976a5ad205f1bab` |

The live GitHub metadata confirms the requested draft, head, and base. This was an audit only; no repository changes, review submissions, dispatches, or merges were made.

| ID | Prior severity | File · declaration | Disposition and evidence | Further fix |
|---|---|---|---|---|
| G40-01 | major | `IdentityBased/Defs.lean:142–159`; `BonehBoyen.lean:243–384` · encoding fields and BB1 witnesses | **Closed under ruling G40-01.** The three fields express the ruled reachable-context injectivity, exclude the round-1 constant-ciphertext countermodel, and are discharged by sound BB1 proofs without new admissions. | None within the ruling. |
| G40-02 | major | Canonical Rule 10 suite | **Closed.** LE-gate40 covers all ten owners; the supplement reruns the suite at the exact merged head. Both have 40/40 passing seals, successful paired controls, and zero foreign explicit unfolds. | None. |
| G40-03 | minor | `BonehBoyenMachine.lean:62–78` · T4 sketch | **Closed.** The sampler now specifies its width, trial count, independent coin blocks, strict order bound, and negligible total error. | None. |
| G40-04 | minor | T4; T1; `Pairing/Group.lean` | **Closed.** T4 has its BB04 source tag; T1 is identified as independently derived folklore; the natural-exponent reader is distinguished from the integer-exponent consequence. | None. |
| G40-05 | minor | `BB1.decrypt_encrypt`; `bb1_correct` | **Closed.** Both existing correctness sketches have the required `**Proof sketch.**` marker. | None. |
| G40-06 | minor | Pairings README; PR description | **Closed.** The README at the supplemental records revision names the correct head/base and historical versus new seal coverage. The live PR description matches `pr-description-r2.md` byte for byte. | None. |

Lean paths in the finding table are under `TCSlib/Cryptography/AdvancedEncryption/`, except where `Pairing/` is specified.

**Encoding repair.** The round-1 countermodel produces two distinct ciphertexts under the same setup output and maps them to the same wire string. Applying the new `encCT_inj` to those two reachable outputs would force the distinct ciphertexts to be equal. Hence that instance no longer satisfies `IBEScheme`.

The fields cover the public parameters, extracted private keys, and challenge ciphertext supplied to the adversary in BB04 §2.1, with the contextual scope explicitly selected by the ruling. In particular, `encSK_inj` is per setup output; this clearance does not strengthen it to global injectivity or claim an efficient decoder or a generic computational equivalence theorem between typed and wire views. Those stronger claims are not part of the ruled contract. Quantification over the target identity and over messages outside `MsgSpace` strengthens the interface beyond the game’s needs, but is harmless here: BB1 proves the stronger statements.

The three new BB1 proofs are sound:

1. `bb1_encPP_inj` uses the exact generated-description length to remove padding without truncation. Four fixed-width list splits recover equal descriptions and equal element encodings; the group’s encoding injectivity then gives equality of the dependent parameter objects.
2. `bb1_encSK_inj` and `bb1_encCT_inj` work in one fixed description. Their concatenated words have exactly the advertised widths. Removing padding and splitting the words reduces equality to the published injectivity fields for group elements.
3. The `bb1Scheme` obligations correctly traverse possible setup/key/encryption outputs. Public parameters use `length_desc` for both setup draws. Key and ciphertext outputs have the fixed description required by their respective lemmas; `Sigma.mk` lifts equality into the scheme’s dependent types.

These proofs use existing public padding, list, and encoding lemmas. No private replacement host or undisclosed duplicate public result was identified. The new lemmas and their scheme obligations have only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` in the supplied censuses.

**Seals and the supplement.** I independently reconstructed all 40 original LE-gate40 probes and all 40 supplemental probes by removing their hash-checked insertions. The reconstructed sources match the Git blobs at `70c1f444` and `9e7a9648`, respectively. I checked probe and log hashes against runner records, clean error counts, and install/EOF records. I also rederived the conservative request sets from the collector’s closure/catalog rows and checked coverage of the elaborated-term references.

The ten owners are `Group`, `Assumptions`, `Operations`, `Joux`, `Defs`, `BonehBoyen`, `BonehBoyenMachine`, `BonehBoyenSecurity`, and the `IdentityBased` and `AdvancedEncryption` facades. The remaining three changed files contain imports/options only. Each strict A/B and coe A/B variant passes all ten owners. In each harness, all 43 sealed negatives fail exactly once, their 43 readers pass, and unsealed controls pass; I checked diagnostics against the recorded declaration spans. The explicit-unfold scan is unchanged: 164 items, including 116 theorem uses, 40 local/unresolved uses, eight owned definitions, and zero foreign unfolds. Source review supports those dispositions.

The supplement binds all 79 probes to their stored bytes and runner logs: 40 seals, 36 controls, and three auxiliary probes. Its tools match LE-gate40’s archived tools. Request changes are additions only: four rows in each of `Operations`, `BonehBoyenMachine`, `BonehBoyenSecurity`, and `IdentityBased`; 148 in `AdvancedEncryption`. They account for the merged IterateFind helpers and expanded GSW closure. **This is sufficient evidence at the merged head; no seal rerun remains outstanding for this audit.**

**Merge, documents, and unchanged confirmations.** Git-tree comparison confirms that merge `39d42e235a62b7085ffc19b01f371015c20d7795` takes every single-sided change from its owning parent. Only the two shared facades changed on both sides. The root equals the PR parent because it already contains the tip’s import; `AdvancedEncryption.lean` is the filed union of both imports, contents entries, and references. No other path differs from both parents. Against the tip parent, the merge changes exactly #331’s 13 files. The head’s only subsequent change is LE-doc-abs in the `Assumptions` module docstring.

LE-doc-abs agrees with the authorized DW-7 transcription of BB04 §3.1: the paper uses an absolute difference for output zero. Complementing Boolean output changes the sign of the difference and preserves its absolute value. No inconsistent advantage claim remains in the 13 Lean files; the IBE factor of two remains correctly disclosed. The stale README and plan wording in the original pack are distinguishable from the refreshed records at the supplement revision; they were not treated as current summaries.

Independent comment-stripped comparison confirms that `Group`, `Assumptions`, and `BonehBoyenMachine` changed only in documentation. `Defs` adds exactly the three fields; `BonehBoyen` adds exactly the encoding section and scheme obligations. `Operations`, `Joux`, and `BonehBoyenSecurity` are byte-identical to round 1. T1–T4 and `bb1_sidSecure` retain their statements. The new proof fields do not alter the old computational projections or the simulator.

The round-1 confirmations therefore still hold: the target statements have sound mathematical routes; T2–T4 suffice for the existing headline with the same two order-error charges, four simulation-error charges, and two DBDH advantages; the completed group/Joux/BB1 proofs, setup order, handler cases, simulator, fill split, layering, and facade exports remain valid under the rulings. T1–T4 remain admissions, and `bb1_sidSecure` remains proved modulo T2–T4. The two later-fill notes are outside this re-audit.

**Verification and limits.**

| Evidence | Independently checked result |
|---|---|
| Round-2 top-level manifest | 17/17 matching files; bundle SHA-256 `5ad33e669a2bab6788165a9fd6f9722666d5838a353d699ae65f2bbe512f187c` |
| Round-1 top-level manifest | 13/13 matching files at exchange `870bed6ca6d79f43599ab2972f74834137672b2a` |
| `verification-r2.zip` | 31/31 listed payloads match; no extra payloads |
| LE-gate40 inner manifest | All 448 present payloads match; the five absent `current.pid` bookkeeping files are exactly the disclosed omissions |
| Integration inner manifest | 794/794 listed payloads match |
| Supplemental inner manifest | 415/415 listed payloads match; external and internal manifests agree |
| Supplemental ZIP | SHA-256 `5b3b520379cc4b991985b4a432917cdf485f40e1959e2a0352c4e5bf15f56895`; bound to supplemental Git records |
| Bundle and source closure | All 21 bundle sections and 110 head-source files match their pinned Git blobs |
| Build source binding | All 1,299 closure source files match both the merge’s Git blobs and their matching build records; an independent root-and-Checks import walk yields the same 1,299 modules |
| Supplied build results | Merge: 661/661 rebuilt modules have clean logs and successful records; supplied whole-tree check is OK. Supplement at the exact head: 41/41 successful builds over its 109-module closure |
| Admissions | 237 → 241, exactly one T1, two T2/T3, and one T4; no other count changes |
| Axioms | New injectivity lemmas, BB1 correctness, and Joux results are standard-only; each target’s closure has only its own direct admission; `bb1_sidSecure` inherits exactly T2–T4 |
| Incident checks | The 31 rechecked modules match their original source/object/log hashes and diagnostic counts |
| Lint | Cryptography baseline 92 FAIL / 101 WARN → 92 FAIL / 103 WARN: no new FAIL; the two new acronym WARNs have the existing readers `sidSecure_iff`, `bdhAssumption_iff`, and `dbdhAssumption_iff` |

No independent Lean elaboration was performed. Build and axiom conclusions refer to the supplied, hash-bound evidence, checked against source and raw logs. The original PDFs and SSH signer identities were not independently authenticated; the authorized source transcriptions and Git objects were used. No necessary evidence is missing within this audit’s scope.

The integration build after #327/#324 on branch tip `201bf57a` remains a maintainer merge condition, outside this verdict. The user retains dispatch and merge authority.
