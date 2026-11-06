## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03f1-pack-r2.md =====

# Gate 03f1 ([PS10] ch. 2–4, discrete log, its hard-core bit, ElGamal), round 2: delta audit pack

**What is audited:** the repair of round 1, on `cryptography/pass-shelat-ch2-4` at `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95` (the merge of
[Shilun-Allan-Li/tcslib#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206), the gate 03 repair batch, and the records commits of 2026-11-06).
- **The round 1 findings** are `findings/gate03f1-findings.md` (in the bundle, verbatim), the maintainer's review `review/gate03f1-review.md`, and the resolutions `resolutions-03f1-r1.md`.
- **The repair:** #206's diff (`evidence-repairs/03-batch/repair.diff.txt`; it covers five gates, and only this pack's files are under audit) and the records changes named in the resolutions.
- **The deliverable:** **`gate03f1-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header. **The source is attached separately:** [PS10] (PDF; book page = PDF page − 12).

## Brief for the auditor

1. **Verify each resolution** of `resolutions-03f1-r1.md`: fixed, recorded, scheduled, or not resolved (and why).
2. **Audit the changed surface afresh:**
   - **the rewritten sketch of `fullDLCollection_hardCore`** (the major): recompute its coin budget, the statistical term `(1 + 16n^{2c+2})·2⁻ⁿ`, `T ≤ 16n^c` and the success bound, and say whether a worker following it can prove the statement as stated (`hbig` kept, ruling R-03f1-1 (A));
   - the new lemmas `sampleBelowL_eq_rejectBlocksL` and `rejectBlocksL_eq` (each an equation and nothing more);
   - the docstring changes (#3, M1, M3).
3. **Check that nothing else changed** in this pack's files: the statement diff (`statements.txt`) lists every added and changed declaration of the batch.

Pack 03a's severity guide applies. Attempt at least one adversarial instantiation against the changed surface. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Findings, resolutions, the diff | as above |
| Under audit, at the pin | `Candidates/{DiscreteLog, DiscreteLogHardcore, ElGamal, Concrete}.lean`; records: `briefs/pass-shelat/inventory-ch2.md` (Claim-62.2) |
| Context | `03f1-pack.md` and earlier round packs, `03a-pack.md`, `policy.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03-batch/`)

- **Elaboration** (`replay.log`): the 128 modules downstream of #206's 21 changed files, then `audits/pass-shelat/Checks`, each checked alone after a base sync (`base-sync.log`): **129 of 129 pass, 0 errors**; every module's `sorry` count equals the base. A maintainer re-check of 8 key modules also passes (`maintainer-recheck.log`).
- **Axioms** (`axioms.log`): 549 prints over the 21 files, compared with the base: no axiom set changed; the 10 new lemmas are standard.
- **Seal** (`seal.log`): the consumers of `ProverBounded` pass sealed (their base versions fail); the new proofs pass with the definitions they could unfold sealed.
- **Lint** (`lint.log`): `scripts/style_lint.py` and `scripts/campaign_style_lint.py --check8b`, compared with the base: no new finding.
- **Statements** (`statements.txt`): 10 added, 2 changed (the two ruled ones in `NP.lean`), 0 removed.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per resolution row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`. The gate closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03f1-findings.md =====

# Gate 03f1 — external statement audit findings

**Verdict: DO NOT CLOSE — 0 blockers, 1 major, 2 minors.** The major is a materially incorrect random-tape/statistical-error calculation in the trusted proof sketch of `fullDLCollection_hardCore`; it does not require changing that theorem’s signature. All **21 admitted declarations** were assessed: **15 (a), 6 (b), 0 (c)**. Category (b) records a true statement with narrower scope or weaker sampling requirements than the source, including explicitly declared deviations; it is not automatically a defect. None of these verdicts claims a completed Lean proof.

Audited the attached four candidate files at [commit `0c348ff94cacf24d96d99078c9dd9e328530c8d2`](https://github.com/Shilun-Allan-Li/tcslib/commit/0c348ff94cacf24d96d99078c9dd9e328530c8d2), against the attached Pass–shelat third edition, book pp.36, 52–53, 62, 82–86, 105–107, and Definition 102.2 on p.102 (PDF page = book page + 12). Used the bundled Arithmetic/Collections interfaces, design, inventories, policy and prior-audit records. Supplemental repository reads were pinned to the same commit: the four audited files were byte-checked by Git blob hash; Adversary/Ensembles were consulted for experiment semantics; HardCore/HardCoreCollection for interface context; and [Rabin.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/0c348ff94cacf24d96d99078c9dd9e328530c8d2/TCSlib/Cryptography/Candidates/Rabin.lean) solely to resolve Claim-62.2’s location and statement. No tactic-proof audit or independent Lean replay was performed.

Input fingerprints: bundle SHA-256 `051bac59bdd0f563bd4ddd8916552f77e30542daa94b51b7e4213b524bf9b534` (17 sections); PDF SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Line numbers below are within the individual bundled source files. Candidate filenames abbreviate `TCSlib/Cryptography/Candidates/`; names inside `ExpGroupGen`, `GroupPKScheme` and `DistinctPrimes` retain their source namespaces where needed.

The single table contains the findings, all 21 individual sorry verdicts, independent mathematical restatements of every definition, statement/docstring assessments of every theorem (including the four private helpers), the required adversarial instantiations, and all inventory dispositions. A dash in “Sorry verdict” means that row is not an individual admitted declaration; dependencies on admissions are separately reflected in the axiom evidence.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix | Sorry verdict |
|---|---|---|---|---|---|---|
| 1 | major | `DiscreteLogHardcore.lean:550` · `fullDLCollection_hardCore`, proof sketch | The proposed random-tape budget does not implement the cited rejection sampler; the displayed final statistical loss also has the wrong coefficient. The theorem itself is true under its stated restrictions. | The sketch allocates `2n` bits per majority trial but cites `sampleBelowL m (Nat.size m) n n`, which needs `n²` bits when `Nat.size m = n`. On only `2n` bits, after two rejected blocks the next empty block reads as zero and is accepted. For prime `p = 523`, `n = 10`, `m = p−1 = 522`, the resulting distance from uniform is `(1−522/1024)²(1−1/522) = 32823521/136839168 ≈ 0.239869`, not at most `2⁻¹⁰`. Also `nℓ = 16n^(2c+2)`, so the stated union bound `(nℓ+1)2⁻ⁿ` does not yield the final `2n^(2c+2)2⁻ⁿ`. Finally, `T = ceil((p−1)/s)` depends on the input index and is not itself a coin polynomial in `n`. | Replace the sketch by a consistent construction. For sufficiently large `n`, take `ε = 1/(2n^c)`, `s = floor((p−1)/(8n^c))`, `ℓ = 16n^(2c+1)`, and bound `T ≤ K(n) := 16(n+1)^c+1` using `p−1 ≥ 16n^c`. Use `n²` bits to sample `t < T` and `n²` bits for each of the `nℓ` exponents, plus independent adversary coins: total `n²+nℓ(n²+A.coinLen n)`, a fixed polynomial. Guard small parameters and malformed inputs; eventually `T < 2^n`. The resulting lower bound is `3ε/(8K(n)) − (1+16n^(2c+2))2⁻ⁿ`, still non-negligible infinitely often. Alternatively keep `2n` bits but explicitly switch to reduction modulo the order and prove its different sampling lemma. No theorem-signature change is needed. | — |
| 2 | minor | `inventory-ch2.md:194,445,517`; `03f1-pack.md` · Claim-62.2 | The advertised location and hence the bundled coverage of the Rabin symmetry lemma are stale. | `Concrete.lean` has no Claim-62.2 statement. At the exact audited commit, it is `Candidates/Rabin.lean:198`, `rabin_symmetry`, with distinct odd primes and an optional-output root finder. This agrees with DESIGN §6, which assigns the item to Cand2. I retrieved that pinned declaration to resolve the discrepancy; this does not turn the rest of Rabin into gate-03f1 scope. | Point the inventory to `Rabin.lean · rabin_symmetry` and mark it as gate-03f2 context, or explicitly include that declaration when asking this pack to audit it. | — |
| 3 | minor | `ElGamal.lean:49,294` · P8-1 repair explanation | The repaired definitions are correct, but the explanation overstates when the old dependent-sum definitions made DDH false. | Randomness of the generator alone is insufficient: if `q` is fixed and only the generator element varies, both old fibre weights are constant, hence both instance marginals are still uniform. Even variation of `q` need not produce a non-negligible gap, for example when comparable orders differ only on exponentially rare coins. The old bug was the unjustified change of instance law, with concrete bad families, not a universal impossibility for every randomized or varying-order generator. | Replace both universal claims by “can give different instance laws and can make the assumption false for reasons unrelated to DDH.” Do not revert the product-seed repair. | — |
| 4 | note | Bundle identity and execution evidence | The four in-scope Lean files exactly match the pinned repository blobs; the evidence counts reconcile. | Pinned commit: `0c348ff94cacf24d96d99078c9dd9e328530c8d2`. The replay contains 89 distinct module checks, all `rc=0, errors=0`, totalling 39 sorry warnings. The axiom log contains 150 theorem/lemma entries: 124 in the four audited files plus 26 in contextual `Arithmetic.lean`; 34 mention `sorryAx`, 116 only standard axioms, and no other axiom name occurs. The four source files have exactly 21 admitted declarations (6+7+7+1). Thus “5 files” in the lint log includes Arithmetic. | These are checked maintainer attestations, not an independently rerun Lean build. Tactic proofs were outside scope. | — |
| 5 | note | Independent finite semantic checks | Finite checks support the algebraic review and reproduce the major finding; they do not prove the asymptotic theorems. | Exhaustively checked all seeds for the 26 pairs `1 ≤ n ≤ 4`, `0 < m < 2^n` in `sampleBelowL`; all 107,122 `(p,g,e)` cases for full-group generators at primes `p < 200`, `p ≡ 3 mod 4`, in perfect-oracle inversion; and 30,726 ElGamal cancellation cases at safe primes 5, 7, 11, 23, including `h=1`. All intended identities passed. The short-tape sampling counterexample in finding 1 was evaluated with exact rational arithmetic. | None. | — |
| 6 | note | Adversarial instantiation 1 · identity and small groups | A purported generator equal to the identity is excluded by the hardness-instance validity predicates; the encryption scheme handles its own identity case differently. | In `SafePrimeValid`, `orderOf 1 = 1` contradicts prime `q ≥ 2`; in `FullGroupValid`, `p ≡ 3 mod 4` implies `p−1 ≥ 2`, likewise excluding it. Generic `ExpValid` does allow order 1, but the constant zero-exponent inverter succeeds on such indices, so non-negligible mass there contradicts `DLHard`. ElGamal deliberately allows `h=g²=1`: decryption remains correct, while messages become exposed. Its probability is bounded by `δ(n)+9·2⁻ⁿ` under `hbig`; a generator always outputting a padded constant prime fails `hbig` and the relevant hardness assumption. | None. | — |
| 7 | note | Adversarial instantiation 2 · nonuniform exponents and varying orders | Neither ensemble lets an adversary replace the specified exponent law by an arbitrary biased law. | Both DDH seed spaces are ordinary products. Therefore each generator coin string has probability `1/card(G.gen.Coins n)` in both worlds, even when `q` varies. Conditional on that string, exponent blocks are independent and each is at distance at most `2⁻ⁿ` from uniform. Thus the real and random ensembles are within `2·2⁻ⁿ` and `3·2⁻ⁿ` of their respective ideal-exponent laws, and replacing both changes any distinguishing advantage by at most `5·2⁻ⁿ`. Small parameters are a finite exception. P8-1 is repaired. | None. | — |
| 8 | note | Adversarial instantiation 3 · advice knowing the group | Giving the predictor advice about the group does not invalidate the reduction or evade its quantifiers. | `DLHard` and `Collection.HardCore` quantify over every NUPPT, with parameter-indexed polynomial advice; the entire group index is already part of the input. Fixing the generator coins defines a per-instance predictor that keeps the same advice. `good_instances` averages these conditional success probabilities; the inverter need not recognize the good set. It reuses the predictor advice at the same parameter. If advice makes a small or otherwise easy family invertible, that family fails the DL hypothesis, rather than satisfying a vacuous hard-core claim. | None. | — |
| 9 | note | Adversarial instantiation 4 · boundary parameters and malformed inputs | The collection fallback, empty-trial cases, and decoder restrictions do not create false sampling or inversion statements. | For `n=0`, `0<m<2^n` is impossible, so the special sampler closeness theorem has no missing zero case. In the general rejection lemma `T=0` gives the valid distance bound 1, and the supplied default makes the target subtype nonempty. Below `G.n₀`, the exponentiation collection uses a valid width-2 index and even a zero-coin sampler returns the encodable exponent 0. Wrong-length inversion answers fail both experiments. The raw polynomial-time claims are total-function claims: their fills must also handle arbitrary widths, zero moduli and overlapping/truncated blocks, not silently assume honest inputs. | None. | — |
| 10 | note | Adversarial instantiation 5 · messages outside the subgroup | The group restriction is substantive; canonicalisation is not a reversible encoding of arbitrary messages. | Without canonicalisation, the Legendre symbol of `c₂=h^(ab)m` equals that of `m`, so a residue and a nonresidue are perfectly distinguishable. At `p=7,q=3`, both natural messages 0 and 3 are canonicalised to 1; hence arbitrary bit-string messages are not recovered. For a valid generated key, however, `egCanon p q m=m` is exactly subgroup membership: the fallback only adds `m=1`, which is already a member. The formal correctness theorem therefore covers every claimed message. | None. | — |
| 11 | note | `DiscreteLog.lean:117` · `dlP`, `dlM`, `dlG`, `dlW` | These definitions read the first numeral, the first nested numeral, the final nested numeral, and the width of the first numeral, respectively. | They use total pair projections, so arbitrary malformed strings still have values; none of these definitions asserts validity. | None. | — |
| 12 | note | `DiscreteLog.lean:132` · `WellFormedIndex` | An index is exactly a nested pair of three width-n strings. | This is encoding width, not a leading-one or full-bit-length condition. The separate full-length predicates supply the latter where needed. | None. | — |
| 13 | note | `DiscreteLog.lean:136` · `WellFormedIndex.dlW_eq`, `WellFormedIndex.length_eq`, `dlP_lt_two_pow` | `dlW_eq` correctly recovers width n. `length_eq` correctly gives total length `5n+4`. `dlP_lt_two_pow` correctly bounds the parsed number by its width. | These statements match their docstrings; leading zeros are allowed. | None. | — |
| 14 | note | `DiscreteLog.lean:154` · `ExpValid` | Validity means p is prime, `0<m<p`, `0<g<p`, and g has exact order m modulo p. | It does not require a canonical index or m prime; those are deliberately separate requirements. Its undecidable/noncomputable use in semantic domains is not a claim that honest machines decide group order. | None. | — |
| 15 | note | `DiscreteLog.lean:162` · `expOrd` | The semantic domain order is the parsed m at valid indices, and 1 otherwise. | The statement matches its docstring. | None. | — |
| 16 | note | `DiscreteLog.lean:171` · `expOrd_of_valid`, `expOrd_of_not_valid`, `expOrd_le_two_pow`, `val_lt_two_pow_dlW` | `expOrd_of_valid` and `expOrd_of_not_valid` state the two correct branches. `expOrd_le_two_pow` bounds the order by the encoding capacity. `val_lt_two_pow_dlW` consequently bounds every residue. | These include invalid indices and width zero; the default order 1 is essential there. | None. | — |
| 17 | note | `DiscreteLog.lean:188` · `coprime_dlG_dlP` | A valid nonzero residue is coprime to the prime modulus; the statement matches the docstring. | The statement matches its docstring. | None. | — |
| 18 | note | `DiscreteLog.lean:192` · `expUnit` | This is the parsed generator as a unit, using the coprimality supplied by validity. | The statement matches its docstring. | None. | — |
| 19 | note | `DiscreteLog.lean:196` · `coe_expUnit`, `orderOf_expUnit` | `coe_expUnit` correctly identifies its residue. `orderOf_expUnit` correctly transports the exact order m to the unit group. | The statement matches its docstring. | None. | — |
| 20 | note | `DiscreteLog.lean:207` · `expEnc`, `expDec` | `expEnc` writes the residue at index width; `expDec` accepts exactly strings of that width whose value is below the semantic order. | The decoder does not identify differently sized encodings. This is the needed canonical domain representation. | None. | — |
| 21 | note | `DiscreteLog.lean:215` · `expDec_expEnc`, `expEnc_of_expDec` | `expDec_expEnc` gives the decoding left inverse. `expEnc_of_expDec` gives the encoding right inverse on every accepted string. | The gate-03b canonicity repair is present and mathematically correct; the new Collection field is genuinely discharged. | None. | — |
| 22 | note | `DiscreteLog.lean:231` · `expF`, `expEval` | `expF` encodes `g^x mod p` at index width; `expEval` rearranges a string pair into the modular-exponentiation input. | Neither definition silently converts exponents or outputs to a different group. | None. | — |
| 23 | note | `DiscreteLog.lean:241` · `expEval_spec`, `polyTimeComputable_expEval` | `expEval_spec` correctly identifies evaluation on every encoded domain element. `polyTimeComputable_expEval` follows from `H.modExp` and polynomial pairing/projections. | The statement matches its docstring. | None. | — |
| 24 | note | `DiscreteLog.lean:262` · `expF_injective` | Equal encoded exponentials have equal residues, hence equal exponents in `Z_m`, because g has order m. | The theorem is correct as an injectivity statement. It is not a packaged bijection onto an explicit safe-prime range or a `PermCollection`; see Claim-53.2 coverage below. | None. | — |
| 25 | note | `DiscreteLog.lean:291` · `ExpGroupGen` | A uniform polynomial-time machine supplies valid, width-n indices for every coin string from a fixed threshold onward. | It imposes no uniform law on primes or generator elements and no full-length condition. Assumptions relative to this law are deliberate conditional variants of the source, not a proved equivalence with its ideal index law. | None. | — |
| 26 | note | `DiscreteLog.lean:314` · `FullLength`, `FullLengthExcept` | `FullLength` requires `p≥2^(n−1)` for every generated index above the threshold. `FullLengthExcept δ` instead bounds the probability of violating that inequality by δ(n). | Only the latter, together with negligible δ, is used in the two headline results. P8-2 is repaired; existence of such generators remains an explicit assumption, not a theorem. | None. | — |
| 27 | note | `DiscreteLog.lean:341` · `dlProb`, `DLHard` | `dlProb` first averages over uniform generator coins, then over an ideal uniform exponent and independent adversary coins, and counts exactly decoded exponent recovery. `DLHard` requires this probability to be negligible for every NUPPT. | The order of averaging does not tilt the instance law. The adversary receives the parameter and complete index, matching the declared correction of Assumption 52.2. | None. | — |
| 28 | note | `DiscreteLog.lean:355` · `dlProb_nonneg`, `dlProb_le_one` | `dlProb_nonneg` correctly gives the lower probability bound. `dlProb_le_one` correctly gives the upper bound; all generator coin spaces are nonempty. | The statement matches its docstring. | None. | — |
| 29 | note | `DiscreteLog.lean:368` · `ExpGroupGen.FullLength.fullLengthExcept`, `ExpGroupGen.FullLength.exists_fullLengthExcept` | `fullLengthExcept` correctly takes δ=0 when full length holds everywhere. `exists_fullLengthExcept` adds negligibility of zero and supplies the existential headline hypothesis. | The statement matches its docstring. | None. | — |
| 30 | note | `DiscreteLog.lean:394` · `dlDefaultIndex` | The fallback is the width-2 encoding of `(p,m,g)=(3,2,2)`. | It is an exponentiation-valid instance, not a safe-prime instance. This is sufficient for Collection membership below the threshold and changes no asymptotic experiment. | None. | — |
| 31 | note | `DiscreteLog.lean:398` · `expValid_dlDefaultIndex` | The fallback is valid because 2 has order 2 modulo 3; the statement is exact. | The statement matches its docstring. | None. | — |
| 32 | note | `DiscreteLog.lean:419` · `expGenFun`, `expGen` | `expGenFun` runs the original uniform generator at or above the threshold and otherwise emits the fallback, attaching an empty trapdoor. `expGen` packages that function with the original coin polynomial. | The statement matches its docstring. | None. | — |
| 33 | note | `DiscreteLog.lean:427` · `expGenFun_poly`, `expGen_runAt` | `expGenFun_poly` is a fixed-threshold test followed by a polynomial computation. `expGen_runAt` gives the two exact activation branches, using uniformity to erase advice. | The statement matches its docstring. | None. | — |
| 34 | note | `DiscreteLog.lean:465` · `sampleBelowL` | This is the first accepted number below m read from T prefixes of length k at block stride B, or none. | The definition permits short or overlapping blocks. Independence and uniformity require the hypotheses of the later statistical theorem, rather than following from this definition alone. | None. | — |
| 35 | note | `DiscreteLog.lean:471` · `sampleBelowL_lt` | Every accepted value is below m, even on malformed or short coin lists; the statement is correct. | The statement matches its docstring. | None. | — |
| 36 | note | `DiscreteLog.lean:499` · `statClose_sampleBelowL` | True as stated: the width-n, n-trial sampler with fallback 0 is within `2⁻ⁿ` of uniform on `[0,m)`. | Put `k=Nat.size m`. Then `k≤n`, `m/2^k≥1/2`, and the sampled prefixes are independent uniform k-bit values. Conditional on any acceptance the output is uniform; the total law is `(1−λ)U+λ·point(0)`, where `λ=(1−m/2^k)^n`. Its exact distance is `λ(1−1/m)≤2⁻ⁿ`. No arithmetic hypothesis is needed. | None. | a |
| 37 | note | `DiscreteLog.lean:508` · `expSampleRaw` | The raw sampler reads m from the index, uses n trials with stride n, and writes the accepted value or zero at the index width. | The statement matches its docstring. | None. | — |
| 38 | note | `DiscreteLog.lean:522` · `polyTimeComputable_expSampleRaw` | True as a total polynomial-time string function under the arithmetic bundle. | Use `H.size`, `H.le` (with negation for strict comparison), bounded iteration, and fixed-width padding. The repaired bundle already contains the bit-length field; the “requested shared primitive” wording is stale, not a missing hypothesis. With arbitrary inputs, k is bounded by input size even if k exceeds n. | None. | a |
| 39 | note | `DiscreteLog.lean:527` · `expSampler` | This packages the raw domain sampler as a uniform NUPPT with exactly n² coin bits. | The statement matches its docstring. | None. | — |
| 40 | note | `DiscreteLog.lean:531` · `expSampler_runAt` | The stated activation is exactly the n-trial sampler followed by index-width encoding; its statement matches the docstring. | The statement matches its docstring. | None. | — |
| 41 | note | `DiscreteLog.lean:549` · `expSampler_spec` | True at every parameter and every generated coin string: the sample decodes and its evaluator agrees with the domain function. | Above the threshold use `hV` and `G.valid`; below it use `expValid_dlDefaultIndex`. Every accepted value or fallback 0 lies below positive m, and below the numeral capacity. Set x to its residue, then apply canonical decoding and `expEval_spec`. This validates the P3-1 repair, including n=0. | None. | a |
| 42 | note | `DiscreteLog.lean:565` · `expCollection` | This is the Collection with domain `Z_(expOrd i)`, the canonical exponent encoding, exponentiation function, repaired generator, domain sampler and modular evaluator. | Its semantic data and machine fields are connected by the required equations. It makes no unproved uniformity claim inside the structure. | None. | — |
| 43 | note | `DiscreteLog.lean:584` · `expCollection_index`, `expCollection_index_of_lt`, `expCollection_D` | `expCollection_index` correctly identifies the original index above the threshold. `expCollection_index_of_lt` correctly identifies the fallback below it. `expCollection_D` states the exact semantic domain. | The statement matches its docstring. | None. | — |
| 44 | note | `DiscreteLog.lean:618` · `expCollection_sampleClose` | True; the source’s exact domain sampling has been replaced by negligible statistical error under D10. | Choose δ(n)=1 below the threshold and δ(n)=2⁻ⁿ above it. The former bounds any two probability laws; the latter follows from `statClose_sampleBelowL`, exact decoding, and transport from `Fin m` to `Z_m`. Finite modification preserves negligibility. | None. | b |
| 45 | note | `DiscreteLog.lean:635` · `expCollection_invProbAt_le` | True: at parameters above the threshold, the same adversary’s collection inversion event implies its discrete-log recovery event. | Injectivity forces the decoded preimage to be the original exponent. The canonical decoder forces width n and its integer value; therefore `decodeFin n` and `bitsToNat` recognize exactly that exponent. Averaging preserves the implication; no sampling approximation is used because both experiments use ideal exponents. | None. | a |
| 46 | note | `DiscreteLog.lean:647` · `expCollection_oneWay` | True in the library’s D10 collection notion, whose sampling clause is weaker than exact uniform sampling in the source. | The sampling clause is the preceding negligible-closeness theorem. The hard clause follows pointwise above the threshold from `expCollection_invProbAt_le` and `G.DLHard`, then by finite-prefix closure of negligibility. No missing field of ArithmeticFP was found. | None. | b |
| 47 | note | `DiscreteLog.lean:656` · `SafePrimeValid`, `SafePrimeGen` | `SafePrimeValid` adds prime order q and `p=2q+1` to exponentiation validity. `SafePrimeGen` abbreviates a generator of those instances. | The generated subgroup is the unique order-q subgroup of units, hence the squares. The notation “length n” in the abbreviation’s prose means padded width unless a full-length hypothesis is supplied. | None. | — |
| 48 | note | `DiscreteLog.lean:660` · `SafePrimeValid.expValid` | This is the correct validity projection used by the collection construction. | The statement matches its docstring. | None. | — |
| 49 | note | `DiscreteLog.lean:676` · `DLAssumption` | This is exactly `G.DLHard` for the supplied safe-prime generator; it assumes rather than proves hardness for that law. | The statement matches its docstring. | None. | — |
| 50 | note | `DiscreteLog.lean:679` · `dlAssumption_iff` | The equivalence correctly exposes the universal-NUPPT negligibility quantifier. | The statement matches its docstring. | None. | — |
| 51 | note | `DiscreteLog.lean:689` · `dlCollection` | This specializes the generic collection to safe-prime indices, with the stated finite-prefix fallback. | The statement matches its docstring. | None. | — |
| 52 | note | `DiscreteLog.lean:693` · `dlCollection_index`, `dlCollection_oneWay` | `dlCollection_index` correctly identifies generated safe-prime indices above the threshold. `dlCollection_oneWay` correctly specializes the generic one-way theorem under DLAssumption and ArithmeticFP. | This faithfully implements Theorem 52.3 subject to the explicitly chosen group family, generator law and D10 sampling relaxation; it does not establish those hypotheses. | None. | — |
| 53 | note | `DiscreteLogHardcore.lean:103` · `expo`, `halfBit`, `IsGenerator` | `expo` raises a unit to the canonical exponent residue. `halfBit` tests `2·x.val<m`. `IsGenerator` means every unit belongs to the cyclic subgroup generated by g. | These are full-unit-group definitions, not the prime-order DL collection. For m=0 the predicate is a total false predicate; all uses involving uniform finite exponents have nonzero order. | None. | — |
| 54 | note | `DiscreteLogHardcore.lean:120` · `IsGenerator.orderOf_eq`, `expo_injective`, `expo_bijective` | `orderOf_eq` correctly gives order p−1. `expo_injective` correctly uses that order to distinguish exponent residues. `expo_bijective` upgrades injectivity using equality of the finite cardinalities. | The statement matches its docstring. | None. | — |
| 55 | note | `DiscreteLogHardcore.lean:138` · `dlog` | This is a chosen inverse of exponentiation; it is an actual inverse only when g is a generator. | It is explicitly noncomputable and is used for mathematical specifications, not supplied to the polynomial-time reduction. | None. | — |
| 56 | note | `DiscreteLogHardcore.lean:141` · `expo_dlog`, `dlog_expo` | `expo_dlog` correctly gives the right-inverse identity for generators. `dlog_expo` correctly gives the left-inverse identity. | The statement matches its docstring. | None. | — |
| 57 | note | `DiscreteLogHardcore.lean:152` · `two_mul_half`, `neg_one_ne_one_units`, `pow_half_eq_neg_one` | `two_mul_half` correctly gives positivity and twice the half-order for an odd prime. `neg_one_ne_one_units` correctly separates ±1. `pow_half_eq_neg_one` correctly identifies the unique order-two element as g to the half-order. | The statement matches its docstring. | None. | — |
| 58 | note | `DiscreteLogHardcore.lean:190` · `pow_mem_QR_iff`, `sq_eq_pow_two_mul_iff`, `neg_pow_eq` | `pow_mem_QR_iff` correctly equates residuosity with even exponent for a full-group generator. `sq_eq_pow_two_mul_iff` correctly identifies both roots, also allowing their coincidence at p=2. `neg_pow_eq` correctly shifts the exponent by the half-order. | The “larger exponent” description of the second root is read in the halving application, where x is below half the order; the formal equality itself correctly has no such restriction. | None. | — |
| 59 | note | `DiscreteLogHardcore.lean:219` · `dlRoot` | First divide a nonsquare by g, then exponentiate by `p/4+1`. | This computes a square root for the stated p≡3 mod4 setting. It is not a square-root algorithm for arbitrary odd primes. | None. | — |
| 60 | note | `DiscreteLogHardcore.lean:233` · `dlLoop`, `dlQueries` | `dlLoop` records residuosity parity, selects the root using that round’s oracle coins, and reconstructs the exponent least-significant-bit first. `dlQueries` records exactly those adaptive root queries. | Keeping the root on a true answer and negating it on false is the source’s line 11, as repaired by P8-3. | None. | — |
| 61 | note | `DiscreteLogHardcore.lean:250` · `halfOracle`, `dlBits` | `halfOracle` evaluates the half predicate of the mathematical discrete logarithm. `dlBits` runs the loop with that perfect oracle and a singleton coin space. | The statement matches its docstring. | None. | — |
| 62 | note | `DiscreteLogHardcore.lean:259` · `dlLoop_succ`, `dlQueries_zero`, `dlQueries_succ` | `dlLoop_succ` correctly exposes one step. `dlQueries_zero` correctly gives its first query. `dlQueries_succ` correctly gives each query in the recursive tail. | The statement matches its docstring. | None. | — |
| 63 | note | `DiscreteLogHardcore.lean:287` · `dlLoop_eq_dlBits` | If all actual adaptive queries receive the perfect-oracle answer, the noisy loop and perfect loop coincide. | This implication is correct for arbitrary g and oracle; it asserts agreement with the perfect loop, not inversion without a generator hypothesis. | None. | — |
| 64 | note | `DiscreteLogHardcore.lean:319` · `dlBits_pow` | True, but only for primes p≡3 mod4; the source’s algorithm allows efficient square roots for arbitrary odd primes. | For exponent e, one step records `e mod 2` and selects `g^floor(e/2)`: the other root has exponent `floor(e/2)+(p−1)/2` and the opposite strict-half bit. Induction on k gives the answer because e<2^k, including k=0 and e=0. The restriction is explicit and substantive. | None. | b |
| 65 | note | `DiscreteLogHardcore.lean:338` · `majOracle` | Each trial compares the predictor on `y·g^r` with the known half-bit of r; a strict majority of agreements returns true. | Fresh exponent and predictor coins are supplied per coordinate. Ties return false, an explicitly declared difference from the source; the failure inequality allows this tie rule. | None. | — |
| 66 | note | `DiscreteLogHardcore.lean:357` · `uprob_trial_ge` | True: a trial votes for the correct half-bit with probability at least `1/2+ε/2` in either stated window. | Translation by e preserves the uniform exponent law. In the lower window the target half-bit differs from the translated comparison at only 2e positions; in the upper window write `e=(p−1)/2+d` and use 2d positions after complementing. Each count is ≤2s, hence the probability loss is ≤ε/2. The apparent missing odd-prime and nonempty-coin hypotheses are not counterexamples: feasibility of hA, hs and he excludes p=2 and empty ρ. | None. | a |
| 67 | note | `DiscreteLogHardcore.lean:380` · `uprob_majOracle_ne_le` | True: majority failure is at most `1/(ε²ℓ)` under the stated positive ε and ℓ assumptions. | The ℓ coordinates are independent. With vote-success mean at least `1/2+ε/2`, a wrong majority forces a downward deviation of at least `ℓε/2`; variance is at most ℓ/4, so Chebyshev gives `(ℓ/4)/(ℓε/2)²=1/(ε²ℓ)`. This is an explicit valid replacement for the garbled source bound. | None. | a |
| 68 | note | `DiscreteLogHardcore.lean:393` · `shiftInverter` | Guess a window number t, solve on `y·g^(−ts)`, then add ts modulo p−1. | The output is a residue, so successful recombination is interpreted modulo the group order, as required. | None. | — |
| 69 | note | `DiscreteLogHardcore.lean:408` · `invProb_shiftInverter_ge` | True: its success is at least `(1−δ)/T`. | For every canonical exponent e, choose `t=floor(e/s)<T`; then `e−ts=e mod s<s`. That guess has probability 1/T and the stipulated solver succeeds with probability at least 1−δ. If ρ′ is empty, the hypothesis at e′=0 forces δ≥1, making the conclusion trivial; thus no Nonempty hypothesis is missing. | None. | a |
| 70 | note | `DiscreteLogHardcore.lean:416` · `dlInverter` | This is the shifted inverter whose short-window solver is the k-round majority-oracle loop. | The statement matches its docstring. | None. | — |
| 71 | note | `DiscreteLogHardcore.lean:435` · `invProb_dlInverter_ge` | True: success is at least `(1−k/(ε²ℓ))/T` under the displayed hypotheses. | The predictor bound implies ε≤1/2, hence s≤(p−1)/8. On the perfect trajectory every queried exponent lies in one of the two tested windows; fresh round coins give the per-round failure bound. A union bound on errors at the fixed perfect-path queries, or a first-error argument, gives k/(ε²ℓ), avoiding an unjustified independence assertion for noisy adaptive queries. Apply the range-reduction lemma. | None. | a |
| 72 | note | `DiscreteLogHardcore.lean:449` · `good_instances` | The mean-success hypothesis correctly guarantees at least ε/2 mass with success at least `1/2+ε/2`. | Its assumptions include an upper bound on each success value and nonempty finite instances. Nonnegativity of the values is not needed for this lower bound. | None. | — |
| 73 | note | `DiscreteLogHardcore.lean:461` · `FullGroupValid`, `FullGroupGen`, `FullDLAssumption` | `FullGroupValid` fixes order p−1 and p≡3 mod4; `FullGroupGen` supplies those instances; `FullDLAssumption` assumes negligible inversion for their actual generator law. | The restriction is declared in the module, declarations and DESIGN §8(3). It is benign for this restricted theorem, not an equivalence to unrestricted Lemma 84.1 or to `DLAssumption` for an arbitrary safe-prime generator. No bridge between those different generator laws is proved here. | None. | — |
| 74 | note | `DiscreteLogHardcore.lean:464` · `FullGroupValid.expValid` | The projection to exponentiation validity is correct. | The statement matches its docstring. | None. | — |
| 75 | note | `DiscreteLogHardcore.lean:484` · `fullDLCollection` | This is the generic collection instantiated on the full-group generator. | The statement matches its docstring. | None. | — |
| 76 | note | `DiscreteLogHardcore.lean:489` · `fullDLCollection_oneWay` | The generic one-way theorem correctly applies under FullDLAssumption and ArithmeticFP. | It proves one-wayness, not the hard-core-bit result; the latter needs its separate reduction. | None. | — |
| 77 | note | `DiscreteLogHardcore.lean:496` · `halfPred`, `halfStr` | `halfPred` tests `2x.val+2≤p`; `halfStr` performs the identical test on the two input numerals. | Defining this total numerical predicate avoids asking the machine to decide index validity. At valid full-group indices it is exactly the desired strict half predicate. | None. | — |
| 78 | note | `DiscreteLogHardcore.lean:501` · `halfPred_eq`, `halfStr_spec` | `halfPred_eq` correctly converts the inequality to `2x.val<p−1` at a prime index. `halfStr_spec` correctly identifies the string evaluator on every encoded domain element, including invalid indices. | The statement matches its docstring. | None. | — |
| 79 | note | `DiscreteLogHardcore.lean:526` · `polyTimeComputable_halfStr` | True as a total polynomial-time function from the supplied arithmetic hypotheses. | For all natural p,x, `2x+2≤p` iff `x<floor(p/2)`. Compute the quotient with `H.divMod`, compare with `H.le`, and negate the comparison. This uses neither a square-root oracle nor any unlisted arithmetic field. | None. | a |
| 80 | note | `DiscreteLogHardcore.lean:580` · `fullDLCollection_hardCore` | True under its hypotheses, with narrower group and sampling scope than the source; its current proof sketch needs finding 1 repaired. | An average advantage `n^(−c)` gives at least ε/2 mass of full-length good instances after discarding the negligible short-prime coins, with ε=`n^(−c)/2`. On these, the concrete reduction has inverse-polynomial success. The corrected polynomial coin allocation and negligible sampling loss in finding 1 yield a NUPPT DL inverter, contradicting hDL. The easy half is `halfStr`. Changing the strict half-bit to the source’s inclusive boundary changes prediction success by at most the expected `1/(p−1)`, negligible under hbig. This is a mathematical provability verdict, not a completed Lean fill. | None. | b |
| 81 | note | `ElGamal.lean:114` · `safe_ne_two`, `five_le_safe`, `safe_half` | `safe_ne_two` correctly excludes p=2. `five_le_safe` correctly gives p≥5. `safe_half` correctly identifies both half-order quotients with q. | The hypotheses allow the small safe prime p=5,q=2; the later group claims remain valid in that case. | None. | — |
| 82 | note | `ElGamal.lean:128` · `card_QR_safe`, `mem_QR_iff_pow_eq_one`, `orderOf_eq_of_mem_QR` | `card_QR_safe` correctly gives q squares. `mem_QR_iff_pow_eq_one` correctly recognizes them as the q-th roots of unity. `orderOf_eq_of_mem_QR` correctly assigns order q to every nonidentity square. | The statement matches its docstring. | None. | — |
| 83 | note | `ElGamal.lean:143` · `zpowers_eq_QR`, `eq_QR_of_card` | `zpowers_eq_QR` correctly identifies the subgroup generated by a nonidentity square. `eq_QR_of_card` correctly proves uniqueness of the order-q subgroup. | The statement matches its docstring. | None. | — |
| 84 | note | `ElGamal.lean:163` · `card_sqrt_safe`, `pushesUniform_sqTo_safe`, `uprob_sq_eq_one` | `card_sqrt_safe` correctly gives two roots per square. `pushesUniform_sqTo_safe` consequently gives uniform squares from uniform units. `uprob_sq_eq_one` correctly computes the exceptional identity probability `2/(p−1)=1/q`. | The statement matches its docstring. | None. | — |
| 85 | note | `ElGamal.lean:193` · `statClose_of_uprob_ne` | Two samplers on a common seed space have distance bounded by their disagreement probability. | The event symmetric difference is contained in sample disagreement; the assertion is also true for empty seed spaces under the library convention. | None. | — |
| 86 | note | `ElGamal.lean:220` · `statClose_sq_generator` | True, with the sharp distance 1/q. | Squaring gives the uniform law on q squares. Conditioning that law on not being the identity gives the uniform generator law; the removed mass is exactly 1/q. The theorem proves the required upper bound, while the event `{1}` attains equality. It does not say the fallback-to-4 law is exactly uniform. | None. | a |
| 87 | note | `ElGamal.lean:228` · `ddhTuple`, `ddhLen` | `ddhTuple` pairs the index with three encoded powers. `ddhLen` is the polynomial `15n+14`. | The group modulus/order/generator are included; this is a lossless encoding at well-formed indices. | None. | — |
| 88 | note | `ElGamal.lean:235` · `eval_ddhLen`, `length_ddhTuple` | `eval_ddhLen` evaluates the length expression correctly. `length_ddhTuple` correctly proves that padding is lossless at a width-n index. | The statement matches its docstring. | None. | — |
| 89 | note | `ElGamal.lean:254` · `ddhExpo` | This casts a rejection-sampled integer below the semantic order into its residue group, using an independent n²-bit block. | The statement matches its docstring. | None. | — |
| 90 | note | `ElGamal.lean:259` · `natCast_val_finEquiv_symm` | The private cast identity correctly identifies the uniform Fin-order and ZMod representations. | The statement matches its docstring. | None. | — |
| 91 | note | `ElGamal.lean:273` · `ddhExpo_statClose` | At a valid width-n index, the claimed `2⁻ⁿ` distance to the uniform residue is correct. | The order is positive and below p<2^n, so the sampler lemma applies; mapping by the cast preserves distance. Its proof depends on that admitted sampler lemma, as the axiom log reports. | None. | — |
| 92 | note | `ElGamal.lean:299` · `ddhReal`, `ddhRandom` | `ddhReal` uses two independent exponent blocks and a product exponent; `ddhRandom` uses three independent blocks. | Both use exactly the same generator-coin marginal, with no dependent-sum reweighting. Their padding can be arbitrary only below the finite validity threshold. See adversarial instantiation 2. | None. | — |
| 93 | note | `ElGamal.lean:326` · `DDHAssumption` | This asserts computational indistinguishability of those two ensembles for every NUPPT distinguisher. | The polynomial length is injective in n, and the complete tuple is visible. Ideal uniform exponents give an equivalent asymptotic condition up to a `5·2⁻ⁿ` perturbation; uniform ideal prime generation is a separate, unproved assumption change. | None. | — |
| 94 | note | `ElGamal.lean:340` · `GroupPKScheme` | This structure contains uniform key generation, uniform encryption, and a deterministic polynomial-time decryptor. | It deliberately has neither a message-space field nor a correctness field. Its prose says correctness is supplied separately. A degenerate constant-encryption object can inhabit this structure but does not falsify the separately stated ElGamal correctness result. | None. | — |
| 95 | note | `ElGamal.lean:358` · `challenge` | Generate a key, run the selector on the public key, encrypt the selected component, and output only the public key and ciphertext. | The statement matches its docstring. | None. | — |
| 96 | note | `ElGamal.lean:373` · `Secure` | Every polynomial-time selector/distinguisher pair has negligible challenge-distribution advantage, with the negligible function chosen before all parameters. | The selector may depend on the public key. Although selector coins/state are not sent to D, this loses no nonuniform CPA attack: fix each parameter’s selector tape achieving the signed average advantage into polynomial advice, and let D recompute the selected messages and state. Public encryption also permits simulation of encryption-oracle queries. This equivalence is a mathematical justification of the formulation, not a separately formalized bridge in the file. | None. | — |
| 97 | note | `ElGamal.lean:381` · `constSelector` | This is a zero-coin advised machine returning the two polynomially bounded message families independently of the public key. | The statement matches its docstring. | None. | — |
| 98 | note | `ElGamal.lean:386` · `constSelector_runAt`, `GroupPKScheme.Secure.const` | `constSelector_runAt` correctly returns the advised pair on every input. `Secure.const` correctly removes the selector’s singleton coin space and derives security for each polynomially bounded pair of message families. | Worst-case message families can be selected nonuniformly, so the family quantifier does not hide an exponential collection of message-specific security bounds. | None. | — |
| 99 | note | `ElGamal.lean:445` · `egUnit` | This returns one plus a rejection-sampled number below p−1, with fallback 1. | It is approximately, not exactly, a uniform unit on honest input; the statistical error is accounted for later. | None. | — |
| 100 | note | `ElGamal.lean:449` · `egUnit_pos`, `egUnit_lt` | `egUnit_pos` correctly gives positivity for all arguments. `egUnit_lt` correctly gives strict upper bound p when p≥2, regardless of tape length. | The statement matches its docstring. | None. | — |
| 101 | note | `ElGamal.lean:463` · `egCanon` | Keep m exactly when `0<m<p` and `m^q mod p=1`; otherwise return 1. | For safe-prime keys this is a total retraction onto the subgroup, not an injective encoding of all naturals or bit strings. | None. | — |
| 102 | note | `ElGamal.lean:471` · `egGenParts`, `egGenCoins`, `egGenRaw` | `egGenParts` forms both keys from the sampled square h and exponent a. `egGenCoins` budgets the instance tape and two n²-bit blocks. `egGenRaw` splits that tape and evaluates the parts. | The original generator component is intentionally ignored; p and q are retained. The scheme samples h including identity, and the security comparison pays for it. | None. | — |
| 103 | note | `ElGamal.lean:515` · `polyTimeComputable_egGenRaw` | True under ArithmeticFP; the supplied fields suffice. | Run the generator on a polynomial-size layout; use `H.sub` for p−1, `H.size` for bit lengths, `H.le` and bounded loops for sampling, and `H.modExp` for squares and powers. Padding and pairing are polynomial. The fill must preserve the total raw function off honest layouts; this is routine arithmetic/width bookkeeping, not a missing cryptographic or arithmetic assumption. | None. | a |
| 104 | note | `ElGamal.lean:520` · `egGen` | This packages the raw key generator as a uniform NUPPT with the stated independent coin blocks. | The statement matches its docstring. | None. | — |
| 105 | note | `ElGamal.lean:525` · `egGen_runAt` | The activation equation correctly recovers the p/q fields and the two independent sampled segments. | The statement matches its docstring. | None. | — |
| 106 | note | `ElGamal.lean:546` · `egEncParts`, `egEncRaw`, `egEnc` | `egEncParts` produces `(h^b,A^b·egCanon(m))` modulo p with rejection-sampled b. `egEncRaw` parses the standard activation layout. `egEnc` packages it as a uniform machine with n² coins. | The statement matches its docstring. | None. | — |
| 107 | note | `ElGamal.lean:565` · `polyTimeComputable_egEncRaw` | True as a total polynomial-time function under ArithmeticFP. | Comparison, membership by modular exponentiation, canonicalisation, multiplication and modular reduction use the named fields. On zero modulus the final n-bit truncation can be computed by exponentiation modulo `2^n`, rather than materializing an exponential-size integer; arbitrary input widths must be respected. Thus no extra field is required by the raw-input cases either. | None. | a |
| 108 | note | `ElGamal.lean:573` · `egEnc_runAt` | The activation equation correctly identifies the ciphertext function on any supplied public key and message. | The statement matches its docstring. | None. | — |
| 109 | note | `ElGamal.lean:584` · `egDecStr` | Parse the secret exponent and modulus, compute `c₁^a`, take its modular inverse, multiply by c₂, and reduce modulo p. | The second component of xgcdStr is the inverse, and the second component of divModStr is the remainder; the projection nesting selects the intended values. | None. | — |
| 110 | note | `ElGamal.lean:596` · `polyTimeComputable_of_forall_eq` | The private theorem correctly transports polynomial-time computability along function equality. | The statement matches its docstring. | None. | — |
| 111 | note | `ElGamal.lean:606` · `polyTimeComputable_egDecStr` | The polynomial-time assertion is exactly the composition of modular exponentiation, inverse, multiplication and remainder from ArithmeticFP. | The statement matches its docstring. | None. | — |
| 112 | note | `ElGamal.lean:626` · `egDecStr_apply` | True for every positive parsed modulus, not only primes and valid ciphertexts. | The modular-power result and its ZMod inverse both fit the modulus numeral width. Multiplication uses the sum of operand widths, so it loses no bits; the final remainder has the stated width. No coprimality assumption is needed for this equation, because it describes ZMod.inv even when it is not a multiplicative inverse. | None. | a |
| 113 | note | `ElGamal.lean:640` · `elGamal` | This packages the three specified algorithms as a GroupPKScheme. | Correctness and security remain separate theorems; this definition does not claim a reversible arbitrary-bit-string message encoding. | None. | — |
| 114 | note | `ElGamal.lean:662` · `elGamal_correct` | True for every valid group message and every key/encryption tape at n≥G.n₀; narrower than all-parameter, arbitrary-bit-string correctness. | Honest g is a nonzero unit, so h=g² is a unit even when h=1. For all sampled a,b, `(h^a)^b·m·((h^b)^a)⁻¹=m`. The membership hypothesis implies m<p<2^n, so writing and decoding the n-bit numeral is exact. The admitted statement needs no full-length or DDH hypothesis. Its finite-prefix and message-space limits must remain visible. | None. | b |
| 115 | note | `ElGamal.lean:675` · `egSquareGen` | Return g² mod p unless it is 1, in which case return 4. | The statement matches its docstring. | None. | — |
| 116 | note | `ElGamal.lean:687` · `egSquareGen_valid` | For any unit represented by `0<g<p`, this is a nonidentity square of order q and lies strictly between zero and p. | The fallback is valid even at p=5: 4 is the square of the unit 2 and is not 1. The primality and safe-prime hypotheses are sufficient. | None. | — |
| 117 | note | `ElGamal.lean:729` · `egGroupParts`, `egGroupGenRaw`, `egGroupGenMachine` | `egGroupParts` replaces the generator field by the repaired square while retaining p,q. `egGroupGenRaw` samples the extra unit from its own block. `egGroupGenMachine` packages the resulting function with `G.coins+n²` coins. | The statement matches its docstring. | None. | — |
| 118 | note | `ElGamal.lean:746` · `polyTimeComputable_egGroupGenRaw` | True under the existing arithmetic fields. | It uses the same generator/bit-length/rejection arithmetic as egGenRaw, followed by a modular square, equality test and constant fallback. No search for primitive roots or factorization of p−1 is being assumed. | None. | a |
| 119 | note | `ElGamal.lean:755` · `egGroupGenMachine_runAt`, `exists_ofFn_eq`, `exists_take_coins` | `egGroupGenMachine_runAt` correctly exposes its activation. Private `exists_ofFn_eq` correctly represents a list of specified length as typed bits. Private `exists_take_coins` correctly identifies the first segment with a full original-generator tape. | The statement matches its docstring. | None. | — |
| 120 | note | `ElGamal.lean:790` · `egGroupGen_valid`, `egGroupGen_wellFormed` | `egGroupGen_valid` correctly obtains a safe-prime index from the repaired square. `egGroupGen_wellFormed` correctly preserves all three width-n components. | The statement matches its docstring. | None. | — |
| 121 | note | `ElGamal.lean:832` · `egGroupGen` | This is the derived safe-prime generator with the same p,q law, its own squared-unit generator field, and fallback 4. | Its generator-element law is not exactly uniform on nonidentity squares. Under ideal units its distance from that uniform law is `(q−2)/(q(q−1))≤1/q`; rejection contributes at most `2⁻ⁿ`. The theorem assumes DDH for precisely this derived law. | None. | — |
| 122 | note | `ElGamal.lean:885` · `elGamal_secure` | True for the explicit group-message scheme, assuming DDH for the derived generator and negligible short-prime probability; this is the corrected, restricted reading of the source theorem. | For each challenge bit, coupling honest keys to the derived-generator DDH experiment costs at most `η(n)=δ(n)+9·2⁻ⁿ`: the keys differ only on h=1. DDH contributes two negligible advantages. Replacing the independent third exponent in each random world by uniform costs `2·2⁻ⁿ` in total, after which multiplication by either selected group message preserves the uniform group law, even for key-dependent selectors. Thus the challenge advantage is at most `2η+ε₀+ε₁+2·2⁻ⁿ` above the threshold and at most 1 below it. All terms are negligible after finite-prefix adjustment; the proof uses only the supplied arithmetic fields. | None. | b |
| 123 | note | `Concrete.lean:107` · `uprob_and_eq_mul_subtype`, `one_sub_div_le_uprob_subtype` | `uprob_and_eq_mul_subtype` correctly gives the conditioning product identity, including empty events. `one_sub_div_le_uprob_subtype` correctly gives `1−(1−Pr[S])/δ` when `Pr[E]≥δ>0`. | The positive lower bound itself ensures a nonempty ambient/event space, so no extra nonemptiness hypothesis is missing. | None. | — |
| 124 | note | `Concrete.lean:155` · `uprob_le_uprob_subtype_add`, `uprob_subtype_prod_eq`, `uprob_diag` | `uprob_le_uprob_subtype_add` correctly pays the complement mass when dropping conditioning. `uprob_subtype_prod_eq` correctly rearranges conditioning on the first coordinate. `uprob_diag` correctly gives reciprocal cardinality on a nonempty finite type. | The statement matches its docstring. | None. | — |
| 125 | note | `Concrete.lean:215` · `invProb_prodFun_le_plant` | The planting bound correctly splits successful product inversion into “all coordinates outside G” and a union of successful planted good coordinates. | The factor m accounts for choosing a uniform position. Nonempty α and ρ are present; m=0 gives the harmless upper bound 1. This is the declared uniform-position version, rather than the source’s first-prime-position algorithm. | None. | — |
| 126 | note | `Concrete.lean:269` · `one_sub_one_div_pow_le_exp_neg`, `claim_36_2`, `exp_neg_le_half_pow`, `claim_36_2_half_pow` | `one_sub_one_div_pow_le_exp_neg` correctly bounds the failure tail for positive a. `claim_36_2` correctly specializes a=4n² and k=n for positive n. `exp_neg_le_half_pow` correctly compares the two exponentials. `claim_36_2_half_pow` correctly composes those bounds. | Claim 36.2 is the scalar inequality from book p.36; prime-pair probability also needs the separately stated density lemma. No assertion that n=1 contains primes is inferred from the scalar formula. | None. | — |
| 127 | note | `Concrete.lean:316` · `one_div_le_uprob_prime_pair_bits` | The stated density bound is the prime-counting bound transported to two independent uniform n-bit strings, for n≥2. | It uses primes below 2^n, including shorter binary representations, in accordance with the campaign’s declared convention. | None. | — |
| 128 | note | `Concrete.lean:326` · `primesPairEquiv` | Read both bit strings and identify the prime-pair subtype with the product of the two prime subtypes. | The statement matches its docstring. | None. | — |
| 129 | note | `Concrete.lean:333` · `primesPairEquiv_apply_val`, `one_div_card_primes_le` | `primesPairEquiv_apply_val` correctly identifies both values. `one_div_card_primes_le` correctly bounds diagonal probability by `2n/2^n` for n≥2. | The statement matches its docstring. | None. | — |
| 130 | note | `Concrete.lean:360` · `DistinctPrimes`, `p`, `q` | `DistinctPrimes n` is the subtype of two distinct primes below 2^n. Its p and q definitions are the two natural-number projections. | The statement matches its docstring. | None. | — |
| 131 | note | `Concrete.lean:373` · `p_prime`, `q_prime`, `p_lt`, `q_lt`, `p_ne_q` | `p_prime` and `q_prime` correctly expose the two prime hypotheses. `p_lt` and `q_lt` correctly expose their strict numeral bounds. `p_ne_q` correctly exposes distinctness. | The statement matches its docstring. | None. | — |
| 132 | note | `Concrete.lean:388` · `mul_lt`, `totient_mul`, `one_lt_totient` | `mul_lt` correctly bounds pq by `2^(2n)`. `totient_mul` correctly gives `(p−1)(q−1)` for distinct primes. `one_lt_totient` correctly gives at least 2, including the pair 2,3. | The statement matches its docstring. | None. | — |
| 133 | note | `Concrete.lean:426` · `ext`, `isEmpty_of_lt` | `ext` correctly determines the subtype element from its two values. `isEmpty_of_lt` correctly excludes distinct prime pairs when n<2. | The statement matches its docstring. | None. | — |
| 134 | note | `Concrete.lean:444` · `default` | For n≥2 this is exactly the allowed prime pair (2,3). | The statement matches its docstring. | None. | — |
| 135 | note | `Concrete.lean:456` · `decodeDistinctPrimes`, `encodeDistinctPrimes` | `decodeDistinctPrimes` accepts paired width-m numerals only when both are distinct primes. `encodeDistinctPrimes` writes those two values at width m. | The nonempty first component of a successful decoding ensures that the total pair projections came from an actual encoded pair. | None. | — |
| 136 | note | `Concrete.lean:469` · `decodeDistinctPrimes_encode`, `encodeDistinctPrimes_of_decode` | `decodeDistinctPrimes_encode` correctly gives the decoding left inverse. `encodeDistinctPrimes_of_decode` correctly gives canonicity of every accepted string. | This checks the other advertised gate-03b repair without reopening its already repaired issue. | None. | — |
| 137 | note | `Concrete.lean:517` · `rejectBlocksL` | Read T prefixes of length k with stride B, return the first number satisfying E, or none. | No independence is built into this raw definition; k≤B and a full uniform tape are needed by the statistical lemma. | None. | — |
| 138 | note | `Concrete.lean:524` · `rejectBlocksL_spec` | Every accepted value satisfies E and lies below 2^k, even for short or overlapping raw lists. | The statement matches its docstring. | None. | — |
| 139 | note | `Concrete.lean:554` · `statClose_rejectBlocksL` | True for all stated parameters, including zero trials, zero-width blocks and all-accepting predicates. | Disjoint block prefixes push uniform `T·B` bits to independent uniform k-bit numbers. Conditional on any hit, the accepted value is uniform on the E-subtype. Failure has probability `(1−Pr[E])^T`; replacing it by the supplied valid default changes distance by at most that quantity. The default also proves the target subtype nonempty. The bound is not negligible for arbitrary E,T; negligibility requires a density bound and a suitable trial count in each application. | None. | a |
| 140 | note | Typeclass instances in the four audited files | The instance declarations introduce no additional claimed cryptographic assumptions. | ExpValid decidability is classical; expOrd is nonzero by construction. constSelector coins form a singleton. The DistinctPrimes nonzero-modulus, nonzero-totient and prime Fact instances follow from its two distinct prime fields. Their mathematical contents agree with their comments. | None. | — |
| 141 | note | Inventory · Asm-52.2; Thm-52.3; Claim-53.2 | Asm-52.2 and Thm-52.3 are faithfully represented under the declared relative-generator, safe-prime and approximate-sampling conventions; Claim-53.2 is only partially packaged. | DLAssumption and dlCollection_oneWay are the corresponding assumption/theorem. expF_injective proves the safe-prime map injective; finite cardinality then implies bijection onto its generated subgroup, but no such typed safe-prime bijection or PermCollection is exported. expo_bijective is the full-unit-group variant, not that missing safe-prime packaging. Claim-53.2 is optional in DESIGN §6.2. | Retain the optional/partial status; do not describe a usable safe-prime permutation collection as already supplied. | — |
| 142 | note | Inventory · Claim-36.2; Claim-62.2 | Claim-36.2 is present as the exact tail inequality. Claim-62.2 has a faithful statement in the separately pinned Rabin file, not Concrete. | For Claim-62.2, conditional on a fixed square and root-finder coins, the hidden uniform input root is uniform on the four roots; exactly two are ± the answer whenever a valid root is returned. Hence the “different from ±x” success probability is half the root-return success probability, and the formal ≤2 inequality is valid. Empty adversary coins give zero on both sides. The source’s assertion that the adversary itself chooses four roots uniformly is unnecessary and incorrect in general. | Correct the inventory location as in finding 2; the rest of Rabin remains outside this audit. | — |
| 143 | note | Inventory · Constr-82.b | The Blum–Micali PRG is not formalized in these files. | This is explicitly deferred both in the inventory and DESIGN §6.2. A hard-core bit and a bijection between exponent and unit types alone do not provide the iterated permutation representation, seed distribution and stretch proof required for a PRG. | Keep it deferred; do not claim this pack establishes the p.82 PRG. | — |
| 144 | note | Inventory · Lem-84.1 and Lem-84.1.0, .1, .3, .4, .5; Alg-84.2; Alg-85.a | All listed components have corresponding declarations, with the explicit restrictions and sketch correction recorded above. | Lem-84.1: fullDLCollection_hardCore. Lem-84.1.0: halfStr_spec and polyTimeComputable_halfStr. Lem-84.1.1: the four group identities. Alg-84.2: dlLoop/dlBits and dlBits_pow. Alg-85.a: majOracle and its majority bound. Lem-84.1.3: uprob_trial_ge, with the corrected vote-event direction. Lem-84.1.4: shiftInverter and its bound. Lem-84.1.5: good_instances and the first-error/union-bound argument. The source errors on pp.84–86 are corrected rather than adopted. | None. | — |
| 145 | note | Inventory · Asm-105.1; NT-105.a; Alg-106.2; Claim-107.a; Thm-107.3 | All core items have faithful corrected counterparts with the declared generator and message-space scope. | The DDH definitions implement Asm-105.1 with fixed coin blocks. The cardinality, generator and squaring lemmas implement NT-105.a. The key/encryption/decryption functions and correctness theorem implement Alg-106.2 on G_q. The squaring/uniformity/identity/distance lemmas implement Claim-107.a. elGamal_secure implements the G_q version of Thm-107.3. Its conclusion is not arbitrary-bit-string encryption under Definition 102.1. | None. | — |
| 146 | note | Inventory · Claim-106.a; Claim-106.b; Def-107.b | These optional items have no corresponding formal declarations in the audited files. | DDH⇒DL is not exported. The full-unit-group DDH attack is not exported. A reversible bit-string-to-G_q encoding is not exported; egCanon is many-to-one and is not Def-107.b. All three are explicitly optional in DESIGN §6.2, so their absence is not a new core-coverage major. | Keep the distinction between the completed core and absent optional interfaces explicit. | — |
| 147 | note | ArithmeticFP dependency review | No audited statement requires a field missing from the repaired bundle. | Sampling uses comparison and unary bit length; decrements, offsets and bounded parameter calculations use sub/add/mul/divMod; membership, residuosity and p≡3 mod4 roots use modExp; inversion uses xgcd; input guards can use primality and comparisons. H.add, H.sub and H.size are already present. The restricted square-root construction avoids an unlisted general square-root algorithm. All candidate efficiency claims remain conditional on H; this audit does not discharge H. | None. | — |
| 148 | note | Previously repaired issues · G3-1, gate-03a #12, gate-03l axiom coverage, P3-1, P8-1–3 | The advertised repairs are present; none is re-reported as an unfixed semantic defect. | Both decoding-canonicity lemmas are valid; the DL imports are the three precise randomized modules; axiom coverage includes all 124 public theorem/lemma declarations in the actual scope; the finite-prefix generator is valid for Collection; DDH uses product seeds; negligible-exception full length replaces universal full length; the root-selection convention and the p.86 event reversal are correctly recorded. Finding 3 is only an overstatement in the historical explanation, not a recurrence of the DDH seed bug. | None. | — |


Notation glossary: `n` is the security parameter/numeral width; `p` is the prime modulus; `q` is the safe-prime subgroup order; `m` is a generic exponent-domain order (or the message variable where the source declaration uses that name); `G_q` is the order-q subgroup of squares; `g` is a group element/generator and `h=g²` is ElGamal’s sampled base; `i` is the encoded group index; `x,e` are exponents and `r` denotes random coins or a sampled exponent as specified locally. `U` is a uniform law, `point(0)` the point mass at zero, `λ` a rejection-failure probability, and “distance”/“TV” means total variation. `ε` is prediction advantage, `δ` a short-prime or failure bound, `s` the short-exponent window size, `T` its number of windows, `k` a bit width or loop count as in the named declaration, `ℓ` the number of majority trials, `B` a block stride, and `c` a fixed inverse-polynomial exponent. The only new bounding functions are `K(n)=16(n+1)^c+1` in finding 1 and `η(n)=δ(n)+9·2⁻ⁿ` in the ElGamal hybrid calculation. `A`, `B₀`, `M`, `D` denote the source predictor/inverter, short-window solver, message selector and distinguisher; `ρ,ρ′` are their finite coin types. “PPT” means probabilistic polynomial time and “NUPPT” permits polynomial nonuniform advice. All other identifiers are declarations or inventory labels from the audited material.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/review/gate03f1-review.md =====

# Gate 03f1: review of the auditor's findings (discrete log, its hard-core bit, El Gamal, the samplers)

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03f1-findings.md`: 148 rows (1 major, 2 minors, 145 notes) and 21 sorry verdicts (15 (a), 6 (b), 0 (c)).
- **Code:** worktree `SP/wt-g03c-fix` at `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (checked with `git rev-parse HEAD`). Line numbers below refer to that commit. `SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Since the pin.** #203, #204 and #205 have merged (head `ee6a8d02`). None touches `Candidates/{DiscreteLog, DiscreteLogHardcore, ElGamal, Concrete, Arithmetic}.lean` or the DL fill brief (`git diff 0c348ff9 HEAD`). `inventory-ch2.md` changed only in its Miller–Rabin rows (gate 03f2, F01–F02). The Claim-62.2 rows of finding 2 are unchanged. **No finding is affected by them.**
- **Downstream code read:** prong A `SP/wt-prong-a` at `2d7b5441` (`Authentication/DLHash.lean`). I grepped prongs B, C, D, D2 and S2b (`587843c7`, `9e6f08bb`, `6ea900ae`, `c6198d86`, `afe5982f`, `27ae72da`) for every declaration of this pack. Only the facade `Candidates.lean` and prong A's `DLHash.lean` mention them.
- **Source:** `blueprint/src/references/pass-shelat-2010-ch3.raw.md` (§3.4.1 pp. 84–86, §3.11 pp. 105–107) and `-ch2.raw.md`.
- **Records:** DESIGN §5 items 20–21, §8 item 3; run-3 summary P8-1 to P8-3; the inventories; `fills/dl-candidates/brief-draft.md`; gate 03f2's findings (row D148).
- **Not done.** No Lean was built or run. The finite checks were exact rational arithmetic and exhaustive enumeration in `SP/g03rev2/f1check.py`, run with `python3 -I`.

## Summary

- **Verdicts on the three findings: 3 true, 0 partly true, 0 false.**
  - #1 is true and slightly understated: the sketch has four further slips (§1.3).
  - #3 is true, but its line references are off: the text is at `ElGamal.lean:57–62` and `:295–298`, not `:49` and `:294`.
  - I spot-checked the notes, re-deriving every constant they state. None is false.
  - **I agree with all 21 sorry verdicts (15 (a), 6 (b), 0 (c)), and the counts reconcile** with `evidence/f1/admissions.txt` (21) and `axioms.log` (150 prints, 34 `sorryAx`; 124 in the four files plus 26 in `Arithmetic.lean`).
- **The most important answer: `fullDLCollection_hardCore` stays provable as stated.** Only its proof sketch is wrong (§1.2 gives the corrected one). No statement in the pack is false, unprovable, or weaker than its docstring claims. One hypothesis, `hbig`, is stronger than needed (M1).
- **Severity changes: none.**
  - #1 stays **major**. The fill brief tells workers "Each target's docstring carries its proof sketch. **Follow it, or report why it fails**" (`fills/dl-candidates/brief-draft.md`). The sketch describes a coin budget on which its own 2⁻ⁿ sampling claim is false (exhaustive counterexample below). That is "materially misleading" for the fill it gates, even though the fix is to a docstring.
  - #2 stays **minor** (records), and #3 stays **minor** (docstring).
- **Fixes, in order of importance:**
  1. **#1.** Replace the second half of `fullDLCollection_hardCore`'s sketch (`DiscreteLogHardcore.lean:561–579`) by the text in §1.4. This is a docstring change only, and it must land before the dl-b fill is issued.
  2. **M2.** `sampleBelowL m k B T` is definitionally `rejectBlocksL (· < m) k B T`. Derive `statClose_sampleBelowL` from `statClose_rejectBlocksL` (re-point its sketch and the fill brief). Otherwise dl-a fills the same lemma twice.
  3. **M3.** Drop the stale "requested shared primitive" phrases at `DiscreteLog.lean:517` and `ElGamal.lean:512–513`. `H.size` and `H.sub` are bundle fields (P7-1). Under the fill brief's "report any missing operation" rule, the phrases would trigger spurious reports.
  4. **#3.** Correct the P8-1 history at `ElGamal.lean:57–62` and `:295–298`, aligning it with DESIGN §5 item 20.
  5. **M1.** Change "Needed"/"must have" for `hbig` at `DiscreteLog.lean:51–52, :319–321` and `ElGamal.lean:845–847` to "used". The hypothesis is dispensable in both headline theorems.
  6. **#2.** Records: move Claim-62.2 to `Rabin.lean · rabin_symmetry` in `inventory-ch2.md:194, 445, 517`.
  7. **M4.** Records: the pack's interface-use note under-lists what ch. 5–8 uses (prong A's `DLHash.lean`).
- **Rulings needed: none.** Every recommended fix is a docstring or records change, with no statement or interface change and no debt. One *optional* ruling, R-03f1-1 (drop `hbig` from the two headline theorems, M1), is set out in §M1. Under the recommended option A it is not needed.
- **Ripple:**
  - No other gate-03 pack is affected.
  - In ch. 5–8, prong A's `DLHash.lean` uses `ExpGroupGen`, `ExpGroupGen.DLHard`, `ExpValid`, `dlM`, `dlP`, `expGenFun`, `expSampleRaw`, `expEval`, `expF_injective` and `statClose_sampleBelowL`. None of the fixes changes any of them. M2 adds a lemma and keeps `sampleBelowL`'s definition.
  - `Checks.lean`: no change.

---

## 1. Finding #1 (major): the random-tape and statistical-error calculation in `fullDLCollection_hardCore`'s sketch

### 1.1 Verdict: **true**. Severity: **major (agree)**.

**What the sketch says** (`DiscreteLogHardcore.lean:562–579`):
- `s := ⌊ε(p−1)/4⌋`, `T := ⌈(p−1)/s⌉ ≤ 8n^c + 1`, `k := n`, `ℓ := 4n·(2n^c)² = 16n^{2c+1}`, with `ε = n^{-c}/2`.
- Coins `T·n + n·ℓ·(2n + A.coins)`.
- "samples `t` and the `r_{j,i}` by rejection (`sampleBelowL` with `H.le`; the statistical term `n·ℓ·(1/2)^n + (1/2)^n` by `statClose_rejectionSample`/`StatClose.prod` …)".
- Conclusion: `G.dlProb B n ≥ 3ε/(8(8n^c+1)) − 2n^{2c+2}(1/2)^n`.

**Each of the auditor's three claims checks:**
1. **A `2n`-bit block cannot carry a rejection sample within 2⁻ⁿ of uniform.**
   - The only closeness lemma for `sampleBelowL` is `statClose_sampleBelowL` (`DiscreteLog.lean:499–502`). It is for `sampleBelowL m (Nat.size m) n n` on `Fin (n * n) → Bool`, that is n trials of n-bit blocks, n² coins.
   - On `2n` coins the third block is `drop (2n) r = []`, and `listToNat [] = 0 < m`, so after two rejections the sampler outputs 0.
   - I enumerated all 2²⁰ tapes for `p = 523` (prime, `523 ≡ 3 mod 4`, `2⁹ ≤ 523 < 2¹⁰`), `n = 10`, `m = 522`, `k = Nat.size 522 = 10`.
     - The distance from uniform on `[0, 522)` is exactly **32823521/136839168 ≈ 0.23987**. This is `(1 − 522/1024)²(1 − 1/522)`, the auditor's value.
     - The claimed bound is `2⁻¹⁰ ≈ 0.00098`.
     - With n² = 100 coins the same formula gives `(502/1024)¹⁰(521/522) ≈ 0.00080 ≤ 2⁻¹⁰`, as `statClose_sampleBelowL` says.
   - Rejection over a single block cannot reach 2⁻ⁿ either: two trials of n bits fail with probability up to 1/4.
2. **The final coefficient is wrong.** With the sketch's own `ℓ = 16n^{2c+1}`, the statistical term it names is `nℓ·2⁻ⁿ + 2⁻ⁿ = (16n^{2c+2} + 1)2⁻ⁿ`, not `2n^{2c+2}2⁻ⁿ`. Both are negligible, so the contradiction survives, but the displayed bound is false as written.
3. **`T·n` is not a coin polynomial.** `T = ⌈(p−1)/s⌉` depends on the input's `p`, while `NUPPT` coins are a `PolyExpr` in `n`. The budget must use a bound `K(n) ≥ T`, and t must be sampled below the input-dependent `T` from a fixed-size block.

### 1.2 Is the statement still provable as stated? **Yes.**

I re-derived the whole chain against the code. The statement (`:580–582`) needs no change:
- `Collection.HardCore` (`Collections.lean:229–236`) is one-sided: `≤ 1/2 + ε(n)` for every n, averaged over `Gen`'s coins with an ideal uniform x.
- `halfPred` is exactly balanced at every valid index: `p − 1` is even, so `#{x < p−1 : 2x+2 ≤ p} = (p−1)/2`. A constant predictor therefore gets exactly 1/2. The source's inclusive `half` would be biased by `1/(p−1)`.
- The concrete lemmas, re-derived:
  - **`uprob_trial_ge`.** The disagreement sets have sizes `2e` and `2d`, both `< 2s`, and `4s ≤ ε(p−1)` gives a loss of at most `ε/2`.
  - **`uprob_majOracle_ne_le`.** `HardcoreBit.majority` sends ties to `false` (`PairwiseIndependence.lean:235`). A wrong majority forces at most ℓ/2 correct votes. Chebyshev then gives `(ℓ/4)/(ℓε/2)² = 1/(ε²ℓ)`.
  - **`invProb_shiftInverter_ge`.** `invProb` is the preimage form, `Experiments.lean:60`. The guess `t = ⌊e/s⌋ < T` has probability `1/T`. An empty coin type gives `δ ≥ 1`.
  - **`invProb_dlInverter_ge`.** Use a union bound over the k rounds at the *perfect-path* queries `±g^{⌊e_j/2⌋}`. These lie in the two windows, because `ε ≤ 1/2` forces `s ≤ (p−1)/8`. Off the union, the noisy path equals the perfect path, so `dlLoop_eq_dlBits` applies.
  - **`dlBits_pow`.** For even e the kept root is `g^{e/2}`, because the other root `g^{e/2+(p−1)/2}` has `2·val ≥ p−1`. For odd e use `g^{e−1}`. The base case is k = 0, e = 0.
- The asymptotic wrapper works with the parameters of §1.4. All the arithmetic it needs is in `ArithmeticFP`: `sub`, `add`, `divMod`, `le`, `modExp`, `xgcd`, `mul`. The loops it needs are in the closure calculus: `polyTimeComputable_iterateFind`, `_iterateEmit`, `_majority`, `NUPPT.polyTimeComputable_layout`.

### 1.3 What the auditor did not say (further slips in the same sketch)

1. `:561`: "`A_i y ρ := A.distinguisherL n ⟨i, encD y⟩ ρ`" is a type slip. `encD` encodes domain elements of `Z_{expOrd i}`, and `y` is a unit. The predictor sees `f_i(x)`, so it should be `A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
2. `:570`: `statClose_rejectionSample` is the typed sampler on `Fin T → Fin k → Bool`. The string sampler the machine runs is covered by `statClose_sampleBelowL`, which this fill then depends on (fill order: dl-a first).
3. `:563`: "`T ≤ 8n^c + 1`" needs `p − 1 ≥ 8n^c(8n^c + 1)`, not only the stated `p − 1 ≥ 8n^c`.
   - With `x = (p−1)/(8n^c)` and `s = ⌊x⌋ ≥ x − 1`, `(p−1)/s ≤ 8n^c/(1 − 8n^c/(p−1))`.
   - This is true for large n on full-length p, but the sketch should say so, or use a cruder bound.
   - My bound: if `x ≥ 2` then `s ≥ x/2`, so `T ≤ 16n^c`. The auditor's `K(n) = 16(n+1)^c + 1` is looser and also correct.
4. `:568`: "computes `s` and `T` from `1^n` and `p` (`H.divMod`, `H.mul`)" needs the binary numeral of `8n^c`.
   - Neither the bundle nor the candidates' closure calculus converts unary to binary. `H.size` goes the other way.
   - Two routes exist:
     - put the n-bit numeral of `8n^c` in B's advice (B is non-uniform, and `DLHard` quantifies over every `NUPPT`);
     - or build it from main's `countLoop` (`ClassP/BinaryArith/PrimeFind.lean:144`, `Nat.bits |z|`) and `polyTimeComputable_reverse` (`BinaryArith/Mul.lean:73`), with a glue lemma between the two numeral conventions.
   - The advice route is cheaper. This is not a missing bundle field, because the statement does not need one.

### 1.4 Concrete fix: the corrected sketch (replace from "Apply `invProb_dlInverter_ge` …" at `:562` to the end of the docstring at `:579`; also fix `:561`)

```text
success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
Apply `invProb_dlInverter_ge` with `ε := n^{-c}/2`, `s := ⌊(p−1)/(8n^c)⌋` (so `4s ≤ ε(p−1)`),
`T := ⌈(p−1)/s⌉` (so `Ts ≥ p − 1`), `k := n` (`s ≤ p − 1 < 2^n`) and `ℓ := 16 n^{2c+1}`
(so `k/(ε²ℓ) = 1/4`). For large `n` the good instances have `p − 1 ≥ 2^{n−1} − 1 ≥ 16 n^c`, so
`(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16 n^c) ≥ 1` and `T ≤ K(n) := 16 n^c < 2^n`; the inverter then
succeeds with probability `≥ (3/4)/T ≥ 3/(4K(n))` on each good instance, with ideal coins.
The machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, ⟦8n^c⟧_n⟩`
(the `n`-bit numeral of `8n^c`: the bundle has no unary-to-binary conversion); coins
`n·n + n·ℓ·(n·n + A.coins)` (a `PolyExpr`, `c` being fixed): one block of `n·n` coins for `t`
and, for each of the `n·ℓ` trials, a block of `n·n` coins for `r_{j,i}` and `A.coins` coins for
`ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`; computes `s` and `T` (`H.sub`,
`H.divMod`, `H.add`); outputs `0^n` unless `1 ≤ s` and `T < 2^n` (the analysis uses only the good
instances); samples `t := (sampleBelowL T (Nat.size T) n n ·).getD 0` and
`r_{j,i} := (sampleBelowL (p−1) (Nat.size (p−1)) n n ·).getD 0` (`H.le`, `H.size`,
`polyTimeComputable_iterateFind`); shifts `y · g^{−ts}` (`H.modExp`, `H.xgcd`); and runs the `n`
rounds of `dlLoop` (`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`, D11):
quadratic residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by
`H.modExp` (`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
`⟨⟨⟨1^n, ⟨i, z_{j,i}⟩⟩, A.advice n⟩, ρ_{j,i}⟩` (`polyTimeComputable_iterateEmit`,
`NUPPT.polyTimeComputable_layout`), the comparison with `half(r_{j,i})` (`halfStr`), the majority
(`polyTimeComputable_majority`), the negation `p − z` and the bit assembly; finally
`(bits + ts) mod (p−1)` as an `n`-bit numeral (`decodeFin n` reads it back,
`bitsToNat_natToBits`). Sampling: each of the `1 + nℓ` sampled coordinates is within `(1/2)^n`
of uniform (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`); the coins of `A`
are exact; `StatClose.prod` and `StatClose.abs_uprob_sub_le_prod` give a loss of at most
`(1 + 16 n^{2c+2})(1/2)^n` at every instance. Averaging over the good set (probability
`≥ ε/2`, `HardcoreBit.uprob_mul_le_uexp`):
`G.dlProb B n ≥ (ε/2)·3/(4K(n)) − (1 + 16 n^{2c+2})(1/2)^n = 3/(256 n^{2c}) − (1 + 16 n^{2c+2})(1/2)^n`
for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`.
```

**Alternative (not recommended).** Keep `2n`-bit exponent blocks and reduce modulo `p − 1`. The distance is `r(m−r)/(2^{2n}m) ≤ m/2^{2n+2} < 2⁻ⁿ/4` (`r = 2^{2n} mod m`; ≈ 8.9·10⁻⁵ for the example above). This needs a new sampling lemma that the library lacks, and the machine would differ from `expSampleRaw`'s sampler.

**Ripple.**
- `DiscreteLogHardcore.lean` docstring only. No statement, `Checks.lean` or other-pack change.
- In ch. 5–8 nothing changes: no prong cites `fullDLCollection_hardCore` (grep, all prong worktrees).
- The dl-b fill brief must be issued after this fix. It should cite `statClose_sampleBelowL` as a dependency, which makes dl-a's sampler lemma a prerequisite of dl-b's headline.

---

## 2. Finding #2 (minor): Claim-62.2's location

### Verdict: **true**. Severity: **minor (agree)**.

- `inventory-ch2.md` gives `Concrete.lean` in three places:
  - `:194`, the row's location column;
  - `:445`, "New concrete lemma in `Candidates/Concrete.lean`";
  - `:517`, item C6 under "§4 New concrete-layer lemmas … put these in `Concrete.lean` unless noted".
- The lemma is `Candidates/Rabin.lean:198`, `rabin_symmetry`, at the pin and at head. `Concrete.lean` has no Claim-62.2 statement.
- DESIGN §6 (`DESIGN.md:1142`) already assigns Claim-62.2 to Cand2 (RSA/Rabin).
- 03f1's pack lists Claim-62.2 in its source list (`03f1-pack.md:23`) and in its inventory scope (`:57`), so it was mis-scoped to this pack.
- **The coverage gap the auditor raises does not exist.** Gate 03f2, whose scope includes `Rabin.lean`, audited it (`gate03f2-findings.md` row D148, a note: faithful). 03f2 closed at 0 majors.

**Fix (records).**
- `inventory-ch2.md:194`: change the location to `Cryptography/Candidates/Rabin.lean` (`rabin_symmetry`).
- `inventory-ch2.md:445`: replace "New concrete lemma in `Candidates/Concrete.lean`" by "In `Candidates/Rabin.lean` (`rabin_symmetry`)".
- `inventory-ch2.md:517`: "C6 Claim-62.2 (Rabin symmetry lemma), in `Candidates/Rabin.lean`".
- In `resolutions-03f1-r1.md`, record that the item belongs to 03f2 (D148).

**Ripple:** none.

---

## 3. Finding #3 (minor): the P8-1 history overstates when the old definitions made DDH false

### Verdict: **true**. Severity: **minor (agree)**. The line references are wrong: use `ElGamal.lean:57–62` and `:295–298`.

**Check.**
- On the old seed `Σ r, Z_{q_r}^k` (k = 2 or 3), the coin string r has weight `q_r^k / Σ q^k`.
  - **Constant q:** both weights are `2^{-|r|}`, so the instance laws coincide. "false for every randomized generator" (`:61–62`) is therefore false.
  - **q varying on a negligible set** (say one coin string `r₀` out of `2^{L(n)}`): both laws put mass at most `2/(2^L − 1)` off the common value, so they are negligibly close. "false for every generator whose `q` varies with the coins" (`:298`) is therefore false too.
  - **Non-negligible variation:** two same-length orders `q`, `3q/2` on half the coins each give the instance laws `(4/13, 9/13)` and `(8/35, 27/35)`, at distance `36/455`. Here the threshold test works.
- DESIGN §5 item 20 already words this correctly: "uniform-on-Σ tilts the instance law by the fibre sizes".
- The repair (product seeds) is right and must stay.

**Fix (docstrings).**
- `ElGamal.lean:59–62`. Replace "— the two ensembles then had different instance laws whenever `q` varies with the coins, and the threshold test `[q ≥ θ_n]` distinguished them with constant advantage, so `DDHAssumption` was false for every randomized generator." by:

  > — so the two ensembles could have different instance laws, and when `q` varies non-negligibly with the coins (two orders `q`, `3q/2` on half the coins each give the laws `(4/13, 9/13)` and `(8/35, 27/35)`) a threshold test `[q ≥ θ_n]` distinguished them, making `DDHAssumption` false for reasons unrelated to DDH.

- `ElGamal.lean:297–298`. Replace "making `DDHAssumption` false for every generator whose `q` varies with the coins." by "which could make `DDHAssumption` false for reasons unrelated to DDH (DESIGN §5 item 20)."

**Ripple:** none.

---

## 4. The 21 admitted declarations (verdict of the auditor → mine)

| File · declaration | Auditor | Mine | Reason (re-derived) |
|---|---|---|---|
| `DiscreteLog` `statClose_sampleBelowL` :499 | a | a | Law `(1−λ)U + λδ₀`, `λ = (1−m/2^k)^n ≤ 2⁻ⁿ` (`2^{k−1} ≤ m`), exact distance `λ(1−1/m)`. Also a corollary of `statClose_rejectBlocksL` (M2). |
| `polyTimeComputable_expSampleRaw` :522 | a | a | A total function. Bit length by `H.size` (stale wording, M3), comparisons by `H.le`, `iterateFind`, padding. |
| `expSampler_spec` :549 | a | a | Valid at every n (`G.valid`/`hV` from `n₀` on, `expValid_dlDefaultIndex` below). `v < m < p < 2^{dlW}` decodes canonically. |
| `expCollection_sampleClose` :618 | b | b | `δ = 1` below `n₀`, `2⁻ⁿ` above. True. D10 sampling relaxation (declared). |
| `expCollection_invProbAt_le` :635 | a | a | `expF_injective` plus canonical `expDec` give width n and value `x.val`. `decodeFin`/`bitsToNat_eq_listToNat` share the MSB-first convention (`Primality.lean:660`). |
| `expCollection_oneWay` :647 | b | b | Follows from the previous two. D10. |
| `DiscreteLogHardcore` `dlBits_pow` :319 | b | b | True (§1.2). Restricted to `p ≡ 3 (mod 4)` (declared, DESIGN §8 item 3). |
| `uprob_trial_ge` :357 | a | a | §1.2. `p = 2` and empty `ρ` make the hypotheses infeasible. |
| `uprob_majOracle_ne_le` :380 | a | a | §1.2 (ties to `false`, Chebyshev). |
| `invProb_shiftInverter_ge` :408 | a | a | §1.2. |
| `invProb_dlInverter_ge` :435 | a | a | §1.2 (perfect-path union bound). |
| `polyTimeComputable_halfStr` :526 | a | a | `2x+2 ≤ p ⟺ x < ⌊p/2⌋`: `H.divMod`, `H.le`, negation. |
| `fullDLCollection_hardCore` :580 | b | b | Provable as stated (§1.2). Narrower than the source by `p ≡ 3 (mod 4)` and D10. Its sketch is wrong (#1). `hbig` is avoidable (M1). |
| `ElGamal` `statClose_sq_generator` :220 | a | a | TV(uniform on `G_q`, uniform on `G_q∖{1}`) is exactly `1/q`, attained at `{1}`. `q ≥ 2` keeps the subtype nonempty. |
| `polyTimeComputable_egGenRaw` :515 | a | a | Total function. On `p ∈ {0, 1}` the sampler falls back to `g = 1`. Stale wording, M3. |
| `polyTimeComputable_egEncRaw` :565 | a | a | Total function. On `p = 0` the n-bit truncation is `modExp` modulo `2^n` (the auditor's point holds). |
| `egDecStr_apply` :626 | a | a | `xgcdStr`'s inverse has width `|p|`, `mulStr` is lossless and `divModStr`'s remainder has width `|p|`. True for `p > 0` without coprimality. |
| `elGamal_correct` :662 | b | b | `h = g² mod p` is a unit even when `h = 1`, so `h^{ab}m(h^{ab})⁻¹ = m`. `m = 1` (the `egCanon` fallback) is covered, and `n ≥ n₀` forces `2^n > p ≥ 5`. |
| `polyTimeComputable_egGroupGenRaw` :746 | a | a | As `egGenRaw`, plus one test and a constant. |
| `elGamal_secure` :885 | b | b | Re-derived: hybrid-1 gap `η = δ + 9·2⁻ⁿ` (`1/q ≤ 8·2⁻ⁿ` for full-length p and n ≥ 2, plus `2⁻ⁿ` for `egUnit`). Total `2η + ε₀ + ε₁ + 2·2⁻ⁿ`. DDH is assumed for the derived generator (declared). `hbig` is avoidable (M1). |
| `Concrete` `statClose_rejectBlocksL` :554 | a | a | True for all parameters, including `T = 0` (bound 1) and `k = 0`. |

**Pack question: does any statement need a field the bundle lacks? No.**
- The candidate that looks like one is the binary numeral of `n^c` in `fullDLCollection_hardCore`'s machine (§1.3 item 4).
- It is a fill-level need, met by advice. It is not a statement need.

---

## Missed by the auditor

### M1 (minor, docstring; optional statement strengthening): `hbig` is dispensable in both headline theorems, but the docstrings call it "needed"

**The claims in the docstrings:**
- `DiscreteLog.lean:51–52`: "the prime must have full length `2^{n−1} ≤ p`".
- `:319–321`: "Needed, with `Negligible δ`, where the proofs divide by `q` or `p − 1`".
- `ElGamal.lean:845–847`: "`hbig` … makes the sampling term `1/q ≤ 8·2^{-n}` negligible".

**Why `hbig` is avoidable:**
- **`fullDLCollection_hardCore`.**
  - Let `B₁` invert by exhaustive search when `p − 1 < 16n^c` (at most `16n^c` calls of `H.modExp` in an `iterateFind` loop; the numeral `⟦16n^c⟧` goes in the advice).
  - Let `B₂` be the window inverter of §1.4 when `p − 1 ≥ 16n^c`.
  - On the good set (probability `≥ ε`), `dlProb B₁ + dlProb B₂ ≥ ε·3/(4K(n)) − (1+16n^{2c+2})2⁻ⁿ`. So one of them is non-negligible infinitely often, contradicting `hDL`.
  - Nothing uses full length.
- **`elGamal_secure`.**
  - Suppose `E_r[1/q_r] ≥ n^{-c}` infinitely often. Then `Pr[q ≤ 2n^c] ≥ n^{-c}`, because `1/q ≤ 1/2` always.
  - The DDH distinguisher that, when `q ≤ 2n^c`, finds `a` by search from `A = h^a` and accepts iff `Z = B^a` has advantage `≥ n^{-c}/2 − 2⁻ⁿ` against `egGroupGen H G`. This contradicts `hDDH`.
  - Hence `Pr[g² ≡ 1] ≤ E[1/q] + 2⁻ⁿ` is negligible without `hbig`.
- **Why it matters:** with negligible δ, `hbig` is not known to be satisfiable without an unproved safe-prime density conjecture. `FullLengthExcept`'s own docstring calls it "itself open". It is therefore a real extra assumption, and an avoidable one.
- **Not a weakening relative to the source:** [PS10]'s `Π̃_n` has full-length p by definition. So the (b) verdicts stand.

**Fix (recommended, option A; no statement change).**
- `DiscreteLog.lean:51–52`: "the prime must have full length" → "the proofs use full length".
- `:319–321`: "Needed, with `Negligible δ`, where the proofs divide by …" → "Used, with `Negligible δ`, by the proofs that divide by … (a convenience: instances with `p − 1` below a polynomial can be inverted by exhaustive search, so `hbig` could be dropped; gate 03f1 review, M1)".
- `ElGamal.lean:845–847`: likewise.

**Optional ruling R-03f1-1, only if the stronger statements are wanted.**
- **(A) Keep `hbig`, fix the docstrings (recommended).** Cost: none now. The two theorems stay conditional on an avoidable hypothesis.
- **(B) Drop `hbig` from `fullDLCollection_hardCore` and `elGamal_secure` before the fills.**
  - Cost: two statement changes; a brute-force branch in dl-b and a small-q DDH distinguisher in dl-c (each a bounded `iterateFind` search); revision of DESIGN §5 item 21 and the P8-2 record.
  - No ch. 5–8 ripple: neither theorem is cited there.
- **(C) Defer to a post-fill strengthening.** Cost: a second statement change later, and a re-audit of the two theorems then.

**Ripple:** docstrings only under A. Under B, packs 03f1 (re-audit of two statements) and the dl-b and dl-c fill briefs.

### M2 (minor, duplication): `sampleBelowL` is `rejectBlocksL (· < m)`

**Check.**
- `sampleBelowL m k B T r` (`DiscreteLog.lean:465–468`) and `rejectBlocksL E k B T r` (`Concrete.lean:517–520`) have the same body with `E := (· < m)`. The block layout is the same, `drop (t*B)` then `take k`.
- `DiscreteLog` imports `Concrete`.
- So `statClose_sampleBelowL` is `statClose_rejectBlocksL (· < m) (Nat.size m) n n (Nat.size_le …) (d := 0)`, followed by `{v : Fin (2^k) // v < m} ≃ Fin m` and `(1 − m/2^k)^n ≤ (1/2)^n`.
- `sampleBelowL_lt` likewise follows from `rejectBlocksL_spec`.
- Both lemmas are admitted, and the fill brief draft (`fills/dl-candidates/brief-draft.md:50`) says they "differ in the block layout". Following it, dl-a would fill the same lemma twice.
- `Concrete.lean:516` already notes that `sampleBelowL` "has the same shape", so this is a disclosed similarity. It is not yet a dedup.

**Fix.**
- Add `theorem sampleBelowL_eq_rejectBlocksL : sampleBelowL m k B T = rejectBlocksL (· < m) k B T := rfl`. This is a new lemma; no definition changes, so prong A's `expSampleRaw` and `DLHash` are untouched.
- Re-point `statClose_sampleBelowL`'s sketch (`:487–498`) to it plus `statClose_rejectBlocksL`.
- Fix the fill brief: dl-a fills `statClose_rejectBlocksL` first.
- Optionally add a duplication-ledger line.

**Ripple:** dl-a's order. None in ch. 5–8.

### M3 (minor, sketch staleness): "requested shared primitive(s)"

**Check.**
- `DiscreteLog.lean:517` (`polyTimeComputable_expSampleRaw`) calls `Nat.size` a "requested shared primitive". The auditor noted this one, in row 38.
- `ElGamal.lean:512–513` (`polyTimeComputable_egGenRaw`) calls "the decrement `p − 1` and the bit length `Nat.size`" "requested shared primitives". The auditor did not flag this one.
- Both are bundle fields since P7-1: `H.sub` and `H.size` (`Arithmetic.lean:252, 263`).
- The fill brief's rule "if a needed operation is missing from the bundle, report it" makes the stale words a source of spurious escalations.

**Fix.** Replace each phrase with "(`H.size`)" and "(`H.sub`, `H.size`)" respectively.

**Ripple:** none.

### M4 (note, records): ch. 5–8 uses more of this pack than the pack declares

**Check.**
- `03f1-pack.md:90–91` says the declarations cited by ch. 5–8 are `ExpGroupGen` and `DLAssumption`.
- Prong A's `Authentication/DLHash.lean` (`2d7b5441`) uses `ExpGroupGen`, `ExpGroupGen.DLHard`, `ExpValid`, `dlM`, `dlP`, `expGenFun`, `expSampleRaw`, `expEval`, `expF_injective` and `statClose_sampleBelowL`.
- `dlHash_crh` assumes full-group DL (`hV : … dlM i = dlP i − 1`, as in Lemma 84.1), not `DLAssumption`.
- None of this review's fixes changes those declarations. M2 keeps `sampleBelowL`'s definition for this reason.

**Fix.** Correct the interface list in the S1 note and the gate records, so that later repairs to these files check prong A.

**Ripple:** records only.

### Smaller corrections to the auditor's notes (no change requested)

- Row 15 (#3) and row 13 cite `ElGamal.lean:49, :294`. The text is at `:57–62` and `:295–298` (see §3).
- Row 72 (`good_instances`): the lemma's `ε/2` is weaker than what its hypotheses give (`ε/(1−ε)`). It is still correct as stated and is proved.
- Row 141 (Claim-53.2): agree. `DiscreteLog.lean:91`'s "(Claim-53.2 of the inventory, proved)" gives injectivity into strings only. Reading "permutation" as "bijection onto its image" makes it acceptable; no change needed.

---

## Proposed closing condition for gate 03f1

1. **The major's fix.** #1's corrected sketch (§1.4, with `:561`) is merged as a docstring-only change.
2. **The minors and M-items.** #3, M1 (option A), M2 (the `rfl` lemma and the sketch re-point) and M3 are merged in the same docstring PR. #2 and M4 are applied to the records.
3. **Evidence for the PR:**
   - a statement byte-identity check of every declaration in the four files against `0c348ff9`, with only docstrings changed and one new `rfl` lemma;
   - a lint run on the four files;
   - re-check of the four modules and their downstream closure (prong A not required);
   - axiom prints unchanged except for the new lemma, which must print standard.
4. **Closing round 2** (delta pack, as for 03b, 03c and 03e round 2): an external check that the new sketch is consistent (coin budget, constants, `T < 2^n`, advice numeral) and that no statement changed. The gate closes at 0 blockers and 0 majors.
5. **Fill briefs.** The dl-a and dl-b fill briefs are revised before issue:
   - the dl-a order (M2);
   - dl-b's dependency on `statClose_sampleBelowL`;
   - the advice route for `⟦8n^c⟧`.
6. **R-03f1-1** needs a user decision only if option B or C is wanted; otherwise none.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03f1-r1.md =====

# Gate 03f1 (discrete log, its hard-core bit, ElGamal): round 1 resolutions

- **Round:** findings `findings/gate03f1-findings.md`, SHA-256 `72909f86e53f745a24af86d23704e1eba2929189f6ab9497a67c504065203b4b`; pin `0c348ff9`. **0 blockers, 1 major, 2 minors**; the 21 admissions 15 (a), 6 (b), 0 (c). Review `review/gate03f1-review.md`: all true; `fullDLCollection_hardCore` provable as stated. Ruling R-03f1-1 (A): keep `hbig`.
- **Repair:** the gate 03 repair batch, PR [#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206) (head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`, merged by `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; evidence `evidence-repairs/03-batch/`), plus the records commits of 2026-11-06.

| Finding | Severity | Resolution |
|---|---|---|
| #1 | major | **Fixed** (#206, item D). `fullDLCollection_hardCore`'s sketch is replaced by the review's §1.4: `n²` coins for `t`, `n²` plus A's coins per trial, `T ≤ 16n^c`, success `≥ 3/(256 n^{2c}) − (1 + 16n^{2c+2})·2⁻ⁿ`, and the binary numeral of `8n^c` in the inverter's advice. Docstring only. |
| #2 | minor | **Fixed (records).** Claim-62.2's inventory rows point at `Rabin.lean` · `rabin_symmetry` (audited at 03f2). |
| #3 | minor | **Fixed.** `ElGamal.lean`'s history of the run-3 DDH repair (P8-1), with the review's texts. |
| M1 | (review) | **Fixed (docstrings; ruling R-03f1-1 (A)).** `hbig` is described as "used, a convenience, dispensable" at `DiscreteLog.lean` and `ElGamal.lean`; the statements keep it. |
| M2 | (review) | **Fixed.** `sampleBelowL_eq_rejectBlocksL` (`DiscreteLog.lean`), with `rejectBlocksL_eq` beside its definition (`Concrete.lean`) so that no other file's definition is unfolded. `statClose_sampleBelowL`'s sketch derives it from `statClose_rejectBlocksL`; the DL fill brief fills it as a corollary. |
| M3 | (review) | **Fixed.** The stale "requested shared primitive(s)" wording cites `H.size` and `H.sub`. |
| M4 | (review) | **Recorded.** Prong A's `DLHash.lean` also uses `expGenFun`, `expSampleRaw`, `expEval`, `ExpValid`, `dlM`, `dlP`, `DLHard`, `expF_injective` and `statClose_sampleBelowL`; no fix changes them. |
| Notes | note | No change. |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/repair.diff.txt =====

diff --git a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
index 66f802b8..c51a6ff4 100644
--- a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
@@ -38,6 +38,11 @@ inside one finite machine.
   the host: from the host seam at the module's entry state, with any output prefix, the host
   reaches the seam at the module's return state with the module's result word, forwarding exactly
   the module's output, and visits no control state meanwhile; `guard_add` chains such segments.
+* **Head envelopes.** A clean module's heads stay within its budget `B |arg|` of the origin at
+  every time (`Clean.envelope`), and the host's heads stay within `t` cells of the origin up to
+  time `t` of a call (`host_call_envelope`), hence within `B |arg|` during a clean call
+  (`host_clean_envelope`). These are the coarse envelopes from the time bounds and the unit head
+  moves of `Turing.MultiTapeTM.workTapePos_step_le` (gate 03l round 2, finding 1).
 
 ## Origin
 
@@ -62,6 +67,8 @@ machines, the control states and their table, the return map and the start state
   clean install and a clean emit module with a polynomial budget on the argument length.
 * `Turing.ModuleHost.host_call`, `host_clean` — one module call inside the host, with the guard
   that no control state is visited; `guard_add` — chaining guarded segments.
+* `Turing.ModuleHost.Clean.envelope`, `host_call_envelope`, `host_clean_envelope` — the head
+  envelopes of a clean module and of a host call.
 * `Turing.ModuleHost.first_halt`, `live_prefix` — cutting a halting run at its first halt, and
   liveness of the prefix of a live run.
 * `Turing.ModuleHost.request_budget` — a polynomial budget on a bounded request fits a common
@@ -213,6 +220,44 @@ theorem clean_iff (M : FinTM Bool) (result emit : List Bool → List Bool) (B :
           state := none, output := emit arg} :=
   Iff.rfl
 
+/-- **The head envelope of a clean module** (H14's space clause): if `Clean M result emit B`,
+then for every native input `x` and argument `arg`, at every time `v` of the run of `M` from the
+seam at its start state holding `arg` (before, at and after its first halt), every work head is
+within `B |arg|` cells of the origin, where all heads start (`Cfg.ofWords_workTapePos`).
+
+This is the coarse envelope from the time bound: one step moves each head by at most one cell
+(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
+`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`), the first halt comes at a time `t ≤ B |arg|`,
+and the run is constant from `t` on. The contract gives nothing sharper: it fixes the terminal
+seam, not the intermediate head positions, and a clean module may move a head out and back
+before it halts at the seam (gate 03l round 2, finding 1).
+
+**Proof sketch.** Take the first halt `t ≤ B |arg|` of `Clean`. At a time `v ≤ t` each head is
+within `v` cells of its start (`MultiTapeTM.workTapePos_runFrom_mem_Icc`); at `v > t` the run
+is halted, so its configuration is the one at `t` (`MultiTapeTM.runFrom_add`,
+`MultiTapeTM.runFrom_of_halt`). -/
+theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ}
+    (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
+    |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
+      (B arg.length : ℤ) := by
+  obtain ⟨t, -, htB, -, hend⟩ := ((clean_iff M result emit B).1 h).2 x arg
+  have hhalt : (M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t).state =
+      none := by
+    rw [hend]
+  obtain ⟨u, hut, hu⟩ : ∃ u ≤ t,
+      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v =
+        M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u := by
+    rcases le_total v t with hvt | htv
+    · exact ⟨v, hvt, rfl⟩
+    · refine ⟨t, le_rfl, ?_⟩
+      rw [← Nat.add_sub_of_le htv, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
+  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (M.tm.workTapePos_runFrom_mem_Icc
+    (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u j)
+  rw [Cfg.ofWords_workTapePos] at h1 h2
+  have hB : (u : ℤ) ≤ B arg.length := by exact_mod_cast hut.trans htB
+  rw [hu, abs_le]
+  constructor <;> omega
+
 /-- Turn a clean-call bridge contract into the uniform first-halting form.
 
 **Proof sketch.** The release wrapper stops one step after the positive exit (`stop_clean`);
@@ -503,6 +548,42 @@ theorem host_call {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n 
   · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
     exact host_seam M K ret i hp x result pre out q none
 
+/-- **The head envelope of a host call** (H14's space clause for one call, inclusive of its
+endpoint): run from its seam at the entry state of module `i` holding `arg` with output prefix
+`pre`, the host has, at every time `v ≤ t`, every work head within `t` cells of the origin,
+where all heads start (`Cfg.ofWords_workTapePos`). Under the hypotheses of `host_call`, `t` is
+the duration of the call, so this bounds the heads throughout the call.
+
+This is the coarse envelope from the time bound: one step moves each head by at most one cell
+(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
+`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`). A sharper envelope follows from the proof of
+`host_call` and is not stated here: before the return, the host's tape `j` is module `i`'s
+tape `j` for `j < (M i).k` (the padded module runs in lockstep and the forwarding keeps every
+physical field, `Turing.emit_run`), and every other tape stays blank with its head at the
+origin, so the host's heads obey any head envelope of the module.
+
+**Proof sketch.** `MultiTapeTM.workTapePos_runFrom_mem_Icc` from the host seam, whose heads are
+at the origin, and `v ≤ t`. -/
+theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) :
+    ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
+      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos
+        j| ≤ (t : ℤ) := by
+  intro v hv j
+  have key : ∀ c : Cfg K Bool (State C M) x, c.workTapePos j = 0 →
+      |((hostTM M K hk ctrl ret q₀).tm.runFrom c v).workTapePos j| ≤ (t : ℤ) := by
+    intro c hc
+    obtain ⟨h1, h2⟩ :=
+      Finset.mem_Icc.1 ((hostTM M K hk ctrl ret q₀).tm.workTapePos_runFrom_mem_Icc c v j)
+    rw [hc] at h1 h2
+    have hvt : (v : ℤ) ≤ t := by exact_mod_cast hv
+    rw [abs_le]
+    constructor <;> omega
+  exact key {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
+    (Cfg.ofWords_workTapePos (input := x) (entry (C := C) M i) (stateWord K arg) j)
+
 /-- **Chaining guarded segments.** If the run from `c` avoids the state `anchor` before time `a`
 and is at `d` at time `a`, and the run from `d` avoids `anchor` before time `b`, then the run
 from `c` avoids `anchor` before time `a + b`. -/
@@ -545,4 +626,38 @@ theorem host_clean {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n 
     host_call M K hk ctrl ret q₀ i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
   exact ⟨t, hp, ht, hguard, hend⟩
 
+/-- **A clean module call inside the host, with its head envelope** (the bounded call of
+`host_clean` together with H14's space clause): if module `i` is `Clean` with result map `f`,
+emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
+prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
+output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
+`ret i` holding `f arg`, with output `pre ++ g arg`, visits no control state before `t`, and at
+every time `v ≤ t` has every work head within `B |arg|` cells of the origin.
+
+The envelope is the coarse one from the time bound (`host_call_envelope`, which also describes
+the sharper envelope inherited from the module).
+
+**Proof sketch.** `host_clean` gives `t` and the call; `host_call_envelope` at `t`, with
+`t ≤ B |arg|`, gives the envelope. -/
+theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M)
+    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
+    (h : Clean (M i) f g B) (x arg pre : List Bool) :
+    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
+      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
+          ≠ some (.inl c)) ∧
+      (hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
+        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧
+      ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
+          v).workTapePos j| ≤ (B arg.length : ℤ) := by
+  obtain ⟨t, hp, ht, hguard, hend⟩ := host_clean M K hk ctrl ret q₀ i f g B h x arg pre
+  refine ⟨t, hp, ht, hguard, hend, fun v hv j => ?_⟩
+  have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
+  exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB
+
 end Turing.ModuleHost
diff --git a/TCSlib/Cryptography/Asymptotic/OneWay.lean b/TCSlib/Cryptography/Asymptotic/OneWay.lean
index b2445e44..7ac5de06 100644
--- a/TCSlib/Cryptography/Asymptotic/OneWay.lean
+++ b/TCSlib/Cryptography/Asymptotic/OneWay.lean
@@ -281,8 +281,9 @@ theorem WorstCaseOneWay.toLit {𝓕 : FunFamily} (h : 𝓕.WorstCaseOneWay) : 
   simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hB, hofn]
 
 /-- **The literal form implies the `1^n` form when the output length determines the
-parameter** (injective `outLen`, the case of every family of the text; repair of the run-3
-audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a `1^n`-inverter `B` is the literal
+parameter** (injective `outLen`, equivalently non-constant output length for these polynomial
+lengths; repair of the run-3 audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a
+`1^n`-inverter `B` is the literal
 inverter `NUPPT.exists_reparam_advice B φ var` with `φ (outLen n) = n`, which hard-wires `1^n`
 and `B.advice n` at the output length and leaves its extra coins unread.
 
diff --git a/TCSlib/Cryptography/Candidates/Concrete.lean b/TCSlib/Cryptography/Candidates/Concrete.lean
index 59dac7c5..938af1fa 100644
--- a/TCSlib/Cryptography/Candidates/Concrete.lean
+++ b/TCSlib/Cryptography/Candidates/Concrete.lean
@@ -519,6 +519,15 @@ def rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List B
     if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
     else none
 
+/-- Block rejection sampling unfolded: `rejectBlocksL E k B T r` is the first `some v` over
+`t ∈ [0, T)` (`List.findSome?` over `List.range T`) with `v` the number read from the first `k`
+bits of the `t`-th block of `B` bits of `r`, kept iff `E v`. -/
+theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
+    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
+      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
+      else none :=
+  rfl
+
 /-- An accepted value satisfies the test and is below `2^k` (it is read from at most `k`
 bits, `listToNat_lt_two_pow`). -/
 theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r : List Bool} {v : ℕ}
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLog.lean b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
index 767d14fe..b7fbd309 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLog.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
@@ -49,7 +49,8 @@ collection `expCollection H G hV` therefore takes the validity bridge `hV : ∀
 as an argument.
 
 **Full-length primes.** Where a proof divides by `q` or `p − 1` (Lemma 84.1's range reduction,
-the `1/q` term of Theorem 107.3) the prime must have full length `2^{n−1} ≤ p`. This is
+the `1/q` term of Theorem 107.3) the proofs use full length `2^{n−1} ≤ p` (a convenience: the
+hypothesis is dispensable in both headline theorems, gate 03f1 review, M1). This is
 demanded only *except on a negligible set of coins* (`ExpGroupGen.FullLengthExcept δ` with
 `Negligible δ`): a strict-PPT generator may fall back to a fixed instance when its rejection
 loop fails (D10), and demanding full length on every coin string (`ExpGroupGen.FullLength`)
@@ -316,9 +317,11 @@ def FullLength : Prop :=
 
 /-- The generator outputs primes of full length `n` **except on a set of coins of probability
 at most `δ n`**: for `n ≥ n₀`, `Pr_r[p < 2^{n−1}] ≤ δ n` (the fallback instance of a strict-PPT
-rejection sampler, D10). Needed, with `Negligible δ`, where the proofs divide by `q` or
+rejection sampler, D10). Used, with `Negligible δ`, by the proofs that divide by `q` or
 `p − 1` (Lemma 84.1's range reduction, the `1/q` term of Theorem 107.3): the short-prime coins
-are discarded and contribute at most `δ n`. Whether safe primes (resp. primes `≡ 3 (mod 4)`
+are discarded and contribute at most `δ n`. This is a convenience: instances with `p − 1` below
+a polynomial can be inverted by exhaustive search, so `hbig` could be dropped (gate 03f1
+review, M1; ruling R-03f1-1 (A) keeps it). Whether safe primes (resp. primes `≡ 3 (mod 4)`
 with a generator) of full length can be produced for every `n` except with negligible
 probability is itself open ([PS10, p. 52]: the sampler's "basic theoretical properties are
 unknown"); the hypothesis `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems
@@ -467,6 +470,15 @@ def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
     if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
     else none
 
+/-- `sampleBelowL` is block rejection sampling with the test `v < m`:
+`sampleBelowL m k B T = rejectBlocksL (· < m) k B T` (the same blocks, the same test; gate 03f1
+review, M2). -/
+theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) :
+    sampleBelowL m k B T = rejectBlocksL (· < m) k B T := by
+  funext r
+  rw [rejectBlocksL_eq]
+  rfl
+
 /-- A sampled value is below `m`. -/
 theorem sampleBelowL_lt {m k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleBelowL m k B T r = some v) :
     v < m := by
@@ -484,18 +496,15 @@ distance `(1/2)^n` of the uniform number below `m`. The closeness fact behind
 `expCollection_sampleClose` and the El Gamal samplers (`egUnit`, `egGenParts`, `egEncParts`,
 `ddhExpo`).
 
-**Proof sketch.** `k ≤ n` by `Nat.size_le`, so trial `t < n` reads the first `k` bits of the
-`t`-th block of `n` bits of `List.ofFn b` (`NumberTheory.chunk`; `List.drop`/`List.take` of
-`List.ofFn`), and `sampleBelowL m k n n` is `firstHit (· < m)` of the numbers read from the
-blocks (`List.findSome?` over `List.range n` versus `List.finRange n`; `listToNat` of the `k`
-bits is `bitsToNat` of the block's prefix, `bitsToNat_eq_listToNat`). The map from the `n · n`
-coins to the `n` prefixes is a product of coordinate projections, so it pushes the uniform
-distribution to the uniform one on `Fin n → Fin k → Bool` (`StatClose.comp_pushesUniform`),
-and reading bits is the bijection `bitsEquiv k` onto `Fin (2^k)`; `statClose_firstHit` with
-`E = {x < m}` and `d = 0` gives closeness `(1 − m/2^k)^n ≤ (1/2)^n` (`Nat.lt_size_self`:
-`m/2^k ≥ 1/2`), transported along the bijection `{x : Fin (2^k) // x < m} ≃ Fin m` by
-`StatClose.comp_equiv_right` and `StatClose.map` (`Fin.val`), exactly as in
-`statClose_rejectionSample`. -/
+**Proof sketch.** A corollary of `statClose_rejectBlocksL` (gate 03f1 review, M2; that lemma is
+filled first, and this one is not filled a second time). With `k = Nat.size m`, `k ≤ n` by
+`Nat.size_le` (`m < 2^n`), and `sampleBelowL m k n n = rejectBlocksL (· < m) k n n`
+(`sampleBelowL_eq_rejectBlocksL`). `statClose_rejectBlocksL (· < m) k n n` with the default
+`d = 0` (`0 < m`, `0 < 2^k`) gives closeness `(1 − Pr_{v < 2^k}[v < m])^n = (1 − m/2^k)^n` to
+the uniform element of `{v : Fin (2^k) // v < m}`, and `(1 − m/2^k)^n ≤ (1/2)^n` since
+`2^k ≤ 2m` (`Nat.lt_size_self` and the minimality of `Nat.size`: `m/2^k ≥ 1/2`). Transport the
+target along the value-preserving bijection `{v : Fin (2^k) // v < m} ≃ Fin m`
+(`StatClose.comp_equiv_right`) and weaken the bound (`StatClose.mono`). -/
 theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
     StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
       (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
@@ -514,7 +523,7 @@ def expSampleRaw (z : List Bool) : List Bool :=
 domain `D_i`"] given the arithmetic bundle.
 
 **Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
-leading zeros stripped (requested shared primitive, as in the RSA sampler); the trial loop is
+leading zeros stripped (`H.size`); the trial loop is
 `Complexity.polyTimeComputable_iterateFind` over the `n` blocks of `1^n` bits
 (`polyTimeComputable_pairDropPoly`), each trial comparing the first `k` bits with `m`
 (`H.le`); the payload is the accepted block, the `none` branch gives the fallback; the output
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
index 14900a0d..8c1cc2b3 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
@@ -558,24 +558,36 @@ set and by `WellFormedIndex`), the domain is `Z_{p−1}` (`expOrd_of_valid`), `f
 `expo g_u x` with `g_u := expUnit` a generator (`orderOf_expUnit`, `IsGenerator` by
 `orderOf_eq_card_of_forall_mem_zpowers`-converse `zpowers_eq_top_of_prime_card`-free counting:
 `Nat.card_zpowers`), and `half_i x = halfBit (p−1) x` (`halfPred_eq`), so `A`'s per-instance
-success is `predProb (expo g_u) (halfBit (p−1)) A_i` with `A_i y ρ := A.distinguisherL n ⟨i, encD y⟩ ρ`.
-Apply `invProb_dlInverter_ge` with `s := ⌊ε(p−1)/4⌋ ≥ 1` (as `p − 1 ≥ 2^{n−1} − 1 ≥ 8n^c` for
-large `n`), `T := ⌈(p−1)/s⌉ ≤ 8n^c + 1`, `k := n`, `ℓ := 4n · (2n^c)² = 16 n^{2c+1}`: the inverter
-succeeds on the good instances with probability `≥ (3/4)/T ≥ 3/(4(8n^c + 1))`, hence overall
-`≥ (ε/2) · 3/(4(8n^c + 1))` (`OneWay.uprob_mul_le_uexp`-style averaging over the good set). The
-machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, 1^{n}⟩`, coins
-`T·n + n·ℓ·(2n + A.coins)` (all `PolyExpr`), on `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`,
-computes `s` and `T` from `1^n` and `p` (`H.divMod`, `H.mul`), samples `t` and the `r_{j,i}` by
-rejection (`sampleBelowL` with `H.le`; the statistical term `n·ℓ·(1/2)^n + (1/2)^n` by
-`statClose_rejectionSample`/`StatClose.prod`, `StatClose.abs_uprob_sub_le_prod`), shifts
-`y · g^{−ts}` (`H.modExp`, `H.xgcd` for the inverse), and runs the `n` rounds of `dlLoop`
-(`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`, D11): quadratic
-residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by `H.modExp`
-(`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
-`⟨⟨⟨1^n, ⟨i, z_i⟩⟩, A.advice n⟩, ρ_i⟩` (`polyTimeComputable_iterateEmit`, `NUPPT.polyTimeComputable_layout`),
-the comparison with `half(r_i)` (`halfStr`), the majority (`polyTimeComputable_majority`), the
-negation `p − z` and the bit assembly; finally `(bits + ts) mod (p−1)` as an `n`-bit numeral
-(`decodeFin n` reads it back, `bitsToNat_natToBits`). Thus `G.dlProb B n ≥ 3ε/(8(8n^c+1)) − 2n^{2c+2}(1/2)^n`
+success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
+`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
+Apply `invProb_dlInverter_ge` with `ε := n^{-c}/2`, `s := ⌊(p−1)/(8n^c)⌋` (so `4s ≤ ε(p−1)`),
+`T := ⌈(p−1)/s⌉` (so `Ts ≥ p − 1`), `k := n` (`s ≤ p − 1 < 2^n`) and `ℓ := 16 n^{2c+1}`
+(so `k/(ε²ℓ) = 1/4`). For large `n` the good instances have `p − 1 ≥ 2^{n−1} − 1 ≥ 16 n^c`, so
+`(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16 n^c) ≥ 1` and `T ≤ K(n) := 16 n^c < 2^n`; the inverter then
+succeeds with probability `≥ (3/4)/T ≥ 3/(4K(n))` on each good instance, with ideal coins.
+The machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, ⟦8n^c⟧_n⟩`
+(the `n`-bit numeral of `8n^c`: the bundle has no unary-to-binary conversion); coins
+`n·n + n·ℓ·(n·n + A.coins)` (a `PolyExpr`, `c` being fixed): one block of `n·n` coins for `t`
+and, for each of the `n·ℓ` trials, a block of `n·n` coins for `r_{j,i}` and `A.coins` coins for
+`ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`; computes `s` and `T` (`H.sub`,
+`H.divMod`, `H.add`); outputs `0^n` unless `1 ≤ s` and `T < 2^n` (the analysis uses only the
+good instances); samples `t := (sampleBelowL T (Nat.size T) n n ·).getD 0` and
+`r_{j,i} := (sampleBelowL (p−1) (Nat.size (p−1)) n n ·).getD 0` (`H.le`, `H.size`,
+`polyTimeComputable_iterateFind`); shifts `y · g^{−ts}` (`H.modExp`, `H.xgcd`); and runs the
+`n` rounds of `dlLoop` (`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`,
+D11): quadratic residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by
+`H.modExp` (`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
+`⟨⟨⟨1^n, ⟨i, z_{j,i}⟩⟩, A.advice n⟩, ρ_{j,i}⟩` (`polyTimeComputable_iterateEmit`,
+`NUPPT.polyTimeComputable_layout`), the comparison with `half(r_{j,i})` (`halfStr`), the
+majority (`polyTimeComputable_majority`), the negation `p − z` and the bit assembly; finally
+`(bits + ts) mod (p−1)` as an `n`-bit numeral (`decodeFin n` reads it back,
+`bitsToNat_natToBits`). Sampling: each of the `1 + nℓ` sampled coordinates is within `(1/2)^n`
+of uniform (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`); the coins of
+`A` are exact; `StatClose.prod` and `StatClose.abs_uprob_sub_le_prod` give a loss of at most
+`(1 + 16 n^{2c+2})(1/2)^n` at every instance. Averaging over the good set (probability
+`≥ ε/2`, `HardcoreBit.uprob_mul_le_uexp`):
+`G.dlProb B n ≥ (ε/2)·3/(4K(n)) − (1 + 16 n^{2c+2})(1/2)^n`
+`= 3/(256 n^{2c}) − (1 + 16 n^{2c+2})(1/2)^n`
 for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`. -/
 theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen)
     (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) :
diff --git a/TCSlib/Cryptography/Candidates/ElGamal.lean b/TCSlib/Cryptography/Candidates/ElGamal.lean
index 1f1d1ab4..be4efe98 100644
--- a/TCSlib/Cryptography/Candidates/ElGamal.lean
+++ b/TCSlib/Cryptography/Candidates/ElGamal.lean
@@ -56,10 +56,11 @@ generator's coins (`ExpGroupGen.FullLengthExcept`).
 
 **Run-3 audit repairs.** P8-1: the run-2 DDH ensembles had dependent-sum seeds
 `Σ r, Z_{q_r} × Z_{q_r}` (resp. three factors), on which the uniform seed gives the coin string
-`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — the two ensembles
-then had different instance laws whenever `q` varies with the coins, and the threshold test
-`[q ≥ θ_n]` distinguished them with constant advantage, so `DDHAssumption` was false for every
-randomized generator. The seeds are now product types (uniform coins for the generator, D6)
+`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — so the two ensembles
+could have different instance laws, and when `q` varies non-negligibly with the coins (two
+orders `q`, `3q/2` on half the coins each give the laws `(4/13, 9/13)` and `(8/35, 27/35)`) a
+threshold test `[q ≥ θ_n]` distinguished them, making `DDHAssumption` false for reasons
+unrelated to DDH. The seeds are now product types (uniform coins for the generator, D6)
 with the exponents read by `ddhExpo`. P8-2: `elGamal_secure`'s hypothesis `G.FullLength`
 (full length on every coin string) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.
 
@@ -294,8 +295,8 @@ run-3 audit P2-2, by instance resolution).
 
 Repair (run-3 audit P8-1): the run-2 seed type `Σ r : G.gen.Coins n, Z_{q_r} × Z_{q_r}` gave
 the coin string `r` probability `q_r² / Σ_r q_r²` under the uniform seed, so the instance law
-depended on the fibre sizes and differed from `ddhRandom`'s (cubes), making `DDHAssumption`
-false for every generator whose `q` varies with the coins. -/
+depended on the fibre sizes and differed from `ddhRandom`'s (cubes), which could make
+`DDHAssumption` false for reasons unrelated to DDH (DESIGN §5 item 20). -/
 noncomputable def ddhReal (G : SafePrimeGen) : Ensemble ddhLen where
   σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))
   X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
@@ -509,9 +510,9 @@ def egGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
 (`polyTimeComputable_pairTakePoly`/`_pairDropPoly` on `⟨1^n, r⟩`); run `G.gen.output` on the
 layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`); the two
 rejection loops are `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the
-test `H.le` (the decrement `p − 1` and the bit length `Nat.size` are requested shared
-primitives, as in the RSA generator); `h = g² mod p` and `h^x mod p` by `H.modExp`; the
-numerals are padded to width `n` (`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
+test `H.le` (the decrement `p − 1` and the bit length `Nat.size`: `H.sub`, `H.size`);
+`h = g² mod p` and `h^x mod p` by `H.modExp`; the numerals are padded to width `n`
+(`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
 theorem polyTimeComputable_egGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
     PolyTimeComputable (egGenRaw G) := by
   sorry
@@ -843,8 +844,11 @@ except on a negligible set of the generator's coins (and under the arithmetic hy
 **Deviation:** message space `G_q` and the chosen-message form of security (the text's
 `m ∈ Z_p` is insecure, source error 28); the DDH assumption is relative to `egGroupGen H G`
 and samples its exponents by rejection (`ddhExpo`, D10); `hbig` (`ExpGroupGen.FullLengthExcept`)
-makes the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of probability
-`δ n`; the text leaves the proof as an exercise and omits the generator-versus-square term.
+is used to make the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of
+probability `δ n` (a convenience: if `E[1/q]` were not negligible, a DDH distinguisher finding
+`a` by exhaustive search when `q ≤ 2n^c` would contradict the DDH assumption, so `hbig` could be
+dropped; gate 03f1 review, M1; ruling R-03f1-1 (A) keeps it); the text leaves the proof as
+an exercise and omits the generator-versus-square term.
 
 Repair (run-3 audit P8-1, P8-2): the DDH ensembles' seeds became products (so hybrid 1 below
 is exact up to the event `g² = 1`), and `hbig : G.FullLength` became
diff --git a/TCSlib/Cryptography/Candidates/Factoring.lean b/TCSlib/Cryptography/Candidates/Factoring.lean
index 42944c08..0566c08f 100644
--- a/TCSlib/Cryptography/Candidates/Factoring.lean
+++ b/TCSlib/Cryptography/Candidates/Factoring.lean
@@ -499,11 +499,17 @@ with the step dropping `n` bits, the test `hP` on the first `n` bits, the payloa
 bits, `R = 2n²`, `P = var`), whose `List.range.find?` form is `firstHit` over `chunk`
 (`samplePrime`); the fallback numeral `natToList n 2 = 0^{n-2}10` of a failed run is the
 `none` branch of `iterateFind` (a constant string of unary-polynomial length,
-`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`); the acceptance test of
-`samplePairOut` is two `H.prime` calls, a `pairEq` test and two `H.le`
-comparisons with `1^{max n 2}` (`polyTimeComputable_ite`), the accepted blocks are re-encoded
-with `max n 2` bits (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the
-default pair is a constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
+`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`). The acceptance test of
+`samplePairOut` uses `hP` only (this theorem has no `ArithmeticFP` argument): the two prime
+tests are `hP`, and the inequality of the two values is tested by comparing the two `n`-bit
+words directly (a `pairEq` test: words of equal length have equal values iff they are equal);
+the two range checks `< 2^{max n 2}` are discharged from the fixed widths, not computed (each
+`samplePrimeL` output has `n` bits, so its value is `< 2^n ≤ 2^{max n 2}`,
+`listToNat_lt_two_pow`); the branch is `polyTimeComputable_ite`. The accepted words are
+re-encoded with `max n 2` bits by leading-zero padding (the `max n 2`-bit numeral of an `n`-bit
+word is the word preceded by `max n 2 − n` zeros, a constant block of unary-polynomial length:
+`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the default pair is a
+constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
 theorem polyTimeComputable_samplePairRaw (hP : PolyTimeComputable primeStr) :
     PolyTimeComputable samplePairRaw := by
   sorry
diff --git a/TCSlib/Cryptography/Candidates/RSA.lean b/TCSlib/Cryptography/Candidates/RSA.lean
index e548ac26..e2379a32 100644
--- a/TCSlib/Cryptography/Candidates/RSA.lean
+++ b/TCSlib/Cryptography/Candidates/RSA.lean
@@ -755,14 +755,26 @@ so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of `x`", wh
 event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`, `decodeFin_ofFn`,
 `bitsToNat_natToBits`, `val_units_pow`). Since `x ↦ x^e` pushes uniform to uniform
 (`pushesUniform_rsaPerm`, `PushesUniform.uprob_eq`), the inner probability equals the RSA
-inner probability at `(z, e)`. The law of `(z, e)` under the generator's coins is within
-`rsaGenErr n` of the ideal uniform law on `DistinctPrimes n × Z*_{Φ(N)}`
-(`statClose_samplePrime` with the prime fallback `natToBits n 2` of `samplePrimeL` — run-3
-audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map` through the validity
-test with `uprob_diag` and `one_div_card_primes_le` for the fallback on `p = q`,
-`statClose_rejectBlocksL` for `e` with the acceptance rate of the sampleClose sketch); `StatClose.abs_uprob_sub_le_prod` with the
-auxiliary coins `(y, r)` turns `uexp` over the generator's coins into `uexp` over `z`
-(`uexp_prod`, `uprob_prod`) up to `rsaGenErr n`. -/
+inner probability at `(z, e)`: a number `h(z, e) ∈ [0, 1]` (over `y` and `A`'s coins).
+The exponent group `Z*_{Φ(N)}` depends on `z`, so the generator's law is not compared with one
+uniform product: the comparison is a conditional expectation over `z`. Split the generator's
+coins into the two prime segments and the exponent segment (`rsaGenParams`, `uexp_prod`,
+`uprob_prod`). (i) For each fixed prime pair `z`, the exponent drawn from the exponent segment
+(`sampleUnitL` modulo `Φ(N)`, fallback `1`) is within `e^{-n}` of the uniform element of
+`Z*_{Φ(N)}` (`statClose_rejectBlocksL` with the acceptance rate of the sampleClose sketch), so
+the conditional success at `z` exceeds `g(z) := E_{e uniform}[h(z, e)]` by at most `e^{-n}`
+(`StatClose.abs_uprob_sub_le_prod`, with `(y, r)` as the auxiliary coins). (ii) The law of `z`
+under the two prime segments is within `2 · 2^{-n} + 2n/2^n` of the uniform law on
+`DistinctPrimes n` (`statClose_samplePrime` with the prime fallback `natToBits n 2` of
+`samplePrimeL` — run-3 audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map`
+through the validity test with `uprob_diag` and `one_div_card_primes_le` for the fallback on
+`p = q`); averaging the `[0, 1]`-valued `g` over that law instead of the uniform one costs at
+most that distance (`StatClose.abs_uprob_sub_le_prod` again, with `g(z)` read as a probability
+over the auxiliary coins `ω : Π z', Z*_{Φ(N')} × Z_{N'}^* × A.Coins n` at `ω z`). (iii) Adding
+the conditional exponent error, the inversion probability is at most
+`uexp g + (2 · 2^{-n} + 2n/2^n) + e^{-n} = rsaProb (rsaBreaker A) n + rsaGenErr n`, as
+`rsaProb` is the outer `uexp` over `z` of the inner probability over `(e, y, r)`. No error
+beyond `rsaGenErr n` is needed. -/
 theorem rsaCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
     (rsaCollection H).invProbAt A n ≤ rsaProb (rsaBreaker A) n + rsaGenErr n := by
   sorry
diff --git a/TCSlib/Cryptography/Candidates/Rabin.lean b/TCSlib/Cryptography/Candidates/Rabin.lean
index d9c93a07..a0a19227 100644
--- a/TCSlib/Cryptography/Candidates/Rabin.lean
+++ b/TCSlib/Cryptography/Candidates/Rabin.lean
@@ -146,8 +146,12 @@ theorem blumFactoring_of_factoring (hD : BlumDensity) (hF : FactoringAssumption)
 
 /-! ## The symmetry lemma (Claim-62.2) -/
 
-/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`: a square root of `1` different from `±1`
-[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"]. -/
+/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`, for coprime moduli `p`, `q`
+[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"].
+It squares to `1` for all coprime moduli (`crtNegOne_sq`). For primes `p`, `q` it differs from
+`1` when `q` is odd and from `−1` when `p` is odd (`crtNegOne_ne_one`, `crtNegOne_ne_neg_one`),
+so for two odd primes it is a square root of `1` other than `±1`. Coprimality alone does not
+give this: for `p = 2`, `q = 3` it is `5 = −1` in `Z_6`. -/
 noncomputable def crtNegOne {p q : ℕ} (h : p.Coprime q) : (ZMod (p * q))ˣ :=
   (crtUnits h).symm (1, -1)
 
@@ -495,8 +499,9 @@ theorem rabinCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rabinCollection
 /-- The statistical error of the Rabin reductions at parameter `n`: two restricted prime
 samplers and the unit sampler of `rabinFactorer`, the latter counted twice because it enters
 through the factor `2` of the symmetry lemma (`e^{-n}` each: `4e^{-n}`), and the diagonal
-`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` for the `P = |Π_n| − 1 ≥ 2` odd
-primes (`one_div_card_primes_le`) and `1/B ≤ 4n/2^n` for the `B` Blum primes (`BlumDensity`).
+`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` with `P = |Π_n|` the total prime
+count, of which `P − 1 ≥ 2` are odd (`one_div_card_primes_le`), and `1/B ≤ 4n/2^n` for the `B`
+Blum primes (`BlumDensity`).
 
 Repair (run-3 audit P7-3): the diagonal term was `2n/2^n`, which neither the Chebyshev bound
 `2^n ≤ 2n|Π_n|` (odd class: `1/(|Π_n| − 1)`) nor `BlumDensity` (`1/B`) yields; both give
diff --git a/TCSlib/Cryptography/NumberTheory/Chebyshev.lean b/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
index 423c20bc..ddae2c96 100644
--- a/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
+++ b/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
@@ -36,7 +36,8 @@ arguments by the text's monotonicity of `t / log t`.
 
 **Deviation:** [PS10, Theorem 31.3] claims the strict inequality `π(x) > x / (2 log x)` for
 every real `x > 1`; equality holds at `x = 2` (`π(2) = 1`), so the theorem is stated with `≤`,
-for natural arguments `m ≥ 2`. **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
+and for natural arguments `m ≥ 2`, which repairs and restricts the real claim (it fails even with
+`≤` at `x = 3/2`, where `π(x) = 0`). **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
 `x = 1, p = 2`; the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is Mathlib's
 `Nat.pow_factorization_choose_le`. **Deviation:** the density corollary needs `n ≥ 2`
 (`Π_1 = ∅`); the text's "`n`-bit numbers" silently assumes it.
@@ -157,7 +158,9 @@ theorem chebyshev_two_mul (x : ℕ) (hx : 0 < x) :
 `m / (2 log₂ m) ≤ π(m)`.
 
 **Deviation:** stated with `≤` (the text's `>` fails at `m = 2`) and for natural arguments
-`m ≥ 2` (the text's real `x > 1`; `π` is a step function, so nothing is lost).
+`m ≥ 2`. This repairs and restricts the text's claim for every real `x > 1`, which is false even
+with `≤`: at `x = 3/2`, `π(x) = 0 < x / (2 log₂ x)`. The natural-argument form is the one the
+prime-density uses need.
 
 **Proof sketch.** Even `m = 2x`: `chebyshev_two_mul`. Odd `m = 2x − 1 ≥ 3`: `2x` is composite,
 so `π(m) = π(2x) ≥ 2x / (2 log₂(2x))`, and `t ↦ t / log₂ t` is increasing for `t ≥ 3`
diff --git a/TCSlib/Cryptography/NumberTheory/Primality.lean b/TCSlib/Cryptography/NumberTheory/Primality.lean
index e9e0e712..1c496b08 100644
--- a/TCSlib/Cryptography/NumberTheory/Primality.lean
+++ b/TCSlib/Cryptography/NumberTheory/Primality.lean
@@ -41,7 +41,10 @@ The Miller–Rabin test [PS10, §2.6.5] and the prime sampler [PS10, §2.6.6]:
 test reject primes with positive probability; the test draws `α ∈ [1, N−1]` as in the
 standard presentation, matching `|L_N| = N − 1`. Even `N > 2` are rejected outright (the text
 handles only the base case `N = 2`). **Deviation:** [PS10, Theorem 49.14] says "with
-probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case needs `N` odd.
+probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case is proved for odd `N`
+only, as a convenience: for even `N > 2` the liars also lie in a proper subgroup of `Z_N^*` (the
+kernel of `x ↦ x^{N−1}`, which misses `−1` since `(−1)^{N−1} = −1`), and the test rejects even
+`N` outright.
 **Deviation:** `SamplePrime` is truncated to `T` trials (strict PPT with failure `⊥`, D10)
 and tests primality exactly (`Nat.Prime`); with Miller–Rabin in place of the exact test the
 output would only be statistically close to uniform. §2.6.6 (p. 50) misquotes the prime
@@ -386,8 +389,11 @@ private theorem liar_pow_mem {N : ℕ} (hN : 2 < N) {j' : ℕ}
 /-- **Odd composites have few liars** [PS10, Lemma 50.15, second half]: for odd composite
 `N > 2`, `|L_N| ≤ (N−1)/2`, stated as `2 |L_N| ≤ N − 1`.
 
-**Deviation:** the text says `N > 2` composite (oddness is needed) and `<` (the proof gives
-`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14).
+**Deviation:** the text says `N > 2` composite and `<`. The restriction to odd `N` is a
+convenience, not a necessity: for even `N > 2` every liar satisfies `α^{N−1} = 1` while the unit
+`−1` does not (`N − 1` is odd and `−1 ≠ 1`), so the liars again lie in a proper subgroup;
+`uprob_millerRabin_le` rejects even `N` outright and needs only the odd case. The proof gives
+`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14.
 
 **Proof sketch.** ([CLRS09, Theorems 31.38–31.39].) Every liar is a unit (`α^{N−1} = 1`,
 `mrLiar_isUnit`), so it suffices to exhibit a proper subgroup of `Z_N^*` containing every
@@ -859,10 +865,11 @@ private theorem spFind_eq (n : ℕ) (r : Fin (2 * n ^ 2 * n) → Bool) :
     rfl
 
 /-- **`SamplePrime` is a PPT** [PS10, Lemma 51.17, "in time `poly(n)`"], given a
-polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan,
-AKS or Miller–Rabin): there is a uniform `NUPPT` with coin polynomial `2n² · n` whose
-activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks of
-`n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.
+polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan:
+an exact deterministic primality test such as AKS; a bounded-error Miller–Rabin test does not
+compute `hP`'s function exactly): there is a uniform `NUPPT` with coin polynomial `2n² · n`
+whose activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks
+of `n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.
 
 **Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` (M3): on the state
 word `⟨1^n, r⟩`, the step `spStep` drops the first `n` bits of the second component
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
index f6c4bc5f..8e81839e 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
@@ -39,13 +39,15 @@ and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the erro
 a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
 stated for a protocol and a witness relation without assuming the proof property, which the
 theorems add separately.
-The bound `Lz` is necessary, not only convenient (gate 03e, note 9): the distinguisher runs in
-time polynomial in its input, the encoded view, which contains `z`; with `|z| ≥ 2^n` it could
-invert a one-way permutation on `n`-bit inputs and open the unopened commitments of the
-3-colouring protocol, so computational zero-knowledge would fail for every protocol whose
-hiding is only computational. Read literally, [PS10, Definition 121.2] (every
-`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect. For the same reason
-the distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
+The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e,
+note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the
+encoded view, which contains `z`. With `|z|` exponential in `ℓ(n)` it can open the perfectly
+binding commitments by exhaustive search. On a graph with two proper colourings outside one
+colour-permutation orbit, that tells the two real views apart with advantage 1, while the
+simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every
+`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol.
+Protocols with exactly simulable views are not affected. For the same reason the
+distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
 
 **Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
 drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
@@ -307,6 +309,15 @@ def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
     (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
       (S.coinLen (NUPPT.inParam w).length)))
 
+/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
+`inParam w`, argument `inArg w`, empty advice and coins
+`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
+theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
+    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
+      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
+        (S.coinLen (NUPPT.inParam w).length))) :=
+  rfl
+
 /-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
 (for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
 first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
@@ -317,6 +328,41 @@ noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
     attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
   else []
 
+/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
+whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
+attempt `i` if `i < N`, and `[]` otherwise. -/
+theorem retry_eq (S : NUPPT) (w : List Bool) :
+    retry S w =
+      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
+          (NUPPT.inParam w).length then
+        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
+      else [] :=
+  rfl
+
+/-- If attempt `i < |inParam w|` is the first that does not abort (`attempt S w i ≠ []`, and
+`attempt S w j = []` for every `j < i`), then `retry S w` is attempt `i`.
+
+**Proof sketch.** `firstIdx` of the non-abort test is `i` (`firstIdx_eq_of`); rewrite
+`retry_eq` with it and take the `i < |inParam w|` branch. -/
+theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
+    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
+    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
+  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
+    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
+  rw [retry_eq, h, if_pos hi]
+
+/-- If all `|inParam w|` attempts abort (`attempt S w t = []` for every `t < |inParam w|`),
+then `retry S w = []`. Together with `retry_eq_attempt` this covers every input.
+
+**Proof sketch.** `firstIdx` of the non-abort test is `|inParam w|` (`firstIdx_eq_of_forall`);
+rewrite `retry_eq` with it and take the `else` branch. -/
+theorem retry_eq_nil {S : NUPPT} {w : List Bool}
+    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
+  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
+      (NUPPT.inParam w).length :=
+    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
+  rw [retry_eq, h', if_neg (lt_irrefl _)]
+
 /-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.
 
 **Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
index 9869c680..675fa55e 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
@@ -71,9 +71,10 @@ lemmas are proved in this file (the `xor` bijection `adaptiveEquiv` and the chan
 variables `gniShear`), which certifies the repaired statements.
 
 **Deviation (fixed alternation, D8):** the repeated graph-isomorphism protocol uses four
-moves per iteration (`H`, `b`, `γ`, and an empty verifier message) so that the strict
-prover/verifier alternation of `exec` is respected; the repeated protocols run `|x|`
-iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in `|x|` directly).
+moves per iteration (`H`, `b`, `γ`, and a verifier message, empty except for the final
+verdict) so that the strict prover/verifier alternation of `exec` is respected; the repeated
+protocols run `|x|` iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in
+`|x|` directly).
 
 **Deviation (well-formedness):** the verifiers reject common inputs that are not the
 encoding of two graphs on the same vertex set (`wellFormedInstance`); without this check a
@@ -552,7 +553,8 @@ noncomputable def giVerifierRep : Strategy where
 
 /-- The `|x|`-fold graph isomorphism protocol [PS10, Protocol 120.6, "repeat the procedure
 `|G₁|` times"] (Prot-120.6): prover first, four moves per iteration (`H_i`, `b_i`, `γ_i`, and
-an empty verifier message, D8 fixed alternation), `4|x|` messages. -/
+a verifier message, empty except for the final verdict, D8 fixed alternation), `4|x|`
+messages. -/
 noncomputable def giProtocolRep : Protocol where
   P := giProverRep
   V := giVerifierRep
@@ -924,18 +926,20 @@ theorem gni_interactiveProof : InteractiveProof gniProtocolRep Lniso :=
 `n² ≤ |x|`, so at most `|x|` bits per message, on every instance (ruling G3-3 of gate 03;
 `GI.giProver_length_le`). -/
 theorem giProtocol_proverBounded (R : List Bool → List Bool → Prop) :
-    giProtocol.ProverBounded R .var := fun x y r hist _ => GI.giProver_length_le x y r hist
+    giProtocol.ProverBounded R .var :=
+  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProver_length_le x y r hist
 
 /-- The `|x|`-fold form of `giProtocol_proverBounded` (`GI.giProverRep_length_le`). -/
 theorem giProtocolRep_proverBounded (R : List Bool → List Bool → Prop) :
-    giProtocolRep.ProverBounded R .var := fun x y r hist _ => GI.giProverRep_length_le x y r hist
+    giProtocolRep.ProverBounded R .var :=
+  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProverRep_length_le x y r hist
 
 /-- The honest graph non-isomorphism prover sends one bit per message (ruling G3-3 of gate 03;
 `GI.gniProver_length_le`), in one iteration and in the `|x|`-fold protocol. -/
 theorem gniProtocol_proverBounded (R : List Bool → List Bool → Prop) :
     gniProtocol.ProverBounded R (.const 1) ∧ gniProtocolRep.ProverBounded R (.const 1) :=
-  ⟨fun x y r hist _ => GI.gniProver_length_le x y r hist,
-    fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
+  ⟨(Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist,
+    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
 
 /-- One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
 with soundness error `1/2` and efficient prover with respect to `R_iso`
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
index a8918e97..22a93238 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
@@ -318,7 +318,8 @@ theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Ef
       rw [HardcoreBit.uprob_eq_one_of_forall hall]
       norm_num
   efficientP := hP
-  boundedP := ⟨.var, fun x y r hist _ => giProver_length_le x y r hist⟩
+  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
+    giProver_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact gi_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
index 4aeed143..22b293d7 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
@@ -474,7 +474,8 @@ theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVeri
       have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
       linarith
   efficientP := hP
-  boundedP := ⟨.var, fun x y r hist _ => giProverRep_length_le x y r hist⟩
+  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
+    giProverRep_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact giRep_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
index 23519614..b6f95458 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
@@ -37,10 +37,12 @@ last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chap
 are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
 message as the verdict.
 Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover,
-verifier, prover) is repeated under strict alternation by appending one dummy empty verifier
-message to each iteration, so that every iteration starts with the prover; the fourth move of
-`giProtocolRep` and of `colProtocolRep`, and the filler moves of the sequential repetition of
-[PS10, §7.2.1] in ch. 7, follow this convention.
+verifier, prover) is repeated under strict alternation by giving each iteration one additional
+verifier move, so that every iteration starts with the prover. In `giProtocolRep` and
+`colProtocolRep` that move is the empty message, except for the protocol's final move, which
+carries the verifier's verdict (the verdict convention above). The sequential repetition of
+[PS10, §7.2.1] in ch. 7 pads each phase instead with `rounds(|x|)` filler moves of both parties,
+its last filler again carrying the verdict.
 `Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
 activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
 whole random tape; the time is polynomial in the total input length rather than in `|x|`
@@ -331,6 +333,13 @@ of length `2^{rounds}`, which the composition theorems of ch. 7 cannot simulate.
 def ProverBounded (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : Prop :=
   ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length
 
+/-- **Bounded honest messages unfolded:** `π.ProverBounded R B` iff for every `x` and `y` with
+`R x y`, every tape `r` and every history `hist`, `|π.P.next x y r hist| ≤ B(|x|)`. -/
+theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) :
+    π.ProverBounded R B ↔
+      ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length :=
+  Iff.rfl
+
 /-- A message bound `B` implies every pointwise larger bound `B'`. -/
 theorem ProverBounded.mono {π : Protocol} {R : List Bool → List Bool → Prop} {B B' : PolyExpr}
     (h : π.ProverBounded R B) (hle : ∀ n, B.eval n ≤ B'.eval n) : π.ProverBounded R B' :=
diff --git a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
index 6b774497..09042140 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
@@ -33,8 +33,9 @@ read as the output string `[false]`, the negligible `ε` quantified before the i
 cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
 polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
 averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
-every pair of random tapes. The parties' efficiency (the text's "p.p.t.") is
-`Strategy.Efficient`, polynomial time in `|x| + |z| + |messages|` (D8), together with a
+every pair of random tapes. The verifier's efficiency (Definition 116.1's "p.p.t.", and the
+prover's for Definition 119.5) is `Strategy.Efficient`, polynomial time in
+`|x| + |z| + |messages|` (D8), together with a
 polynomial bound `B(|x|)` on the honest prover's messages (ruling G3-3 of gate 03, the
 convention of ch. 6): in the completeness clause of `InteractiveProof` and
 `InteractiveProofErr` for the completeness witness, and as the field `boundedP`
@@ -43,10 +44,13 @@ witness. The residual deviation is that against a cheating prover the verifier's
 polynomial in the length of the messages it receives, not in `|x|`. Since the honest messages
 are short, the verifier can always be capped: `V` reading only the first `B(|x|)` bits of each
 message is still complete (the honest messages are untouched) and sound (against `P*` it acts
-as `V` against `P*` with truncated messages, another prover strategy). So the proof systems
-hold only for languages of the text's class IP — undecidable languages such as the halting
-problem, whose computation histories are not polynomially bounded, are excluded — while
-`IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
+as `V` against `P*` with truncated messages, another prover strategy). So `InteractiveProof`
+(and `InteractiveProofErr` with negligible error, by `InteractiveProofErr.interactiveProof`)
+holds only for languages of the text's class IP — undecidable languages such as the halting
+problem, whose computation histories are not polynomially bounded, are excluded — the
+explicit-error forms with a large error say little (with `s = 1` the zero-message,
+always-accepting protocol is an `EfficientProverProofErr` for every language and relation) —
+while `IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
 (run-3 audit P9-1). The capping argument is not formalized as a lemma.
 
 ## Main definitions
@@ -111,12 +115,14 @@ on the complete history of the fixed-alternation execution; `P'` ranges over str
 polynomial random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is
 `uprob = 1` (every pair of random tapes). The verifier's "p.p.t." is `Strategy.Efficient`,
 polynomial-time in `|x| + |z| + |messages|` (D8), and the honest messages on the completeness
-witness are bounded by `B(|x|)` (the text's p.p.t. prover writes at most `t(|x|)` bits; the
-convention of ch. 6). Against a cheating prover the verifier's work is polynomial in the
-length of the messages it receives, not in `|x|`; because the honest messages are short the
-verifier can be capped to their length without losing completeness or soundness (module
-docstring), so the predicate holds only for languages of the text's class IP. The class `IP`
-is stated with the message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
+witness are bounded by `B(|x|)` (Definition 116.1's prover need not be efficient; bounding its
+messages is the chosen normal form, harmless because a verifier of time `t(|x|)` reads at most
+`t(|x|)` bits of each message; the convention of ch. 6). Against a cheating prover the
+verifier's work is polynomial in the length of the messages it receives, not in `|x|`; because
+the honest messages are short the verifier can be capped to their length without losing
+completeness or soundness (module docstring), so the predicate holds only for languages of the
+text's class IP. The class `IP` is stated with the message-prefix cap `Strategy.ReadsPrefix`
+(run-3 audit P9-1). -/
 structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
   /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
   efficientV : π.V.Efficient
@@ -232,7 +238,7 @@ theorem Protocol.ProverBounded.exists_complete {π : Protocol} {L : Language Boo
       ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 :=
   ⟨B, fun x hx =>
     let ⟨y, hy⟩ := hLR x hx
-    ⟨y, fun r hist => hB x y r hist hy, hc x y hy⟩⟩
+    ⟨y, fun r hist => (π.proverBounded_iff R B).1 hB x y r hist hy, hc x y hy⟩⟩
 
 /-! ### Witness relations -/
 
@@ -466,7 +472,7 @@ theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
 theorem npProtocol_proverBounded (T : List Bool → Bool) (p : PolyExpr)
     {R : List Bool → List Bool → Prop} (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
     (npProtocol T p).ProverBounded R p :=
-  fun x y _ _ hxy => hp x y hxy
+  ((npProtocol T p).proverBounded_iff R p).2 fun x y _ _ hxy => hp x y hxy
 
 /-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
 `R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
diff --git a/TCSlib/Cryptography/ZeroKnowledge/NP.lean b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
index 8ad8b9c0..9e83f76c 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/NP.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
@@ -275,6 +275,7 @@ theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
     {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
     {π : Protocol} {B : PolyExpr} (hB : π.ProverBounded R' B) :
     (π.pullback f w p).ProverBounded R (B.subst p) := by
+  rw [Protocol.proverBounded_iff] at hB ⊢
   intro x y r hist hxy
   rw [PolyExpr.eval_subst, ← h.length_eq x]
   exact hB (f x) (w x y) r hist (h.witness x y hxy)
@@ -674,25 +675,27 @@ scheme `(Com, ℓ)` and every witness relation `R` of `L` there is a Levin reduc
 one-iteration 3-colouring protocol is zero-knowledge for `R` with soundness error
 `1 - 1/p(|x|) + 2^{-p(|x|)}`, and its `n|E|`-fold repetition is an interactive proof with
 efficient prover (`zk_proof_of_levinReduction`, with `hLR` from `WitnessRelation.mem_iff`).
+The Levin reduction `LevinReduction L L3COL R R3COL f w p` is part of the conclusion (ruling
+R-03e-r2-1 of gate 03e round 2), so further protocols can be pulled back along the same maps.
 
 **Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
 theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL)
     {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool}
     {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
     ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
-      (∀ N, N ≤ p.eval N) ∧
+      LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
       EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
       ZK ((colProtocol Com ℓ).pullback f w p) R ∧
       EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
         (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨f, w, p, h⟩ := h3 L R hR
-  exact ⟨f, w, p, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
+  exact ⟨f, w, p, h, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
 zero-knowledge proof", for every witness relation** (Thm-124.1; gate 03e, minors 3 and 4):
 from the text's hypothesis, a one-way permutation, there is a commitment scheme
-(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds,
-under NP-hardness of `3COL` with Levin reductions.
+(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds
+(the Levin reduction included), under NP-hardness of `3COL` with Levin reductions.
 
 **Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
 theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
@@ -700,7 +703,7 @@ theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
     {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
     ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
       ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
-        (∀ N, N ≤ p.eval N) ∧
+        LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
         EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
         ZK ((colProtocol Com ℓ).pullback f w p) R ∧
         EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
@@ -734,7 +737,7 @@ theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → L
         EfficientProverProofErr π L R
           (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
-  obtain ⟨_, _, p, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
+  obtain ⟨_, _, p, -, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
   exact ⟨R, hR, ⟨_, h1⟩, _, p, hp, h2, h3'⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
index 0d3c8409..8e77b389 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
@@ -301,8 +301,9 @@ noncomputable def samplePerm3 (T : ℕ) (r : List Bool) : Equiv.Perm (Fin 3) :=
   ((sampleIdx 6 3 T r).map perm3Equiv).getD 1
 
 /-- The verifier's random edge `e ← E` of [PS10, Protocol 127.5] as an index in `[m]`: `T`
-rejection trials of `Nat.size m` bits (so that `m ≤ 2^k < 2m`, success probability `≥ 1/2`),
-the index `0` on failure (D10). -/
+rejection trials of `k = Nat.size m` bits (for `m > 0`, `m < 2^k ≤ 2m`, so each trial succeeds
+with probability `≥ 1/2`; for `m = 0` the sampler returns the default), the index `0` on
+failure (D10). -/
 def sampleEdgeIdx (m T : ℕ) (r : List Bool) : ℕ :=
   ((sampleIdx m (Nat.size m) T r).map Fin.val).getD 0
 
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
index e8cb2fe1..84e5e0a0 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
@@ -495,8 +495,9 @@ noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr
     else []
 
 /-- The `n|E|`-fold protocol of [PS10, Protocol 127.5] (Prot-127.5): prover first, four moves
-per iteration (commitments, edge, openings, empty verifier message; D8 fixed alternation),
-`4|x|²` moves in all, of which the first `4 n|E|` carry the iterations. -/
+per iteration (commitments, edge, openings, and a verifier message, empty except for the final
+verdict; D8 fixed alternation), `4|x|²` moves in all, of which the first `4 n|E|` carry the
+iterations. -/
 noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
   P := colProverRep Com ℓ
   V := colVerifierRep Com ℓ
@@ -607,7 +608,8 @@ theorem colProtocol_proverBounded {Com : List Bool → List Bool} {ℓ : PolyExp
     ∃ B : PolyExpr, (colProtocol Com ℓ).ProverBounded R B ∧
       (colProtocolRep Com ℓ).ProverBounded R B := by
   obtain ⟨B, hB⟩ := colProver_length_le hC.easy ℓ
-  refine ⟨B, fun x y r hist _ => hB x y r hist, fun x y r hist _ => ?_⟩
+  refine ⟨B, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => hB x y r hist,
+    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => ?_⟩
   show ((colProverRep Com ℓ).next x y r hist).length ≤ B.eval x.length
   simp only [colProverRep]
   split_ifs <;> first | exact hB _ _ _ _ | exact Nat.zero_le _
@@ -878,7 +880,8 @@ theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyE
     obtain ⟨B, hB, -⟩ := colProtocol_proverBounded hC R3COL
     refine ⟨B, fun x hx => ?_⟩
     obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
-    exact ⟨encColoring c, fun r hist => hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
+    exact ⟨encColoring c,
+      fun r hist => (Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
       fun z => HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r⟩
   sound := fun x hx P' z => colProtocol_sound hC x hx P' z
   efficientP := colProver_efficient hC.easy ℓ
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
index c233cc12..955948e3 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
@@ -31,9 +31,10 @@ the distinct colour pairs, the commitment randomness `Fin n → Fin ℓ(n) → B
 `ρ` of an arbitrary verifier `V*` given as its reply function); the *string* layer is the
 simulator `colSim` run by a uniform `NUPPT` on the tape layout of `colSimBlock`.
 
-**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT,
-truncated at `n|E|` attempts and outputting `⊥ = []` on failure, which costs the statistical
-term `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
+**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT
+(D8's definition of `ZK`); it makes at most `n|E|` attempts and outputs `⊥ = []` on failure, as
+the text does (Algorithm 128.7, steps 4–5), and the failure costs the text's own term
+`(1 − 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
 rejection-sampled from the bit tapes; the hybrid over attempts has `n|E|` steps (the text says
 `2n|E|`) and the text's `6|E|` sub-hybrid is replaced by a non-uniform choice of the worst
 `(e', π)`; "`k ∈ [m] ∖ {i', j'}`" is read as `k ∈ [n]`; if `E = ∅` the simulator commits to
@@ -318,9 +319,9 @@ theorem uprob_colSimAttemptH_some [Fintype ρ] (hm : 0 < edgeCount G)
     (fun a => edgeIdxOfMsg_lt hm _) (fun a => T (colRealView Com ℓn G c V a))
 
 /-- **The truncated `S''` fails with probability `(1 - 1/|E|)^N`** [PS10, proof of Proposition
-128.8, "`S''` fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the attempts use
-disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability `1 - 1/|E|`
-(`uprob_colSimAttemptH_none`). -/
+128.8, "`S'` [sic: `S''`] fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the
+attempts use disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability
+`1 - 1/|E|` (`uprob_colSimAttemptH_none`). -/
 theorem uprob_colSimTruncH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
     (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
     uprob (fun w => colSimTruncH Com ℓn G c V N w = none) = (1 - 1 / (edgeCount G : ℝ)) ^ N := by
@@ -633,8 +634,9 @@ noncomputable def colSimAttemptStr (Com : List Bool → List Bool) (ℓ : PolyEx
 the consecutive coin blocks of the tape `r`, the first successful attempt's view, or `⊥ = []`
 after `n|E|` failures; a single attempt if `E = ∅`.
 
-**Deviation (D8):** truncated at `n|E|` attempts (strict PPT) instead of restarting until
-success. -/
+As in [PS10, Algorithm 128.7, steps 4–5], at most `n|E|` attempts, then `fail` (`⊥ = []`).
+**Deviation (D10):** `e'` and the colour pair are rejection-sampled from the tape (defaults `0`
+and `(0, 1)`). -/
 noncomputable def colSim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
     (x z r : List Bool) : List Bool :=
   let B := (colSimBlock ℓ V').eval x.length
@@ -676,9 +678,10 @@ theorem exists_colSimulator {Com : List Bool → List Bool} (hCom : PolyTimeComp
 commitment's hiding error `ε(n)` at the vertex count `n = √|x|` into a function of `|x|`,
 Inf-4.4).
 
-**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)` and `N ≥ max ((n₀ + 1)², 4^c · 4)`:
-`n := Nat.sqrt N ≥ n₀` (`Nat.le_sqrt`) and `N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`), so
-`N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` once `n ≥ 4^c`, whence `|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
+**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)`, `K := max (n₀, 4^c, 1)` and `N ≥ K²`:
+`n := Nat.sqrt N ≥ K` (`Nat.le_sqrt`), so `n ≥ n₀`, `n ≥ 4^c`, `n ≥ 1`, and
+`N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`); hence `N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` and
+`|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
 theorem Negligible.comp_sqrt {μ : ℕ → ℝ} (hμ : Negligible μ) :
     Negligible fun N => μ (Nat.sqrt N) := by
   intro c
@@ -719,48 +722,59 @@ there is a negligible `ε` with, for all `x`, witnesses `y` and `z` with `|z| 
 advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
 `ε(|x|)`.
 
-**Deviation (D8, D10):** strict PPT simulator truncated at `n|E|` attempts, rejection-sampled
+**Deviation (D8, D10):** strict PPT simulator (D8's definition of `ZK`), rejection-sampled
 `π`, `e'` and colour pairs; the error bound is in `|x|` (the text's `e(n)` with `n`
 undefined); one iteration (the `n|E|`-fold protocol's zero-knowledge is sequential
 composition, [PS10, §7.2.1], out of scope).
 
-**Proof sketch.** Fix `V'` efficient and take `S` from `exists_colSimulator hC.easy`. Fix
-`Lz` and `D`. Let `B` be the hiding reduction machine of Claim-129.d (`colSimRed` at the
-string level): at parameter `n` it carries in its advice the worst instance
-`(x_n, y_n, z_n)` with `|x_n| = n²`, `|y_n| = 2n`, `|z_n| ≤ Lz(n²)` (`NUPPT.exists_withAdvice`
-with the polynomial bound `add (add (mul var var) (mul (const 2) var)) (Lz.subst (mul var var))`),
-the hybrid index `k_n`, `e₀`, `π₀` and `D.advice n²`; its coins are the other attempts' blocks
-and `D`'s coins (`NUPPT.exists_split`); it runs `V'`'s machine and `D`'s machine
-(`NUPPT.exists_seq`, `NUPPT.exists_comp`, `polyTimeComputable_iterateFind` for the attempts,
-`polyTimeComputable_blockMap ℓ` with `hC.easy` for the commitments, `msgAt` projections by
-`polyTimeComputable_iterate_pairFstD`). `hC.multiHiding var B` gives a negligible `ε_B` with
-`distAdv (multiCom Com v ·) (multiCom Com v' ·) (B.distinguisherL n) ≤ ε_B n` for all `n`-vectors
-`v, v'`. Put
-`ε N := N · ε_B (Nat.sqrt N) + Real.exp (-(Nat.sqrt N)) + 2 N² (1/4)^N + N² (1/2)^N + (1/4)^N`,
+**Proof sketch.** Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy`, and fix `Lz`
+and `D`. For `x = encGraph G`, `y = encColoring c` with `c` proper and `|z| ≤ Lz |x|`, let `n` be
+the vertex count, `m = |E|`, `K = n m ≤ n³`, and `D'` the distinguisher `D.distinguisherL |x|`
+on the encoded optional view (`⊥ ↦ []`).
+
+(1) The real view, with `π = samplePerm3 |x| …`, is within `(1/4)^{|x|}` of the view with a
+uniform `π`: `statClose_samplePerm3`, `StatClose.prod`/`StatClose.refl` for the prover's
+randomness and `V'`'s tape, and `StatClose.map`. `exec_succ` three times, `decGraph_encGraph`,
+`decColoring_encColoring`, and `colProver` with `V com r_V := V'.next x z r_V [com]` unfold it to
+`some ∘ colRealView`.
+
+If `m > 0`:
+(2) `colSim` is within `K((1/2)^{|x|} + (1/4)^{|x|})` of `colSimTrunc … K`, with uniform
+`(e'_t, (a_t, b_t))` read from disjoint fields of the `t`-th block (`statClose_sampleEdgeIdx`,
+`statClose_sampleColorPair` — the colour-pair analogue of `statClose_samplePerm3`, still to be
+added: the fill ladder's first step, gate 03g review M3 — and `StatClose.prod` over the blocks).
+(3) `uprob_colSimTruncW_eq`.
+(4) `exists_colSimRed_ge` with `N := K` gives `k, e₀, π₀` with
+`distAdv truncW truncH D' ≤ K · distAdv X Y (colSimRed … k e₀ π₀ D')`.
+`CommitmentLemmas.exists_fixCoins` fixes the reduction's attempt table `w₀` without loss.
+With `w₀` fixed, only attempt `k` reads the challenge `cv`, so the fixed reduction is
+`cv ↦ D'(pre <|> planted cv <|> post)` for two constant optional views.
+(5) `statClose_colSimTruncH` and `one_sub_inv_pow_mul_le_exp` give
+`distAdv truncH (some ∘ colRealView) D' ≤ e^{−n}`.
+
+If `m = 0` and `n ≥ 1`, the two views differ only in the commitment vector (`π ∘ c` against
+`0`). For each fixed `π`, `D`'s advantage is the hiding gap of
+`cv ↦ D(encode ⟨x, z, r_V, [cv, []]⟩)`, with `r_V` fixed by `exists_fixCoins`. Average over `π`.
+If `n = 0`, bound the advantage by `1`: the simulator's tape is empty, so its `r_V = []` differs
+from the real tape when `V'.coinLen 0 > 0`.
+
+The machine `B` at parameter `n`: among the finitely many data at vertex count `n` (finite
+because `|z| ≤ Lz(n²)`: this is where the bound `Lz` is used, see the `Defs.lean` module
+docstring), take those whose fixed reduction (either case) has the largest gap on its own
+vectors. Hard-wire `x`, `z`, the case, `ρ_k`, `e₀`, the two endpoint commitments and openings,
+`pre`, `post` and `D.advice (n²)` as advice (`NUPPT.exists_withAdvice`; polynomially bounded by
+`hC.easy.output_length_le` and `colProtocol_proverBounded`). Call `V'`'s uniform machine once
+(`Strategy.Efficient`) and `D` at parameter `n²` on `B`'s coins (`NUPPT.exists_reparam_advice`,
+`φ n = n²`). Its acceptance probabilities on `multiCom` samples are the fixed reduction's (coin
+transport along `finCongr`). `hC.multiHiding var B` gives a negligible `ε_B ≥ 0` (it bounds a
+`distAdv` at every `n`), so the hiding terms are at most
+`K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`.
+
+Put `ε N := N² ε_B (Nat.sqrt N) + exp (−Nat.sqrt N) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`. It is
 negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div`
-(`C = 1`), `negligible_two_pow_neg` (with `(1/4)^N ≤ (1/2)^N`), `Negligible.add`,
-`Negligible.const_mul`. Now fix `x = encGraph G`, `y = encColoring c` with `c` proper
-(`R3COL`), `|z| ≤ Lz |x|`, `n` the vertex count, `m = |E|`. If `m = 0` the real view is
-`⟨⟨x,z⟩,⟨r_V,[colCommit (π ∘ c) r, []]⟩⟩` and the simulated one has the all-zero colours, so
-`D`'s advantage is at most `ε_B n` by `hC.multiHiding` applied to a machine `B'` built like
-`B` (absorbed into `B` by a case split on `m` in its advice). Otherwise `n ≥ 2` and the chain is:
-(1) the real view with `π = samplePerm3 |x| …` is within `(1/4)^{|x|}` of the view with a
-uniform `π` (`statClose_samplePerm3`, `StatClose.prod` with `StatClose.refl` for the
-randomness and `V'`'s tape, `StatClose.map` by the view encoding; `exec_succ` three times,
-`decGraph_encGraph`, `decColoring_encColoring`, `colProver`/`colVerifier` unfold to
-`colRealView` with `V com r_V := V'.next x z r_V [com]`); (2) `colSim` is `(Option.map enc
-(colSimTrunc … (n m) w)).getD []` with the `t`-th attempt's coins read from the `t`-th block
-(`colCoinSlice`, `colSimBlock`), within `n m ((1/2)^{|x|} + (1/4)^{|x|})` of the same with
-uniform `(e'_t, (a_t, b_t))` (`statClose_sampleEdgeIdx`, the colour-pair analogue of
-`statClose_samplePerm3`, `StatClose.prod` over the blocks); (3) `uprob_colSimTruncW_eq` makes
-that the law of `colSimTruncW`; (4) `exists_colSimRed_ge` with `N := n m` gives `k, e₀, π₀`
-with `distAdv (truncW) (truncH) D' ≤ n m · distAdv (X) (Y) (colSimRed …)`, and
-`colSimRed … = B.distinguisherL n` up to the coin bijection (`acceptProb_comp_equiv`), so
-`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`; (5) `statClose_colSimTruncH` and
-`one_sub_inv_pow_mul_le_exp` give `distAdv (truncH) (some ∘ colRealView) D' ≤ e^{-n}`
-(`distAdv_le_of_statClose`). The triangle inequality for `distAdv` (`abs_sub_le` on the
-acceptance probabilities) sums the five terms, and `Nat.sqrt |x| = n` (`length_encGraph`,
-`Nat.sqrt_eq`). -/
+(`C = 1`), `negligible_two_pow_neg` and `Negligible.add`. At `N = 0` its exponential term is
+`1`. Use the triangle inequality for `distAdv` (`abs_sub_le`), and `Nat.sqrt |x| = n`
+(`length_encGraph`, `Nat.sqrt_eq`). -/
 theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
     ZK (colProtocol Com ℓ) R3COL := by
   sorry
diff --git a/audits/pass-shelat/Checks.lean b/audits/pass-shelat/Checks.lean
index 61fb0276..f6e3c056 100644
--- a/audits/pass-shelat/Checks.lean
+++ b/audits/pass-shelat/Checks.lean
@@ -423,6 +423,8 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.Commitment.multiHiding
 -- Ruling G3-3: bounded honest prover messages in the proof systems.
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.mono
+-- Round 2, finding 2: the reading lemma of `Protocol.ProverBounded`.
+#print axioms TCSlib.Cryptography.Protocol.proverBounded_iff
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.exists_complete
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.pullback
 #print axioms TCSlib.Cryptography.InteractiveProof.exists_accept
@@ -439,6 +441,11 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 -- Ruling G3-4: perfect zero-knowledge with abort implies statistical ZK (error 2^{-|x|}).
 #print axioms TCSlib.Cryptography.AbortRetry.statClose_retry
 #print axioms TCSlib.Cryptography.AbortRetry.exists_retrySimulator
+-- Round 2, finding 2: the reading lemmas of `AbortRetry.attempt` and `AbortRetry.retry`.
+#print axioms TCSlib.Cryptography.AbortRetry.attempt_eq
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq_attempt
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq_nil
 #print axioms TCSlib.Cryptography.PerfectZKAbort.statZK
 #print axioms TCSlib.Cryptography.PerfectZKAbort.zk
 #print axioms TCSlib.Cryptography.perfectZK_zeroRounds
diff --git a/machine-library-design.md b/machine-library-design.md
index 1dea9731..52be0e2d 100644
--- a/machine-library-design.md
+++ b/machine-library-design.md
@@ -3087,7 +3087,7 @@ and a statement gate before a second consumer is briefed.
 | H11 | **Indexed input access** (ours, `SpaceComplexity/Logspace/`): the input bit and length languages `inputBitLang`/`inputLenLang` read by an oracle call on a register-held index (their answers `indicator_inputBitLang`/`indicator_inputLenLang`), the stride decoder `boundedDecodeStride_loop` (with `boundedDecode_loop` its stride-one instance), the increment/decrement chain `arm_chain`, and the preimage host (`PreimageHost.compile_decides`, `mem_LOGSPACE_preimage`) | **existing (2026-10-11), public; now a host with received consumers.** The response proposes it stay under `Logspace/` (addendum 1). D7 and `decChain` were done in the payback (PR #101, landed 2026-10-15): `Codec/Engine`'s `decodeStride_loop` and `incChain`/`decChain` are instances of `boundedDecodeStride_loop` and `arm_chain` | every received ARM customer through its decider bank; `Codec/Engine` (its decoder and chains are instances); `PathHardRegs` (`mem_LOGSPACE_preimage` for `dropIdx`); `ARMLoops`, `NARMKit`, `VWord`, `ARMWidthExample` (direct importers) |
 | H12 | **Code reachability with a growing window (`ExpBFS`)**: the reachable-code sets `RCode`/`rset` per radius, the stop rule (`mem_iff_of_card_eq`, `card_rset_succ_of_le`), the window lemma `inWin_runWith_of_decides`, and the breadth-first MARM search giving `NSPACE_subset_exp_dtime_of_le` | **received 2026-10-14; public, ungated; accepted exception.** Built at ARM level, so H4's language-first route and MIG-19 are moot for this theorem | `NSPACE_subset_exp_dtime` (`ExpTime.lean`) and its two corollaries; inductive counting (H13b) uses the stop rule (`ISCountGenRadius` directly, `ISCountGenCorrect` transitively) |
 | H13 | **The customer machines**, each with its named consumers and its own reachability notion: (a) Savitch's midpoint recursion `SavitchARM` with its code-decider bank; (b) inductive counting `ISCount*`; (c) the PATH walk `PathWalk*` with `WalkLe`; (d) PATH hardness `PathHard*` (the code graph `red`); (e) the TQBF walk `TQBFARM`; (f) TQBF hardness `TQBFHard*` (the ∀-folded midpoint formula and Tseitin after the prefix) | **received 2026-10-14; public, ungated; accepted exception.** (a)–(e) are machines over H7–H10; (f) is a reduction over H10 and the polynomial-time closure algebra | (a) `PSPACE_eq_NPSPACE`; (b) `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`; (c) `PATH_mem_NL`; (d) `PATH_NLComplete`; (e) `TQBF_mem_PSPACE`; (f) `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`. Second uses inside the delivery: (b) uses (a)'s decider bank and H12's stop rule; (b) and (d) use (c)'s `WalkLe` and `rawEdge` |
-| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`) | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round.** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
+| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`); head envelopes `Clean.envelope` (a clean module's heads stay within `B \|arg\|` cells of the origin at every time), `host_call_envelope` (within `t` cells up to time `t` of a call) and `host_clean_envelope` (`host_clean` with the envelope `B \|arg\|` throughout the call), the coarse envelopes from the time bounds and the unit head moves of `Turing.MultiTapeTM.workTapePos_step_le` | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round; head-envelope clauses added 2026-11-06 (gate 03l round 2, finding 1).** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
 
 **The received ARM machinery, H7–H13** (registered 2026-10-14: the ARM fill gate's round 2,
 finding 5; user decision 3). The rows' public contracts, with file and line, are in

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/replay.log =====

# replay 2026-11-06T00:49:44Z HEAD=73751f5747d8c0a57aba9939cac8bb16f87ba2ba BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 tree=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans; order=replay-order.txt (downstream2.py of the changed modules, DOWN, + audits/pass-shelat/Checks)
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/SAT rc=0 38s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalNP rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReduction rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix rc=0 1s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLipton rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily rc=0 13s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UniformTableau rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceTableau rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifier rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSound rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSoundInput rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerComplete rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSigma rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Meyer rc=0 7s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CookLevin/Hardness rc=0 385s errors=0 sorry=0
TCSlib/Complexity/ClassNP/Tautology rc=0 10s errors=0 sorry=0
TCSlib/Complexity/ClassNP rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassOracle/SATOracle rc=0 2s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Inclusions rc=0 29s errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHard rc=0 12s errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBF rc=0 28s errors=0 sorry=21
TCSlib/Complexity/Randomized/Inclusions rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/Reductions rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/PTMEquiv rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPOperator rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPAmplify rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPTIMEThreshold rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoin rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoinHalting rc=0 13s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primality rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Matching rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/NPPoly rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/RPExpected rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Yap rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPEquiv rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHosts rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHostsClasses rc=0 45s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroP rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPPIT rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPReduce rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 71s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 42s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 71s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 23s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 8s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 7s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 3s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 4s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 2s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 125s errors=0 sorry=0
# done 2026-11-06T01:12:45Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/axioms.log =====

# Axiom prints, gate 03 repair batch, HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba, tree /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans (after replay.log)
# Input: axrun/all.lean, generated by g03l-ax/axgen.py over every changed .lean file (changed-lean.txt): 549 #print lines (548 names).
# Base comparison: axrun/base.lean (the same list without the 10 new lemmas) against the untouched #203 tree g03l-oleans (read-only; #203 = BASE in Lean code), axrun/base.out.
# Item B's eight simps equations and the three envelope lemmas: axioms-03l.log.

## Comparison (axcmp.py)
HEAD prints: 548; base prints: 538
sorryAx at HEAD: 100 ; at base: 100
non-standard axioms other than sorryAx at HEAD: []
new names: 10
  NEW TCSlib.Cryptography.AbortRetry.attempt_eq ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq_attempt ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq_nil ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.Candidates.rejectBlocksL_eq []
  NEW TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL ['Quot.sound']
  NEW TCSlib.Cryptography.Protocol.proverBounded_iff ['propext']
  NEW Turing.ModuleHost.Clean.envelope ['Classical.choice', 'Quot.sound', 'propext']
  NEW Turing.ModuleHost.host_call_envelope ['Classical.choice', 'Quot.sound', 'propext']
  NEW Turing.ModuleHost.host_clean_envelope ['Classical.choice', 'Quot.sound', 'propext']
changed axiom sets: 0
missing at HEAD: []
TCSlib.Cryptography.zk_proof_of_witnessRelation ['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']
TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp ['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']

## HEAD output (axrun/all.out)
'Turing.ModuleHost.first_halt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.live_prefix' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.clean_iff' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.Clean.envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.clean_install' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.clean_emit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.request_budget' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.state_eq' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.entry_eq' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.hostTM_step_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.guard_add' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.host_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_clean_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_eq_uprob' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofFn_ofString_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofString_id_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.FunFamily.blocks_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofFn_blocks_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_outLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.Easy.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.eval_yaoBlocks' depends on axioms: [propext]
'TCSlib.Cryptography.eval_yaoRounds' depends on axioms: [propext]
'TCSlib.Cryptography.yaoBlocks_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OneWay.invProb_prodFun_le_yaoTry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.claim_38_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.weak_to_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.strong_prod_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.weak' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_ofString_id_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_strongOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_weakOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_worstCaseOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PermFamily.toFunFamily_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_and_eq_mul_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_sub_div_le_uprob_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_le_uprob_subtype_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_subtype_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_sub_one_div_pow_le_exp_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.claim_36_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.exp_neg_le_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.claim_36_2_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.primesPairEquiv_apply_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_card_primes_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_prime' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.q_prime' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_lt' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.q_lt' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_ne_q' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.totient_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.one_lt_totient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.ext' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.isEmpty_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.decodeDistinctPrimes_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.encodeDistinctPrimes_of_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rejectBlocksL_eq' does not depend on any axioms
'TCSlib.Cryptography.Candidates.rejectBlocksL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_rejectBlocksL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.WellFormedIndex.length_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.dlP_lt_two_pow' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.val_lt_two_pow_dlW' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coprime_dlG_dlP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coe_expUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.orderOf_expUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expDec_expEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expEnc_of_expDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expF_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.exists_fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expValid_dlDefaultIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expGenFun_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expGen_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.Candidates.sampleBelowL_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sampleBelowL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_index_of_lt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_D' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.SafePrimeValid.expValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlAssumption_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_oneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.IsGenerator.orderOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_dlog' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlog_expo' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.two_mul_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.neg_one_ne_one_units' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pow_half_eq_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pow_mem_QR_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sq_eq_pow_two_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.neg_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlLoop_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlQueries_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlQueries_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlLoop_eq_dlBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlBits_pow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_trial_ge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_shiftInverter_ge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_dlInverter_ge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.good_instances' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.FullGroupValid.expValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.halfPred_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.halfStr_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_halfStr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_hardCore' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.safe_ne_two' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.five_le_safe' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.safe_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.card_QR_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.mem_QR_iff_pow_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.orderOf_eq_of_mem_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.zpowers_eq_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eq_QR_of_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.card_sqrt_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_sqTo_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_sq_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_of_uprob_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sq_generator' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.eval_ddhLen' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.length_ddhTuple' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ddhExpo_statClose' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.constSelector_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egUnit_pos' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.egUnit_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egEncRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egEnc_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egDecStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egDecStr_apply' depends on axioms: [propext, sorryAx, Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egSquareGen_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egGroupGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGenMachine_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGen_valid' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGen_wellFormed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_secure' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_outLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inv_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_easy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.modulusBits_eq_fmult' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.factorProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coins_oneCallFactorer' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.oneCallFactorer_runAtL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eval_fmultWeakPoly' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.fmult_weakOneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eval_fmultBlocks' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.fmult_prod_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.exists_plantFactorer' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.samplePairOut_eq_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_samplePairRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringGen_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_spec' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_collectionFactorer' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.collectionFactorer_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_rsaPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.mul_inv_val_modEq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.val_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaF_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaDec_rsaEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaEnc_of_rsaDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleUnitL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.N_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.e_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.d_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaN_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaE_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaValid_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_unitSampleStr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaInvRaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rsaGenErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_rsaBreaker' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaBreaker_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaFromFactorStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_rsaFromFactorer' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaFromFactorer_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_rsaProb' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsa_imp_factoring' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.BlumDistinctPrimes.ne_two' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.oddFactorProb_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_factoring' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_ne_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabin_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_oddGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.oddGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_rabinIndexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinMod_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinDec_rabinEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinEval_spec' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rabinErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinFactorRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinFactorer_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.BlumValid.exists_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sqTo_bijective_of_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blum_val_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumDec_blumEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumF_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumInv_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinRootRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumInverter_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_two_mul_card_primes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_mrExp_mul_mrOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrOdd_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrOdd_mul_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mem_mrLiars' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.MRLiar.ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.millerRabin_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_two_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.statClose_samplePrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.bitsToNat_eq_listToNat' does not depend on any axioms
'TCSlib.Cryptography.NumberTheory.eval_samplePrimeCoins' depends on axioms: [propext]
'TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.simulate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_const_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perfectZK_zeroRounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_attempt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.exists_retrySimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.firstHit_map_getD_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.statClose_retry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.uprob_not_ne_nil_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_exp_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.inv_pow_le_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Isomorphic.refl' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.Isomorphic.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Isomorphic.trans' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.isomorphic_permGraph' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.permGraph_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_isomorphic_both' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_honest_reply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decGraphAt_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decGraph_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.instanceVertices_length_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.instanceVertexCount_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encInstance_mem_Liso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encInstance_mem_Lniso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_mem_Lniso_of_mem_Liso' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Riso_witnessRelation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.permCoinLen_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_samplePerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_mul_permFailBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_guess' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_cheat_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_rep_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gni_rep_cheat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_honest_reply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProver_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProverRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocolRep_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gniProver_next_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_outV_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.ofFn_vTapeSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.permCoinLen_le_tape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_outV_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.ofFn_giBitEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giCoinEquiv_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giCoinEquiv_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.exec_repViews' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.length_Vs' depends on axioms: [propext]
'TCSlib.Cryptography.GI.getD_Vs_even' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.getD_Vs_odd' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOf_congr' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOfFin_prefixLT' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOfFin_init_prefixLE' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.prefixLE_last' does not depend on any axioms
'TCSlib.Cryptography.GI.giVerifierRep_next_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_mid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_end' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_end_enc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProverRep_next_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProverRep_next_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProtocolRep_outV' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.repViews_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.repViews_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.honest_views' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giRep_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giRep_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.encodeMsgs_nil' does not depend on any axioms
'TCSlib.Cryptography.Strategy.encodeMsgs_cons' does not depend on any axioms
'TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.Efficient.exists_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.ReadsPrefix.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.moverIsV_true' does not depend on any axioms
'TCSlib.Cryptography.moverIsV_false' does not depend on any axioms
'TCSlib.Cryptography.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.exec_succ' does not depend on any axioms
'TCSlib.Cryptography.exec_length' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Protocol.proverBounded_iff' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.ProverBounded.mono' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.withV_V' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_P' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_rounds' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_verifierFirst' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_self' does not depend on any axioms
'TCSlib.Cryptography.Protocol.outV_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outP_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.transcript_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_withV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.exists_proverCoins_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.exists_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_witnessLanguage' does not depend on any axioms
'TCSlib.Cryptography.mem_witnessSet' does not depend on any axioms
'TCSlib.Cryptography.WitnessRelation.eq_witnessLanguage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_witnessRelation_of_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.EfficientProverProofErr.efficientProverProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.EfficientProverProof.exists_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_outV' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.npProtocol_readsPrefix' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.npProtocol_efficientV' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_efficientP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_proverBounded' depends on axioms: [propext]
'TCSlib.Cryptography.npProtocol_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NP_subset_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.coinLen_pullback' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.pullback_outV' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.pullback_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_levinReduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_owp_levinReduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.threeColorable_ofSimpleGraph_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_L3COL_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encGraph_mem_L3COL_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_edgeList_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeOf_adj' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.exists_edgeOf_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeAt_eq_some_edgeOf' depends on axioms: [propext]
'TCSlib.Cryptography.edgeAt_adj' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeAt_isSome' does not depend on any axioms
'TCSlib.Cryptography.edgeAt_eq_none_iff' depends on axioms: [propext]
'TCSlib.Cryptography.threeColorable_of_edgeCount_eq_zero' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeCount_pos_of_not_threeColorable' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exp_neg_le_inv_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decColor_encColor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encColor_getD_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.padColor_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.sampleEdgeIdx_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeIdxOfMsg_edgeMsg' depends on axioms: [propext]
'TCSlib.Cryptography.edgeIdxOfMsg_lt' does not depend on any axioms
'TCSlib.Cryptography.statClose_samplePerm3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_sampleEdgeIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.msgAt_encodeMsgs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.committedColor_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_bad_edge' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_col_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colWellFormed_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProverRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_multiCom_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.R3COL_witnessRelation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_efficientProverProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_interactiveProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.card_colorPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perm3_ext_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colorPairEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.simColorsW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.firstSome_eq_none_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_colSimTruncW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptH_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptH_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimTruncH_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_colSimTruncH' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colSimHyb_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colSimHyb_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimRed_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_hvzk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zeroKnowledgeProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/seal.log =====

## Part 1: consumers of TCSlib.Cryptography.Protocol.ProverBounded (whole files sealed)

TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (2 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_InteractiveProofs_sealed_control.lean:236:22: error: Function expected at
    ctl: TCSlib_Cryptography_ZeroKnowledge_InteractiveProofs_sealed_control.lean:470:2: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/NP.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_NP_sealed_control.lean:279:8: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (3 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:928:39: error: Type mismatch
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:932:42: error: Type mismatch
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:938:3: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (3 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:611:13: error: Application type mismatch: The argument
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:612:2: error: No goals to be solved
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:882:40: error: Function expected at
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_Soundness_sealed_control.lean:322:21: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_SoundnessRepGI_sealed_control.lean:478:21: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

## Part 2: new proofs that read another file's definitions (copies in a SealTest namespace)

TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean: Clean.envelope, host_call_envelope, host_clean_envelope
  seal: ofWords stateWord runFrom step
  sealed current: PASS
  control (Clean.envelope with the seam's head position read by `rfl` through `Cfg.ofWords`): FAIL (1 error lines); expected fail: as expected
    ctl: ModuleHost_envelopes_sealed_control.lean:29:89: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)

TCSlib/Cryptography/ZeroKnowledge/Defs.lean: attempt_eq, retry_eq, retry_eq_attempt, retry_eq_nil
  seal: firstIdx layout inParam inArg inCoins output coinLen
  sealed current: PASS
  control (the copies plus one `rfl` read of `firstIdx` (seal-active check)): FAIL (1 error lines); expected fail: as expected
    ctl: Defs_AbortRetry_sealed_control.lean:41:45: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)

TCSlib/Cryptography/Candidates/DiscreteLog.lean: sampleBelowL_eq_rejectBlocksL
  seal: rejectBlocksL
  sealed current: PASS
  control (the lemma proved by `funext r; rfl`, reading `rejectBlocksL` through its body): FAIL (1 error lines); expected fail: as expected
    ctl: DiscreteLog_sampleBelowL_sealed_control.lean:15:2: error: Tactic `rfl` failed: The left-hand side
  the same control unsealed: PASS (so its sealed failure is due to the seal)


## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/lint.log =====

# Lint (check 4), HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba vs BASE 092083cd10be7a284db4e97fcf42eddb8296edf7 (archive in g03batch/basetree)
# lint.sh: scripts/style_lint.py on the 21 changed .lean files; scripts/campaign_style_lint.py --check8b per directory, filtered to them.
# Normalized diff base -> head (line numbers masked):
#   26c26,27
#   < INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          548 lines; 16 public / 13 private declarations
#   ---
#   > INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines > target 600
#   > INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines; 19 public / 13 private declarations
#   28,29c29,30
#   < INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                929 lines > target 600
#   < INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                929 lines; 44 public / 6 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines > target 600
#   > INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines; 44 public / 6 private declarations
#   45,56c46,57
#   < INFO  TCSlib/Cryptography/Candidates/Concrete.lean             561 lines; 39 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          710 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          710 lines; 65 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  585 lines; 45 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              890 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              890 lines; 60 public / 4 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/Factoring.lean            691 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/Factoring.lean            691 lines; 47 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/RSA.lean                  914 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/RSA.lean                  914 lines; 85 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/Rabin.lean                994 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/Rabin.lean                994 lines; 96 public / 0 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/Candidates/Concrete.lean             570 lines; 40 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines; 66 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  597 lines; 45 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines; 60 public / 4 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines; 47 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines; 85 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines; 96 public / 0 private declarations
#   58,60c59,61
#   < INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          308 lines; 11 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          901 lines > target 600
#   < INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          901 lines; 30 public / 30 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          311 lines; 11 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines > target 600
#   > INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines; 30 public / 30 private declarations
#   67c68
#   < WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       10 public def(s) without a lemma beside them (check 8): Efficient, ProverBounded, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
#   ---
#   > WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       9 public def(s) without a lemma beside them (check 8): Efficient, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
#   73,86c74,87
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              687 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              687 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        326 lines; 17 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   489 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  981 lines; 68 public / 7 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       464 lines; 49 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 544 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                763 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                763 lines; 23 public / 5 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            423 lines; 40 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            923 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            923 lines; 34 public / 12 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           790 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           790 lines; 42 public / 3 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines; 34 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  985 lines; 68 public / 7 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       473 lines; 50 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 550 lines; 30 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines; 23 public / 5 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            424 lines; 40 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines; 34 public / 12 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines; 42 public / 3 private declarations
#   89,90c90,91
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        326 lines; 17 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   489 lines; 30 public / 0 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
#   94,98c95,99
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          423 lines; 40 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          923 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          923 lines; 34 public / 12 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         790 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         790 lines; 42 public / 3 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          424 lines; 40 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines; 34 public / 12 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines; 42 public / 3 private declarations
# => no new WARN/FAIL; Interaction.lean's check-8 list loses ProverBounded; ModuleHost.lean passes the 600-line target (INFO, 663 lines); the rest are line counts.

### HEAD raw
### scripts/style_lint.py on the changed .lean files

1 findings in 21 files



















TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:723: `colProtocol_sound` proof is 99 lines, no **Proof sketch.**

### scripts/campaign_style_lint.py --check8b, per directory, filtered to the changed files
INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines; 19 public / 13 private declarations
WARN  TCSlib/Cryptography/Asymptotic/OneWay.lean                5 public def(s) without a lemma beside them (check 8): Easy, LengthRegular, OneWayPermutation, strOutLen, yaoRounds
INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines > target 600
INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines; 44 public / 6 private declarations
FAIL  TCSlib/Cryptography/Candidates/ElGamal.lean              line 749: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 145: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 347: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 532: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 805: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 892: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 927: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 951: `sorry` without a proof sketch in the preceding docstring
WARN  TCSlib/Cryptography/Candidates/Concrete.lean             1 public def(s) without a lemma beside them (check 8): default
WARN  TCSlib/Cryptography/Candidates/DiscreteLog.lean          11 public def(s) without a lemma beside them (check 8): DLAssumption, DLHard, FullLength, FullLengthExcept, SafePrimeValid, WellFormedIndex, dlDefaultIndex, dlG, dlM, expSampleRaw, expUnit
WARN  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  9 public def(s) without a lemma beside them (check 8): FullDLAssumption, FullGroupValid, IsGenerator, dlInverter, dlRoot, halfBit, halfOracle, majOracle, shiftInverter
WARN  TCSlib/Cryptography/Candidates/ElGamal.lean              15 public def(s) without a lemma beside them (check 8): DDHAssumption, Secure, challenge, ddhLen, ddhRandom, ddhReal, ddhTuple, egCanon, egEncParts, egEncRaw, egGenCoins, egGenParts, egGenRaw, egGroupGenRaw, egGroupParts
WARN  TCSlib/Cryptography/Candidates/Factoring.lean            7 public def(s) without a lemma beside them (check 8): FactoringAssumption, fmultBlocks, fmultWeakPoly, plantFactor, prodInverter, samplePairRaw, samplePrimeL
WARN  TCSlib/Cryptography/Candidates/RSA.lean                  19 public def(s) without a lemma beside them (check 8): RSAAssumption, RSAValid, rsaBlock, rsaEncVal, rsaFromFactorRaw, rsaGenCoins, rsaGenErr, rsaGenOut, rsaGenParams, rsaGenRaw, rsaIndexOf, rsaInput, rsaInvRaw, rsaPermAt, rsaSampleCoins, rsaSampleRaw, rsaTrapOf, rsaTrials, unitSampleStr
WARN  TCSlib/Cryptography/Candidates/Rabin.lean                28 public def(s) without a lemma beside them (check 8): BlumDensity, BlumFactoringAssumption, BlumValid, blumDefault, blumEnc, blumEncVal, blumInvNat, blumInvRaw, blumPermAt, blumSampleRaw, oddDefault, rabinEnc, rabinErr, rabinF, rabinFactorRaw, rabinFactorStep, rabinGenCoins, rabinGenOut, rabinGenParams, rabinGenRaw, rabinIndexOf, rabinPrimeCoins, rabinRootRaw, rabinRootStep, rabinSampleRaw, rabinTrials, samplePrimePL, smallDistinctPrimes
INFO  TCSlib/Cryptography/Candidates/Concrete.lean             570 lines; 40 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines > target 600
INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines; 66 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  597 lines; 45 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines > target 600
INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines; 60 public / 4 private declarations
INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines > target 600
INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines; 47 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines > target 600
INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines; 85 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines > target 600
INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines; 96 public / 0 private declarations
WARN  TCSlib/Cryptography/NumberTheory/Primality.lean          6 public def(s) without a lemma beside them (check 8): MRLiar, chunk, listToNat, mrExp, mrLiars, samplePrimeCoins
INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          311 lines; 11 public / 3 private declarations
INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines > target 600
INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines; 30 public / 30 private declarations
FAIL  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  facade does not import child module `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete`
FAIL  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  facade does not import child module `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs`
WARN  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              4 public def(s) without a lemma beside them (check 8): HVZK, PerfectZKAbort, StatZK, ZK
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        2 public def(s) without a lemma beside them (check 8): giBitEquiv, vTapeSplit
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   4 public def(s) without a lemma beside them (check 8): Hfun, Vs, giRepCoins, honestH
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  12 public def(s) without a lemma beside them (check 8): Liso, Lniso, coinSlice, gniProtocolRep, gniProver, instanceG, instanceG, permFailBound, prefixLE, prefixLT, samplePerm, wellFormedInstance
WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       9 public def(s) without a lemma beside them (check 8): Efficient, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
WARN  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 3 public def(s) without a lemma beside them (check 8): IP, witnessLanguage, witnessSet
WARN  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                1 public def(s) without a lemma beside them (check 8): LevinNPHard
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            9 public def(s) without a lemma beside them (check 8): Graph.ofSimpleGraph, L3COL, ProperColoring, R3COL, edgeList, edgeMsg, perm3Equiv, sampleIdx, samplePerm3
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            7 public def(s) without a lemma beside them (check 8): challengesBefore, challengesUpTo, colCoinSlice, colCommit, colIterations, colOpen, colProtocolRep
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           17 public def(s) without a lemma beside them (check 8): colRealView, colSim, colSimAttempt, colSimAttemptH, colSimAttemptPlanted, colSimAttemptStr, colSimAttemptW, colSimBlock, colSimCoins, colSimRed, colSimTrunc, colSimTruncH, colSimTruncW, pair6Equiv, sampleColorPair, simCoinsEquiv, simColors
INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines; 34 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  985 lines; 68 public / 7 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       473 lines; 50 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 550 lines; 30 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines; 23 public / 5 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            424 lines; 40 public / 3 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines; 34 public / 12 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines; 42 public / 3 private declarations
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        2 public def(s) without a lemma beside them (check 8): giBitEquiv, vTapeSplit
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   4 public def(s) without a lemma beside them (check 8): Hfun, Vs, giRepCoins, honestH
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          9 public def(s) without a lemma beside them (check 8): Graph.ofSimpleGraph, L3COL, ProperColoring, R3COL, edgeList, edgeMsg, perm3Equiv, sampleIdx, samplePerm3
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          7 public def(s) without a lemma beside them (check 8): challengesBefore, challengesUpTo, colCoinSlice, colCommit, colIterations, colOpen, colProtocolRep
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         17 public def(s) without a lemma beside them (check 8): colRealView, colSim, colSimAttempt, colSimAttemptH, colSimAttemptPlanted, colSimAttemptStr, colSimAttemptW, colSimBlock, colSimCoins, colSimRed, colSimTrunc, colSimTruncH, colSimTruncW, pair6Equiv, sampleColorPair, simCoinsEquiv, simColors
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          424 lines; 40 public / 3 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines; 34 public / 12 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines; 42 public / 3 private declarations

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/statements.txt =====

# Statement diff: decls.py (copied from g03l-fix) over every changed .lean file, BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 vs HEAD=73751f5747d8c0a57aba9939cac8bb16f87ba2ba
# Normalized statement text (comments stripped) of every public declaration, compared by full name.

## Summary: 10 added, 2 changed, 0 removed

## Added
- Turing.ModuleHost.Clean.envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:239)
    theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ} (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
- Turing.ModuleHost.host_call_envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:567)
    theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M)) (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) : ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos j| ≤ (t : ℤ)
- Turing.ModuleHost.host_clean_envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:642)
    theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M)) (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ) (h : Clean (M i) f g B) (x arg pre : List Bool) : ∃ t, 0 < t ∧ t ≤ B arg.length ∧ (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state ≠ some (.inl c)) ∧ (hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t = {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧ ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos j| ≤ (B arg.length : ℤ)
- TCSlib.Cryptography.Candidates.rejectBlocksL_eq (theorem, TCSlib/Cryptography/Candidates/Concrete.lean:525)
    theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) : rejectBlocksL E k B T r = (List.range T).findSome? fun t => if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k)) else none
- TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL (theorem, TCSlib/Cryptography/Candidates/DiscreteLog.lean:476)
    theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) : sampleBelowL m k B T = rejectBlocksL (· < m) k B T
- TCSlib.Cryptography.AbortRetry.attempt_eq (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:315)
    theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) : attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) [] (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take (S.coinLen (NUPPT.inParam w).length)))
- TCSlib.Cryptography.AbortRetry.retry_eq (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:334)
    theorem retry_eq (S : NUPPT) (w : List Bool) : retry S w = if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length < (NUPPT.inParam w).length then attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) else []
- TCSlib.Cryptography.AbortRetry.retry_eq_attempt (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:347)
    theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ} (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ []) (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i
- TCSlib.Cryptography.AbortRetry.retry_eq_nil (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:359)
    theorem retry_eq_nil {S : NUPPT} {w : List Bool} (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = []
- TCSlib.Cryptography.Protocol.proverBounded_iff (theorem, TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:338)
    theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : π.ProverBounded R B ↔ ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length

## Changed (both by ruling R-03e-r2-1 (A), item C #4)
- TCSlib.Cryptography.zk_proof_of_witnessRelation (TCSlib/Cryptography/ZeroKnowledge/NP.lean:679->682)
    OLD: theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
    NEW: theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
- TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp (TCSlib/Cryptography/ZeroKnowledge/NP.lean:698->701)
    OLD: theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧ ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
    NEW: theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧ ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)

## Removed
(none)

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/maintainer-recheck.log =====

# maintainer re-check at 73751f5747d8c0a57aba9939cac8bb16f87ba2ba: 8 key modules, one at a time in import order, on a copy of the worker's tree
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
audits/pass-shelat/Checks rc=0 121s errors=0 sorry=0
# done 2026-11-06T01:22:50Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/base-sync.log =====

# base-sync 2026-11-06T00:22:41Z BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 tree=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans (copy of g03l-oleans, #203 Lean files)
TCSlib/Complexity/Randomized/PPT rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 2s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 75s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 10s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 63s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 77s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 10s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 7s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 3s errors=0 sorry=0
# done 2026-11-06T00:32:55Z

## ===== TCSlib/Cryptography/Candidates/DiscreteLog.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.Concrete
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.NumberTheory.Units
import Mathlib.Data.Nat.Size
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The discrete-logarithm assumption and the discrete-logarithm collection

The discrete-logarithm material of [PS10, §2.8]: the *discrete-log assumption* for a family
of prime-order groups [PS10, Assumption 52.2] and the collection
`DL = {f_{q,g}(x) = g^x : Z_q → G_q}` with indices `(q, g)`, which is a collection of
one-way functions under that assumption [PS10, Theorem 52.3].

**The groups.** Following the text's own instantiation (p. 52, "one usually picks a prime of
the form `p = 2q + 1` … and then sets `G` to be the subgroup of squares in `Z_p^*`"), the
prime-order group `G_q` is the subgroup of squares of `Z_p^* = (ZMod p)ˣ` for a *safe prime*
`p = 2q + 1`. A group instance is the string index `⟨p, ⟨m, g⟩⟩` of three `n`-bit numerals:
the prime `p`, the order `m` of the group generated by `g` (the domain of the exponentiation
is `Z_m`), and the generator `g` (`ExpValid`: `orderOf g = m` in `Z_p`). The same index
format serves the full-group collection of `TCSlib.Cryptography.Candidates.DiscreteLogHardcore`
(`m = p − 1`, `g` a generator of `Z_p^*`, [PS10, Lemma 84.1]) and the El Gamal keys of
`TCSlib.Cryptography.Candidates.ElGamal`, so the exponentiation collection is built once,
generically over a validity predicate `V` on indices: `expCollection`.

**The sampler of instances.** The text samples `q ← Π_n; g ← Gen_{G_q}` and notes (p. 52–53)
that no efficient procedure for safe primes is known. Foundation decision D10 and the
deviation register (#15) replace the ideal sampler by an explicit *instance generator*
`ExpGroupGen V`: a PPT `Gen(1^n)` whose outputs, from a threshold `n₀` on, are valid indices
of three `n`-bit numerals. The assumption and the theorems are relative to the generator;
every statement about machines is conditional on the arithmetic bundle `ArithmeticFP` (D11).
Below the threshold the collection's own generator `expGen` outputs the fixed valid instance
`dlDefaultIndex = ⟨3, ⟨2, 2⟩⟩`, so that every generated index is valid and the sampler's
outputs decode at every parameter (`Collection.sample_spec`, run-3 audit P3-1); the
collection `expCollection H G hV` therefore takes the validity bridge `hV : ∀ i, V i → ExpValid i`
as an argument.

**Full-length primes.** Where a proof divides by `q` or `p − 1` (Lemma 84.1's range reduction,
the `1/q` term of Theorem 107.3) the proofs use full length `2^{n−1} ≤ p` (a convenience: the
hypothesis is dispensable in both headline theorems, gate 03f1 review, M1). This is
demanded only *except on a negligible set of coins* (`ExpGroupGen.FullLengthExcept δ` with
`Negligible δ`): a strict-PPT generator may fall back to a fixed instance when its rejection
loop fails (D10), and demanding full length on every coin string (`ExpGroupGen.FullLength`)
would require a deterministic polynomial-time construction of full-length primes of the
required form, which is not known (run-3 audit P8-2). The rejection sampler of numbers below
`m` (`sampleBelowL`) is within `(1/2)^n` of uniform (`statClose_sampleBelowL`, D10), the
closeness fact shared by the collection's domain sampler and the El Gamal samplers.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the adversary of Assumption 52.2 receives `⟨1^n, ⟨i, g^x⟩⟩`
with the whole index `i = ⟨p, ⟨q, g⟩⟩` (the text passes `g^x` only, source error 8), the
exponent `x ← Z_q` is ideal uniform in the experiment while the honest domain sampler is a
truncated rejection sampler within `2^{-n}` of uniform (D10), the answer is read as an
`n`-bit numeral (wrong length = failure, D5), "`Pr[…] < ε(n)` for a negligible `ε`" is
"`Pr[…]` is negligible", and the ideal "`q ← Π_n; g ← Gen_{G_q}`" is the law of the instance
generator. Theorem 52.3's `R_i = G_p`, `f_{p,g}` are read as `G_q`, `f_{q,g}` (source
error 8) and `k` as `n`.

## Main definitions

* `TCSlib.Cryptography.Candidates.dlP`, `dlM`, `dlG`, `dlW`, `WellFormedIndex` — reading the
  index `⟨p, ⟨m, g⟩⟩`; `TCSlib.Cryptography.Candidates.ExpValid` — valid indices.
* `TCSlib.Cryptography.Candidates.expOrd`, `expEnc`, `expDec`, `expF`, `expEval` — the
  domain `Z_m`, its encoding, the function `x ↦ g^x mod p` and its evaluator.
* `TCSlib.Cryptography.Candidates.ExpGroupGen` — instance generators;
  `ExpGroupGen.dlProb`, `ExpGroupGen.DLHard` — the discrete-log experiment and hardness;
  `ExpGroupGen.FullLength`, `ExpGroupGen.FullLengthExcept` — full-length primes (on every
  coin string / except on a set of coins of probability `δ n`).
* `TCSlib.Cryptography.Candidates.sampleBelowL`, `expSampler`, `dlDefaultIndex`, `expGen`,
  `expCollection` — the exponentiation collection of an instance generator.
* `TCSlib.Cryptography.Candidates.SafePrimeValid`, `SafePrimeGen`,
  `TCSlib.Cryptography.Candidates.DLAssumption` — [PS10, Assumption 52.2];
  `TCSlib.Cryptography.Candidates.dlCollection` — the collection `DL` [PS10, Theorem 52.3].

## Main results

* `TCSlib.Cryptography.Candidates.expF_injective` — `x ↦ g^x` is injective on `Z_m` at a
  valid index (the remark after [PS10, Theorem 52.3]; Claim-53.2 of the inventory, proved).
* `TCSlib.Cryptography.Candidates.expEval_spec`, `expDec_expEnc` — the collection data
  (proved).
* `TCSlib.Cryptography.Candidates.statClose_sampleBelowL` — the rejection sampler of numbers
  below `m` is within `(1/2)^n` of uniform (D10);
  `ExpGroupGen.FullLength.fullLengthExcept`, `ExpGroupGen.FullLength.exists_fullLengthExcept` —
  full length on every coin string is the `δ = 0` case (proved).
* `TCSlib.Cryptography.Candidates.expCollection_invProbAt_le` — inverting the collection is
  the discrete-log experiment; `expCollection_sampleClose`, `expCollection_oneWay`.
* `TCSlib.Cryptography.Candidates.dlCollection_oneWay` — [PS10, Theorem 52.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.8: Definition 52.1, Assumption 52.2, Theorem 52.3 and the remarks on pp. 52–53.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Group instances `⟨p, ⟨m, g⟩⟩` -/

/-- The prime `p` read from the index `⟨p, ⟨m, g⟩⟩`. -/
def dlP (i : List Bool) : ℕ := listToNat (pairFstD i)

/-- The group order `m` read from the index `⟨p, ⟨m, g⟩⟩` (the domain of the exponentiation
is `Z_m`; `m = q` for the prime-order groups, `m = p − 1` for `Z_p^*`). -/
def dlM (i : List Bool) : ℕ := listToNat (pairFstD (pairSndD i))

/-- The generator `g` read from the index `⟨p, ⟨m, g⟩⟩`. -/
def dlG (i : List Bool) : ℕ := listToNat (pairSndD (pairSndD i))

/-- The numeral width of an index: the width of the numeral of `p` (all group elements are
encoded with this width). -/
def dlW (i : List Bool) : ℕ := (pairFstD i).length

/-- An index is *well formed at parameter `n`* when it is a pair `⟨a, ⟨b, c⟩⟩` of three
`n`-bit numerals (the text's "`p` of length `n`"). -/
def WellFormedIndex (n : ℕ) (i : List Bool) : Prop :=
  ∃ a b c : List Bool, i = pairEncode a (pairEncode b c) ∧ a.length = n ∧ b.length = n ∧ c.length = n

/-- The width of a well-formed index is `n`. -/
theorem WellFormedIndex.dlW_eq {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) : dlW i = n := by
  obtain ⟨a, b, c, rfl, ha, -, -⟩ := h
  simp [dlW, ha]

/-- A well-formed index at parameter `n` has length `5n + 4`. -/
theorem WellFormedIndex.length_eq {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) :
    i.length = 5 * n + 4 := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := h
  simp only [length_pairEncode, ha, hb, hc]
  ring

/-- `p < 2^{dlW i}`: the prime fits its numeral. -/
theorem dlP_lt_two_pow (i : List Bool) : dlP i < 2 ^ dlW i := listToNat_lt_two_pow _

/-- An index `⟨p, ⟨m, g⟩⟩` is *valid* when `p` is prime, `0 < m < p`, `0 < g < p`, and `g` has
order exactly `m` in `Z_p` (so `x ↦ g^x` is a bijection of `Z_m` onto the subgroup generated
by `g`, [PS10, Definition 52.1]). (Not efficiently decidable from the index — generators only
ever output valid indices.) -/
def ExpValid (i : List Bool) : Prop :=
  (dlP i).Prime ∧ 0 < dlM i ∧ dlM i < dlP i ∧ 0 < dlG i ∧ dlG i < dlP i ∧
    orderOf ((dlG i : ℕ) : ZMod (dlP i)) = dlM i

noncomputable instance : DecidablePred ExpValid := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The order of the domain at an index: `m` for a valid index and `1` otherwise (so that the
domain `Z_m` is always a finite group). -/
noncomputable def expOrd (i : List Bool) : ℕ := if ExpValid i then dlM i else 1

instance (i : List Bool) : NeZero (expOrd i) := by
  unfold expOrd
  split_ifs with h
  · exact ⟨h.2.1.ne'⟩
  · exact ⟨one_ne_zero⟩

/-- `expOrd` of a valid index is `m`. -/
theorem expOrd_of_valid {i : List Bool} (h : ExpValid i) : expOrd i = dlM i := if_pos h

/-- `expOrd` of an invalid index is `1`. -/
theorem expOrd_of_not_valid {i : List Bool} (h : ¬ ExpValid i) : expOrd i = 1 := if_neg h

/-- The order of the domain fits the numeral width: `expOrd i ≤ 2^{dlW i}`. -/
theorem expOrd_le_two_pow (i : List Bool) : expOrd i ≤ 2 ^ dlW i := by
  unfold expOrd
  split_ifs with h
  · exact (h.2.2.1.trans (dlP_lt_two_pow i)).le
  · exact Nat.one_le_two_pow

/-- The residue of an element of the domain fits the numeral width. -/
theorem val_lt_two_pow_dlW (i : List Bool) (x : ZMod (expOrd i)) : x.val < 2 ^ dlW i :=
  lt_of_lt_of_le (ZMod.val_lt x) (expOrd_le_two_pow i)

/-- `g` is coprime to `p` at a valid index (`0 < g < p` and `p` prime). -/
theorem coprime_dlG_dlP {i : List Bool} (h : ExpValid i) : Nat.Coprime (dlG i) (dlP i) :=
  ((Nat.Prime.coprime_iff_not_dvd h.1).2 (Nat.not_dvd_of_pos_of_lt h.2.2.2.1 h.2.2.2.2.1)).symm

/-- The generator `g` as a unit of `Z_p` at a valid index. -/
noncomputable def expUnit {i : List Bool} (h : ExpValid i) : (ZMod (dlP i))ˣ :=
  ZMod.unitOfCoprime (dlG i) (coprime_dlG_dlP h)

/-- The value of `expUnit` is `g mod p`. -/
theorem coe_expUnit {i : List Bool} (h : ExpValid i) :
    (expUnit h : ZMod (dlP i)) = ((dlG i : ℕ) : ZMod (dlP i)) := ZMod.coe_unitOfCoprime _ _

/-- The order of the unit `g` is `m` [PS10, Definition 52.1, "`g` is a generator"]. -/
theorem orderOf_expUnit {i : List Bool} (h : ExpValid i) : orderOf (expUnit h) = dlM i := by
  rw [← orderOf_units, coe_expUnit]
  exact h.2.2.2.2.2

/-! ## The domain `Z_m`, its encoding and the function `x ↦ g^x` -/

/-- The string encoding of `x ∈ Z_m`: its residue as a numeral of the index width. -/
noncomputable def expEnc (i : List Bool) (x : ZMod (expOrd i)) : List Bool := natToList (dlW i) x.val

/-- The decoder of `Z_m`: a numeral of the index width reading as a number below `m`. -/
noncomputable def expDec (i : List Bool) (w : List Bool) : Option (ZMod (expOrd i)) :=
  if w.length = dlW i ∧ listToNat w < expOrd i then some ((listToNat w : ℕ) : ZMod (expOrd i))
  else none

/-- Decoding inverts encoding (the clause `decD_encD` of `Collection`). -/
theorem expDec_expEnc (i : List Bool) (x : ZMod (expOrd i)) : expDec i (expEnc i x) = some x := by
  have hl : listToNat (expEnc i x) = x.val := listToNat_natToList (val_lt_two_pow_dlW i x)
  rw [expDec, if_pos ⟨by simp [expEnc], by rw [hl]; exact ZMod.val_lt x⟩, hl,
    ZMod.natCast_zmod_val]

/-- **Decoding is canonical** (the clause `Collection.encD_decD` of `expCollection`; gate 03b,
finding 1): a string that `expDec i` decodes to `x` is `expEnc i x`, since it is a numeral of
the index width reading below `m` (`natToList_val_natCast`). -/
theorem expEnc_of_expDec {i w : List Bool} {x : ZMod (expOrd i)} (h : expDec i w = some x) :
    expEnc i x = w := by
  rw [expDec] at h
  split_ifs at h with hw
  rw [← Option.some.inj h, expEnc, natToList_val_natCast hw.1 hw.2]

/-- **The function `f_{q,g}(x) = g^x mod p`** [PS10, Theorem 52.3] as a string function on
`Z_m`: the numeral of `g^x mod p` of the index width (the evaluator `modExpStr` mirrored). -/
noncomputable def expF (i : List Bool) (x : ZMod (expOrd i)) : List Bool :=
  natToList (dlW i) (dlG i ^ x.val % dlP i)

/-- The evaluator of the exponentiation collection on `⟨⟨p, ⟨m, g⟩⟩, x⟩`: one modular
exponentiation `modExpStr ⟨g, ⟨x, p⟩⟩` [PS10, Theorem 52.3, "it is easy to evaluate"]. -/
def expEval (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD (pairSndD (pairFstD z)))
    (pairEncode (pairSndD z) (pairFstD (pairFstD z))))

/-- The evaluator computes `expF` on encoded elements. -/
theorem expEval_spec (i : List Bool) (x : ZMod (expOrd i)) :
    expEval (pairEncode i (expEnc i x)) = expF i x := by
  have hl : listToNat (natToList (dlW i) x.val) = x.val :=
    listToNat_natToList (val_lt_two_pow_dlW i x)
  simp only [expEval, expF, expEnc, dlG, dlP, dlW, pairFstD_pairEncode, pairSndD_pairEncode,
    modExpStr_pairEncode] at hl ⊢
  rw [hl]

/-- The evaluator is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_expEval (H : ArithmeticFP) : PolyTimeComputable expEval :=
  H.modExp.comp ((polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    polyTimeComputable_pairFstD)).pairEncode (polyTimeComputable_pairSndD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- **`x ↦ g^x` is injective on `Z_m`** at a valid index (the remark after
[PS10, Theorem 52.3]: "each function is a permutation"; Claim-53.2 of the inventory): since
`g` has order `m` in `Z_p`, `g^a = g^b` forces `a ≡ b (mod m)`.

**Proof sketch.** Both numerals have width `dlW i` and read as numbers below `p < 2^{dlW i}`
(`natToList_injOn`), so `g^a ≡ g^b (mod p)`; in the group of units, `pow_eq_pow_iff_modEq`
with `orderOf_expUnit` gives `a ≡ b (mod m)`, and `a, b < m`. -/
theorem expF_injective {i : List Bool} (h : ExpValid i) : Function.Injective (expF i) := by
  intro x y hxy
  have hlt : ∀ e : ℕ, dlG i ^ e % dlP i < 2 ^ dlW i :=
    fun e => (Nat.mod_lt _ h.1.pos).trans (dlP_lt_two_pow i)
  have h1 : dlG i ^ x.val % dlP i = dlG i ^ y.val % dlP i := natToList_injOn (hlt _) (hlt _) hxy
  have h2 : expUnit h ^ x.val = expUnit h ^ y.val := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_expUnit, ← Nat.cast_pow,
      ← Nat.cast_pow, ← ZMod.natCast_mod, h1, ZMod.natCast_mod]
  have h3 := pow_eq_pow_iff_modEq.1 h2
  rw [orderOf_expUnit h] at h3
  have hx : x.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt x) (expOrd_of_valid h)
  have hy : y.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt y) (expOrd_of_valid h)
  apply ZMod.val_injective
  unfold Nat.ModEq at h3
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h3

/-! ## Instance generators and the discrete-log experiment -/

/-- An **instance generator** for exponentiation collections with validity predicate `V`:
a PPT `Gen(1^n)` whose outputs, from the threshold `n₀` on, satisfy `V` and are well-formed
indices of three `n`-bit numerals. The formal counterpart of the text's
"`q ← Π_n; g ← Gen_{G_q}`" [PS10, Assumption 52.2] and "pick a safe prime `p = 2q + 1` of
length `n`" [PS10, Algorithm 106.2]; the text itself notes (pp. 52–53) that no efficient
sampler of safe primes with generators is known, so the generator is a hypothesis object.

**Deviation:** the ideal samplers of the text are replaced by a PPT generator relative to
which the assumptions are stated (D10, deviations register #15); outputs below `n₀` are
unconstrained (the degenerate parameters). -/
structure ExpGroupGen (V : List Bool → Prop) where
  /-- The generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The threshold from which the outputs are valid. -/
  n₀ : ℕ
  /-- Outputs are valid from the threshold on. -/
  valid : ∀ n (r : gen.Coins n), n₀ ≤ n → V (gen.runAt n [] r)
  /-- Outputs are well-formed indices of `n`-bit numerals from the threshold on. -/
  wellFormed : ∀ n (r : gen.Coins n), n₀ ≤ n → WellFormedIndex n (gen.runAt n [] r)

namespace ExpGroupGen

variable {V : List Bool → Prop} (G : ExpGroupGen V)

/-- The generator outputs primes of *full length* `n` on **every** coin string: `2^{n-1} ≤ p`
at every generated index from `n₀` on (the text's "`p` of length `n`" read with a leading
`1`; `p < 2^n` already follows from `wellFormed`). Too strong as a hypothesis of a theorem
(see `FullLengthExcept`, run-3 audit P8-2): together with `valid` it asks for a deterministic
polynomial-time construction (run the generator on the all-zero coins) of a full-length prime
of the required form at every `n ≥ n₀`, which is not known. Kept as the deterministic
special case (`FullLength.fullLengthExcept`). -/
def FullLength : Prop :=
  ∀ n (r : G.gen.Coins n), G.n₀ ≤ n → 2 ^ (n - 1) ≤ dlP (G.gen.runAt n [] r)

/-- The generator outputs primes of full length `n` **except on a set of coins of probability
at most `δ n`**: for `n ≥ n₀`, `Pr_r[p < 2^{n−1}] ≤ δ n` (the fallback instance of a strict-PPT
rejection sampler, D10). Used, with `Negligible δ`, by the proofs that divide by `q` or
`p − 1` (Lemma 84.1's range reduction, the `1/q` term of Theorem 107.3): the short-prime coins
are discarded and contribute at most `δ n`. This is a convenience: instances with `p − 1` below
a polynomial can be inverted by exhaustive search, so `hbig` could be dropped (gate 03f1
review, M1; ruling R-03f1-1 (A) keeps it). Whether safe primes (resp. primes `≡ 3 (mod 4)`
with a generator) of full length can be produced for every `n` except with negligible
probability is itself open ([PS10, p. 52]: the sampler's "basic theoretical properties are
unknown"); the hypothesis `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems
records this.

Repair (run-3 audit P8-2): replaces the hypothesis `G.FullLength` of
`fullDLCollection_hardCore` and `elGamal_secure`, which demanded `2^{n−1} ≤ p` on every coin
string and made `{G // G.FullLength}` not known to be inhabited for reasons unrelated to any
cryptographic assumption (contrary to D10 / deviation 15, strict PPT with `2^{-n}` failure). -/
def FullLengthExcept (δ : ℕ → ℝ) : Prop :=
  ∀ n, G.n₀ ≤ n → uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) ≤ δ n

/-- **The discrete-log experiment** [PS10, Assumption 52.2]:
`Pr[i ← Gen(1^n); x ← Z_m : A(1^n, ⟨i, g^x⟩) = x]`, the average over the generator's coins
of the probability, over the ideal uniform `x ∈ Z_m` and the coins of `A`, that the answer of
`A` decodes to an `n`-bit numeral reading as `x`.

**Deviation:** `A` receives `1^n` and the index (the text's `A(g^x)`); ideal uniform `x`;
`n`-bit answers (module docstring). -/
noncomputable def dlProb (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun r : G.gen.Coins n =>
    uprob fun z : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
      ∃ x : Fin n → Bool,
        decodeFin n (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ z.1)) z.2) = some x ∧
          bitsToNat x = z.1.val

/-- **Discrete-log hardness relative to the generator**: every non-uniform PPT solves the
discrete-log experiment with negligible probability. The safe-prime instance is
[PS10, Assumption 52.2] (`DLAssumption`); the full-group instance is the assumption of
[PS10, Lemma 84.1] (`DiscreteLogHardcore`). -/
def DLHard : Prop := ∀ A : NUPPT, Negligible fun n => G.dlProb A n

/-- The discrete-log probability is nonnegative. -/
theorem dlProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ G.dlProb A n := by
  unfold dlProb uexp
  exact div_nonneg (Finset.sum_nonneg fun z _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The discrete-log probability is at most one. -/
theorem dlProb_le_one (A : NUPPT) (n : ℕ) : G.dlProb A n ≤ 1 := by
  haveI : Nonempty (G.gen.Coins n) := ⟨fun _ => false⟩
  unfold dlProb
  exact (OneWay.uexp_mono fun r => uprob_le_one _).trans (OneWay.uexp_const 1).le

end ExpGroupGen

/-- Full length on every coin string is full length except on a set of probability `0`. -/
theorem ExpGroupGen.FullLength.fullLengthExcept {V : List Bool → Prop} {G : ExpGroupGen V}
    (h : G.FullLength) : G.FullLengthExcept fun _ => 0 := by
  intro n hn
  have hz : uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) = 0 := by
    rw [← uprob_false (α := G.gen.Coins n)]
    exact OneWay.uprob_congr fun r => ⟨fun hlt => (not_le.mpr hlt (h n r hn)).elim, False.elim⟩
  exact hz.le

/-- A generator of full length on every coin string satisfies the hypothesis
`∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems (with `δ = 0`). -/
theorem ExpGroupGen.FullLength.exists_fullLengthExcept {V : List Bool → Prop} {G : ExpGroupGen V}
    (h : G.FullLength) : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ := by
  refine ⟨fun _ => 0, fun c => ⟨1, fun n hn => ?_⟩, h.fullLengthExcept⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [abs_zero]
  positivity

/-! ## The exponentiation collection of an instance generator -/

/-- The fixed valid instance `⟨p, ⟨m, g⟩⟩ = ⟨3, ⟨2, 2⟩⟩` with `2`-bit numerals (`2` has order
`2` in `Z_3`): the index output by the collection's generator below the threshold `n₀` of the
instance generator, where the latter's outputs are unconstrained.

Repair (run-3 audit P3-1): `Collection.sample_spec` requires the sampler's outputs to decode
at *every* generated index, so the collection's generator must output valid indices at every
parameter. -/
def dlDefaultIndex : List Bool :=
  pairEncode (natToList 2 3) (pairEncode (natToList 2 2) (natToList 2 2))

/-- The default index is valid: `3` is prime, `0 < 2 < 3`, and `2` has order `2` in `Z_3`. -/
theorem expValid_dlDefaultIndex : ExpValid dlDefaultIndex := by
  have h3 : dlP dlDefaultIndex = 3 := by
    simp [dlP, dlDefaultIndex, listToNat_natToList (by norm_num : 3 < 2 ^ 2)]
  have h2 : dlM dlDefaultIndex = 2 := by
    simp [dlM, dlDefaultIndex, listToNat_natToList (by norm_num : 2 < 2 ^ 2)]
  have hg : dlG dlDefaultIndex = 2 := by
    simp [dlG, dlDefaultIndex, listToNat_natToList (by norm_num : 2 < 2 ^ 2)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3]; exact Nat.prime_three
  · rw [h2]; norm_num
  · rw [h2, h3]; norm_num
  · rw [hg]; norm_num
  · rw [hg, h3]; norm_num
  · rw [hg, h2, h3]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)

/-- The string function of the collection's index generator on the raw layout
`⟨⟨⟨1^n, []⟩, α⟩, r⟩`: `⟨Gen(1^n; r), []⟩` (no trapdoor) from the threshold `n₀` on, and
`⟨dlDefaultIndex, []⟩` below it (where the instance generator's outputs are unconstrained;
run-3 audit P3-1). -/
def expGenFun {V : List Bool → Prop} (G : ExpGroupGen V) (z : List Bool) : List Bool :=
  if G.n₀ ≤ (NUPPT.inParam z).length then
    pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) []
  else pairEncode dlDefaultIndex []

/-- The index generator's string function is polynomial-time: the threshold test compares
the length of `1^n` with the constant `1^{n₀}` (`polyTimeComputable_lenLe`), then
`polyTimeComputable_ite` between the instance generator's output and a constant. -/
theorem expGenFun_poly {V : List Bool → Prop} (G : ExpGroupGen V) : PolyTimeComputable (expGenFun G) := by
  have hp : PolyTimeComputable fun z => [decide (G.n₀ ≤ (NUPPT.inParam z).length)] := by
    have h := polyTimeComputable_lenLe.comp
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const (List.replicate G.n₀ true)))
    convert h using 1
    funext z
    simp [Function.comp, pairFstD_pairEncode, pairSndD_pairEncode]
  have hf : PolyTimeComputable fun z =>
      pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) [] :=
    (G.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
      NUPPT.polyTimeComputable_inCoins)).pairEncode (polyTimeComputable_const [])
  have h := polyTimeComputable_ite hp hf (polyTimeComputable_const (pairEncode dlDefaultIndex []))
  convert h using 1
  funext z
  simp only [expGenFun, decide_eq_true_eq]

/-- The index generator of the collection: `Gen(1^n) = ⟨i, []⟩` with `i` the output of the
instance generator (from `n₀` on; `dlDefaultIndex` below), same coins. -/
noncomputable def expGen {V : List Bool → Prop} (G : ExpGroupGen V) : NUPPT :=
  NUPPT.ofPolyTimeUniform (expGenFun_poly G) G.gen.coins

/-- The activation of the collection's generator: `⟨Gen(1^n; r), []⟩` for `n ≥ n₀`,
`⟨dlDefaultIndex, []⟩` below. -/
theorem expGen_runAt {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n) :
    (expGen G).runAt n [] r =
      if G.n₀ ≤ n then pairEncode (G.gen.runAt n [] r) [] else pairEncode dlDefaultIndex [] := by
  rw [NUPPT.runAt_eq]
  unfold expGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [expGenFun, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.Uniform.runAt_eq G.gen_uniform]

/-- **Rejection sampling of a number below `m`** from a coin list: `T` trials, trial `t`
reading the first `k` bits of the `t`-th block of `B` bits as a number `v`, accepted iff
`v < m`; `none` if every trial is rejected. With `k` the bit length of `m` the acceptance rate
is `m / 2^k ≥ 1/2` [PS10, Theorem 52.3, "it is easy to sample the domain `D_i`"]. -/
def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
  (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none

/-- `sampleBelowL` is block rejection sampling with the test `v < m`:
`sampleBelowL m k B T = rejectBlocksL (· < m) k B T` (the same blocks, the same test; gate 03f1
review, M2). -/
theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) :
    sampleBelowL m k B T = rejectBlocksL (· < m) k B T := by
  funext r
  rw [rejectBlocksL_eq]
  rfl

/-- A sampled value is below `m`. -/
theorem sampleBelowL_lt {m k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleBelowL m k B T r = some v) :
    v < m := by
  unfold sampleBelowL at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  split_ifs at ht with hc
  rw [Option.some.injEq] at ht
  exact ht ▸ hc

/-- **The rejection sampler is close to uniform** (D10; lemma C4 of the Chapter 2 inventory for
`sampleBelowL`): for `0 < m < 2^n`, `n` trials reading `k = Nat.size m` bits from each of `n`
blocks of `n` uniform coins, with the fallback `0`, output a number within statistical
distance `(1/2)^n` of the uniform number below `m`. The closeness fact behind
`expCollection_sampleClose` and the El Gamal samplers (`egUnit`, `egGenParts`, `egEncParts`,
`ddhExpo`).

**Proof sketch.** A corollary of `statClose_rejectBlocksL` (gate 03f1 review, M2; that lemma is
filled first, and this one is not filled a second time). With `k = Nat.size m`, `k ≤ n` by
`Nat.size_le` (`m < 2^n`), and `sampleBelowL m k n n = rejectBlocksL (· < m) k n n`
(`sampleBelowL_eq_rejectBlocksL`). `statClose_rejectBlocksL (· < m) k n n` with the default
`d = 0` (`0 < m`, `0 < 2^k`) gives closeness `(1 − Pr_{v < 2^k}[v < m])^n = (1 − m/2^k)^n` to
the uniform element of `{v : Fin (2^k) // v < m}`, and `(1 − m/2^k)^n ≤ (1/2)^n` since
`2^k ≤ 2m` (`Nat.lt_size_self` and the minimality of `Nat.size`: `m/2^k ≥ 1/2`). Transport the
target along the value-preserving bijection `{v : Fin (2^k) // v < m} ≃ Fin m`
(`StatClose.comp_equiv_right`) and weaken the bound (`StatClose.mono`). -/
theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
    StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
      (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
  sorry

/-- The string function of the domain sampler on the raw layout `⟨⟨⟨1^n, i⟩, α⟩, r⟩`: a number
below the order `m` read from the index, by rejection over `n` trials of `n`-bit blocks
(reading the bit length of `m` from each block), written as a numeral of the index width;
the fallback `0` on failure. -/
def expSampleRaw (z : List Bool) : List Bool :=
  natToList (dlW (NUPPT.inArg z))
    ((sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z)))
      (NUPPT.inParam z).length (NUPPT.inParam z).length (NUPPT.inCoins z)).getD 0)

/-- **The domain sampler is polynomial-time** [PS10, Theorem 52.3, "it is easy to sample the
domain `D_i`"] given the arithmetic bundle.

**Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
leading zeros stripped (`H.size`); the trial loop is
`Complexity.polyTimeComputable_iterateFind` over the `n` blocks of `1^n` bits
(`polyTimeComputable_pairDropPoly`), each trial comparing the first `k` bits with `m`
(`H.le`); the payload is the accepted block, the `none` branch gives the fallback; the output
is padded to the index width (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`). -/
theorem polyTimeComputable_expSampleRaw (H : ArithmeticFP) : PolyTimeComputable expSampleRaw := by
  sorry

/-- **The domain sampler** of the exponentiation collection: a uniform `NUPPT` with `n · n`
coins. -/
noncomputable def expSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_expSampleRaw H) (.mul .var .var)

/-- The activation of the domain sampler on the index `i`. -/
theorem expSampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool) (s : (expSampler H).Coins n) :
    (expSampler H).runAt n i s =
      natToList (dlW i) ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s)).getD 0) := by
  rw [NUPPT.runAt_eq]
  unfold expSampler
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [expSampleRaw, NUPPT.inArg, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- **The domain sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2)]; repair of the run-3 audit, P3-1): at every parameter
the generated index is valid — `hV` with `G.valid` from `n₀` on, `expValid_dlDefaultIndex`
below (`expGen_runAt`) — so the domain is `Z_m` with `0 < m < p < 2^{dlW i}`
(`expOrd_of_valid`, `dlP_lt_two_pow`); the sampler outputs `natToList (dlW i) v` with `v < m`
(`expSampler_runAt`, `sampleBelowL_lt`, or the fallback `0`), which `expDec` reads back
(`length_natToList`, `listToNat_natToList`) as `x = (v : Z_m)` with `expEnc i x` the same
numeral (`ZMod.val_natCast`, `Nat.mod_eq_of_lt`); `expEval_spec` gives the evaluator clause.

**Proof sketch.** Case split on `G.n₀ ≤ n` in `expGen_runAt`, then the computation above. -/
theorem expSampler_spec {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expGen G).Coins n) (s : (expSampler H).Coins n) :
    ∃ x, expDec (pairFstD ((expGen G).runAt n [] r))
        ((expSampler H).runAt n (pairFstD ((expGen G).runAt n [] r)) s) = some x ∧
      expEval (pairEncode (pairFstD ((expGen G).runAt n [] r))
        ((expSampler H).runAt n (pairFstD ((expGen G).runAt n [] r)) s)) = expF _ x := by
  sorry

/-- **The exponentiation collection of an instance generator**: indices `⟨p, ⟨m, g⟩⟩`,
domains `D_i = Z_m` (valid indices; `Z_1` otherwise), `f_i(x) = g^x mod p`, the generator
`expGen G` (the instance generator from `n₀` on, `dlDefaultIndex` below), the sampler
`expSampler H` and the evaluator `expEval` (one modular exponentiation); the validity bridge
`hV` makes every generated index valid, so that the sampler's outputs decode
(`expSampler_spec`, run-3 audit P3-1). The collection `DL` of [PS10, Theorem 52.3] is the
safe-prime instance `dlCollection`; the full-group collection of [PS10, Lemma 84.1] is the
instance of `DiscreteLogHardcore`. -/
noncomputable def expCollection {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : Collection where
  D i := ZMod (expOrd i)
  encD := expEnc
  decD := expDec
  decD_encD := expDec_expEnc
  encD_decD _ _ _ := expEnc_of_expDec
  f := expF
  gen := expGen G
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := expSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := expEval
  eval_poly := polyTimeComputable_expEval H
  eval_spec := expEval_spec
  sample_spec := expSampler_spec H G hV

/-- The index generated by the exponentiation collection from `n₀` on is the instance
generator's output. -/
theorem expCollection_index {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : G.gen.Coins n) (hn : G.n₀ ≤ n) :
    (expCollection H G hV).index n r = G.gen.runAt n [] r := by
  show pairFstD ((expGen G).runAt n [] r) = _
  rw [expGen_runAt, if_pos hn, pairFstD_pairEncode]

/-- The index generated by the exponentiation collection below `n₀` is the default index. -/
theorem expCollection_index_of_lt {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : G.gen.Coins n) (hn : n < G.n₀) :
    (expCollection H G hV).index n r = dlDefaultIndex := by
  show pairFstD ((expGen G).runAt n [] r) = _
  rw [expGen_runAt, if_neg (not_le.mpr hn), pairFstD_pairEncode]

/-- The domain of the exponentiation collection at an index is `Z_{expOrd i}`. -/
theorem expCollection_D {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) :
    (expCollection H G hV).D i = ZMod (expOrd i) := rfl

/-- **The domain sampler is close to uniform** [PS10, Theorem 52.3, "it is easy to sample the
domain `D_i`"]: the decoded output of `expSampler` at a generated index is within a
negligible statistical distance of the uniform element of `Z_m`.

**Proof sketch.** Take `δ n := 1` for `n < n₀` and `δ n := (1/2)^n` for `n ≥ n₀`. At a
generated index `i` (`expCollection_index`, valid by `hV ∘ G.valid`, well formed with
`dlW i = n`) the sampler outputs `natToList n (sampleBelowL m k n n r).getD 0` with
`m = dlM i = expOrd i` (`expSampler_runAt`, `expOrd_of_valid`) and `k = Nat.size m ≤ n`
(`Nat.size_le`, `m < p < 2^n`): `n` trials each reading `k` uniform bits of a block of the
coins (`uprob_comp_equiv` on the block decomposition `NumberTheory.chunk`), accepted iff the
value is below `m`; `sampleBelowL` is `firstHit (· < m)` of the numbers read from the blocks
(`List.findSome?` over `List.range`), so `statClose_sampleBelowL` (`statClose_firstHit` on
`Fin (2^k)` transported along `bitsEquiv`) gives closeness `(1 - m/2^k)^n ≤ (1/2)^n`
(`Nat.lt_size_self`: `m/2^k ≥ 1/2`), and the decoder `expDec` reads the numeral back exactly
(`listToNat_natToList`, `StatClose.map`, `ZMod.natCast_zmod_val`). Negligibility by
`negligible_two_pow_neg` and `Negligible.mono`. -/
theorem expCollection_sampleClose {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (expCollection H G hV).SampleClose δ := by
  sorry

/-- **Inverting the collection is the discrete-log experiment** [PS10, proof of Theorem 52.3,
"the discrete log assumption implies that `f_{p,g}` is hard to invert"]: for `n ≥ n₀`, the
inversion probability of `A` against the exponentiation collection is at most its
discrete-log probability (the same machine, no reduction needed).

**Proof sketch.** Unfold both averages over the generator's coins (`OneWay.uexp_mono`) and
fix `r`; the index `i = Gen(1^n; r)` is valid and well formed (`hV`, `G.valid`,
`G.wellFormed`, `dlW i = n`). If `A`'s answer `w` decodes under `expDec` to `x'` with
`expF i x' = expF i x`, then `x' = x` (`expF_injective`), `w.length = n` and
`listToNat w = x.val`, so `decodeFin n w = some x''` with `bitsToNat x'' = listToNat w = x.val`
(`decodeFin`, `bitsToNat_eq_listToNat`, `List.ofFn_get`); `uprob_mono` with the coin types
identified (`expCollection_index`). -/
theorem expCollection_invProbAt_le {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (A : NUPPT) {n : ℕ} (hn : G.n₀ ≤ n) :
    (expCollection H G hV).invProbAt A n ≤ G.dlProb A n := by
  sorry

/-- **The exponentiation collection is one-way under discrete-log hardness** (the generic
form of [PS10, Theorem 52.3]).

**Proof sketch.** The sampling clause is `expCollection_sampleClose H G hV`. For the
hardness clause fix `A`: `expCollection_invProbAt_le H G hV A` bounds the inversion
probability by `G.dlProb A n` for `n ≥ n₀`, negligible by `hG A`; conclude by
`Negligible.mono` (`Collection.invProbAt_nonneg`, threshold `n₀`). -/
theorem expCollection_oneWay {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (hG : G.DLHard) : (expCollection H G hV).OneWay := by
  sorry

/-! ## Safe primes: the discrete-log assumption and the collection `DL` -/

/-- A **safe-prime instance** `⟨p, ⟨q, g⟩⟩`: a valid index whose order `q` is prime with
`p = 2q + 1`, so that `g` generates the subgroup of squares `G_q ≤ Z_p^*` of prime order `q`
[PS10, Assumption 52.2 and p. 52, "the subgroup of squares … has order `q` which is prime"]. -/
def SafePrimeValid (i : List Bool) : Prop :=
  ExpValid i ∧ (dlM i).Prime ∧ dlP i = 2 * dlM i + 1

/-- A safe-prime instance is a valid instance. -/
theorem SafePrimeValid.expValid {i : List Bool} (h : SafePrimeValid i) : ExpValid i := h.1

/-- **Safe-prime instance generators**: PPTs `Gen(1^n) = ⟨p, ⟨q, g⟩⟩` outputting safe primes
`p = 2q + 1` of length `n` with a generator `g` of the order-`q` subgroup of squares — the
formal "`q ← Π_n; g ← Gen_{G_q}`" of [PS10, Assumption 52.2] and the "`p ← Π̃_n; y ← Gen_q`"
of [PS10, Assumption 105.1]. -/
abbrev SafePrimeGen : Type 1 := ExpGroupGen SafePrimeValid

/-- **The discrete-log assumption** [PS10, Assumption 52.2] relative to a safe-prime instance
generator `G`: for every non-uniform PPT `A`,
`Pr[(p, q, g) ← Gen(1^n); x ← Z_q : A(1^n, ⟨⟨p, ⟨q, g⟩⟩, g^x⟩) = x]` is negligible.

**Deviation:** `A` receives `1^n` and the instance `(p, q, g)` (the text's `A(g^x)`, source
error 8); the group is the subgroup of squares of `Z_p^*` for a safe prime; the instance law
is the generator's (the text's ideal `q ← Π_n; g ← Gen_{G_q}` has no known efficient
sampler, p. 52); "`< ε(n)`" is "negligible" (module docstring). -/
def DLAssumption (G : SafePrimeGen) : Prop := G.DLHard

/-- Unfolding: the discrete-log assumption is the negligibility of every `dlProb`. -/
theorem dlAssumption_iff (G : SafePrimeGen) :
    DLAssumption G ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n := Iff.rfl

/-- **The collection `DL`** [PS10, Theorem 52.3]: indices `(q, g)` (with `p`), domains
`D_i = Z_q`, ranges `R_i = G_q`, `f_{q,g}(x) = g^x`, with the instance generator `G` as
`Gen`, the rejection sampler of `Z_q` and the modular-exponentiation evaluator.

**Deviation:** the text's `R_i = G_p`, `f_{p,g}` are read as `G_q`, `f_{q,g}` (source
error 8) and the parameter `k` as `n`; the range `G_q` is encoded as residues modulo `p`
(`expF`). -/
noncomputable def dlCollection (H : ArithmeticFP) (G : SafePrimeGen) : Collection :=
  expCollection H G fun _ h => h.expValid

/-- The index generated by `DL` from `n₀` on is the instance generator's output `⟨p, ⟨q, g⟩⟩`. -/
theorem dlCollection_index (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : G.gen.Coins n)
    (hn : G.n₀ ≤ n) : (dlCollection H G).index n r = G.gen.runAt n [] r :=
  expCollection_index H G _ n r hn

/-- **Theorem 52.3** [PS10, Theorem 52.3]: under the discrete-log assumption (and the
arithmetic hypotheses), `DL` is a collection of one-way functions.

**Deviation:** see `dlCollection` and the module docstring (instance generator, safe primes,
rejection-sampled domain).

**Proof sketch.** `expCollection_oneWay` with `hV := SafePrimeValid.expValid`: the sampler
is close to uniform (`expCollection_sampleClose`) and inverting the collection is the
discrete-log experiment (`expCollection_invProbAt_le`), negligible by `hDL`. -/
theorem dlCollection_oneWay (H : ArithmeticFP) (G : SafePrimeGen) (hDL : DLAssumption G) :
    (dlCollection H G).OneWay :=
  expCollection_oneWay H G (fun _ h => h.expValid) hDL

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.NumberTheory.QuadraticResidues
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hard-core bit of the discrete logarithm

[PS10, §3.4.1]: under the discrete-log assumption, `half_{p−1}(x) = [x < (p−1)/2]` is a
hard-core predicate for the exponentiation `f_{p,g}(x) = g^x mod p` [PS10, Lemma 84.1], by the
bit-by-bit inversion of [PS10, Algorithm 84.2] with the randomized majority test of p. 85.

**The group.** The lemma, the algorithm and the proof work in the *full* group `Z_p^*` of
even order `p − 1` (the parity of the exponent is read off quadratic residuosity and
`g^{(p−1)/2} = −1`), not in the prime-order group of [PS10, Assumption 52.2]; the hypothesis is
therefore discrete-log hardness for the full-group collection (`FullDLAssumption`, the
exponentiation collection of `DiscreteLog` with `m = p − 1` and `g` a generator of `Z_p^*`),
restricted to primes `p ≡ 3 (mod 4)` so that the square roots of [PS10, Theorem 58.2] are one
modular exponentiation (decision log, open question 3).

**Two layers.** The *concrete* core (one prime `p`, one generator `g`, exact inequalities,
[Gar26]-style): the number theory behind the algorithm (`pow_half_eq_neg_one`,
`pow_mem_QR_iff`, `sq_eq_pow_two_mul_iff`, `neg_pow_eq`), the loop `dlLoop` of
Algorithm 84.2 with an oracle `O` (`dlBits` with the perfect half-oracle, `dlBits_pow`), the
majority test `majOracle` (p. 85) with its per-trial bound `uprob_trial_ge` and failure bound
`uprob_majOracle_ne_le`, the range reduction `shiftInverter` ("as we will show later", never
shown in the text) and the final inverter `dlInverter` with the bound
`invProb_dlInverter_ge`; the good-instance averaging `good_instances`. The *asymptotic*
wrapper `fullDLCollection_hardCore` packages the inverter as a non-uniform PPT.

**Deviation:** Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma
and Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`;
"`ε = s(n)`" should be `1/s(n)`; the range reduction "as we will show later" is never shown;
the good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
`Pr[noinc | low]` by `1/2 − ε/2`, which is the complementary event of its own increment rule
(the counter `lo` counts *disagreements* `b_i ≠ half(r_i)`, so `noinc` is the typical event
on a low instance). Concretely: `dlLoop` follows line 11 literally (the root is kept iff `A`
answers `1` = lower half, negated on `0`); `half_m(x) := [2x < m]` is a harmless strict
variant of the text's `0 ≤ x ≤ m/2` (they differ at the single point `x = m/2`, probability
`1/(p−1)`; the strict form is *not* required by the halving invariant, since the boundary
exponent `(p−1)/2` only arises as the second root of `y = 1`, whose canonical root `dlRoot`
is `1`); the majority test `majOracle` votes on agreements and resolves the text's
inconsistency, with Chebyshev's inequality for pairwise independent trials and an explicit
number `ℓ` of trials (`HardcoreBit.uprob_majority_fails_le`, [PS10, Lemma 189.8] being
garbled); generators of `Z_p^*` are restricted to `p ≡ 3 (mod 4)`; the asymptotic form takes
`p` of full length `n` except on a negligible set of the generator's coins
(`ExpGroupGen.FullLengthExcept`, run-3 audit P8-2) and the arithmetic bundle `ArithmeticFP`.
(Run-3 audit P8-3: the run-2 text claimed line 11 inverted and the strict `half` necessary;
neither is the case.)

## Main definitions

* `TCSlib.Cryptography.Candidates.expo`, `halfBit`, `IsGenerator`, `dlog` — exponentiation
  `Z_{p−1} → Z_p^*`, the predicate `half_{p−1}`, generators and the discrete logarithm.
* `TCSlib.Cryptography.Candidates.dlRoot`, `dlLoop`, `dlQueries`, `dlBits` —
  [PS10, Algorithm 84.2] with an oracle and with the perfect half-oracle.
* `TCSlib.Cryptography.Candidates.majOracle` — the randomized majority test of p. 85;
  `shiftInverter`, `dlInverter` — the range reduction and the inverter `B`.
* `TCSlib.Cryptography.Candidates.FullGroupValid`, `FullGroupGen`, `FullDLAssumption`,
  `fullDLCollection`, `halfPred`, `halfStr` — the asymptotic setting.

## Main results

* `TCSlib.Cryptography.Candidates.pow_half_eq_neg_one`, `pow_mem_QR_iff`,
  `sq_eq_pow_two_mul_iff`, `neg_pow_eq` — the number theory of p. 85 (Lem-84.1.1).
* `TCSlib.Cryptography.Candidates.dlBits_pow` — correctness of Algorithm 84.2 with a perfect
  oracle; `dlLoop_eq_dlBits` — the noisy loop agrees whenever every query is answered correctly.
* `TCSlib.Cryptography.Candidates.uprob_trial_ge` (Lem-84.1.3), `uprob_majOracle_ne_le`
  (Alg-85.a), `invProb_shiftInverter_ge` (Lem-84.1.4), `good_instances` (Lem-84.1.5),
  `invProb_dlInverter_ge` — the concrete core of [PS10, Lemma 84.1].
* `TCSlib.Cryptography.Candidates.halfStr_spec` (Lem-84.1.0),
  `TCSlib.Cryptography.Candidates.fullDLCollection_hardCore` — [PS10, Lemma 84.1].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.1: Lemma 84.1, Algorithm 84.2 and pp. 85–86; §2.12 Theorem 58.2; Appendix A.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.1 (majority votes and pairwise-independent trials).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Exponentiation in `Z_p^*`, the predicate `half_{p−1}`, generators -/

section Concrete

variable {p : ℕ} [hp : Fact p.Prime] [NeZero (p - 1)]

/-- **The exponentiation function** `f_{p,g}(x) = g^x mod p` on `Z_{p−1}` [PS10, Lemma 84.1]. -/
def expo (g : (ZMod p)ˣ) (x : ZMod (p - 1)) : (ZMod p)ˣ := g ^ x.val

/-- **The predicate `half_m`** [PS10, p. 84, "`half_n(x)` is equal to `1` if and only if
`0 ≤ x ≤ n/2`"]: `half_m(x) = 1` iff `2x < m` (lower half).

**Deviation:** strict inequality at the boundary (`x = m/2` counts as upper half), a harmless
variant of the text's `x ≤ m/2`: the two differ at the single point `x = m/2` (for `m = p − 1`
even), of probability `1/(p−1)` under a uniform exponent, and Algorithm 84.2 is correct with
either (the boundary exponent `(p−1)/2` only arises as the second root `−1` of `y = 1`, and
`dlRoot g 1 = 1`). Run-3 audit P8-3 (the run-2 docstring called the strict form necessary). -/
def halfBit (m : ℕ) (x : ZMod m) : Bool := decide (2 * x.val < m)

/-- `g` is a *generator* of `Z_p^*` [PS10, Definition 52.1]: every unit is a power of `g`. -/
def IsGenerator (g : (ZMod p)ˣ) : Prop := ∀ x, x ∈ Subgroup.zpowers g

omit [NeZero (p - 1)] in
/-- A generator of `Z_p^*` has order `p − 1`. -/
theorem IsGenerator.orderOf_eq {g : (ZMod p)ˣ} (hg : IsGenerator g) : orderOf g = p - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]

/-- **Exponentiation by a generator is injective on `Z_{p−1}`** [PS10, Theorem 52.3 remark]. -/
theorem expo_injective {g : (ZMod p)ˣ} (hg : IsGenerator g) : Function.Injective (expo g) := by
  intro x y h
  have h1 := pow_eq_pow_iff_modEq.1 h
  rw [hg.orderOf_eq] at h1
  apply ZMod.val_injective
  unfold Nat.ModEq at h1
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at h1

/-- **Exponentiation by a generator is a bijection `Z_{p−1} → Z_p^*`** (the discrete-log
collection is a collection of permutations, [PS10, p. 53]). -/
theorem expo_bijective {g : (ZMod p)ˣ} (hg : IsGenerator g) : Function.Bijective (expo g) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨expo_injective hg, by rw [ZMod.card, ZMod.card_units]⟩

/-- **The discrete logarithm** `dlog_g(y)`: the inverse of `expo g` (`Function.invFun`). -/
noncomputable def dlog (g : (ZMod p)ˣ) (y : (ZMod p)ˣ) : ZMod (p - 1) := Function.invFun (expo g) y

/-- `g^{dlog_g y} = y` for a generator `g`. -/
theorem expo_dlog {g : (ZMod p)ˣ} (hg : IsGenerator g) (y : (ZMod p)ˣ) : expo g (dlog g y) = y :=
  Function.invFun_eq ((expo_bijective hg).2 y)

/-- `dlog_g (g^x) = x` for a generator `g`. -/
theorem dlog_expo {g : (ZMod p)ˣ} (hg : IsGenerator g) (x : ZMod (p - 1)) : dlog g (expo g x) = x :=
  expo_injective hg (expo_dlog hg _)

/-! ### The number theory of p. 85 (Lem-84.1.1) -/

omit [NeZero (p - 1)] in
/-- For an odd prime, `(p − 1)/2 ≠ 0` and `2 · ((p − 1)/2) = p − 1`. -/
theorem two_mul_half (hp2 : p ≠ 2) : 2 * ((p - 1) / 2) = p - 1 ∧ 0 < (p - 1) / 2 := by
  have h2 := hp.out.two_le
  have hodd := hp.out.eq_two_or_odd'.resolve_left hp2
  obtain ⟨k, hk⟩ := hodd
  omega

omit [NeZero (p - 1)] in
/-- `−1 ≠ 1` in `Z_p^*` for an odd prime. -/
theorem neg_one_ne_one_units (hp2 : p ≠ 2) : (-1 : (ZMod p)ˣ) ≠ 1 := by
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)⟩
  intro h
  exact ZMod.neg_one_ne_one (by simpa [Units.ext_iff] using h)

omit [NeZero (p - 1)] in
/-- **`g^{(p−1)/2} = −1` for a generator `g` of `Z_p^*`** [PS10, p. 85, "recall that
`g^{p/2} = −1 mod p`"].

**Proof sketch.** `(g^{(p−1)/2})² = g^{p−1} = 1`, so `g^{(p−1)/2} = ±1`
(`Units.sq_eq_sq_iff_eq_or_eq_neg`); `+1` would make the order of `g` divide `(p−1)/2 < p − 1`. -/
theorem pow_half_eq_neg_one (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) :
    g ^ ((p - 1) / 2) = -1 := by
  obtain ⟨h2, hpos⟩ := two_mul_half hp2
  have hsq : (g ^ ((p - 1) / 2)) ^ 2 = (1 : (ZMod p)ˣ) ^ 2 := by
    rw [← pow_mul, mul_comm, h2, ZMod.units_pow_card_sub_one_eq_one, one_pow]
  rcases Units.sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exfalso
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hg.orderOf_eq] at hdvd
    have := Nat.le_of_dvd hpos hdvd
    omega
  · exact h

omit [NeZero (p - 1)] in
/-- **`g^e` is a square iff `e` is even** [PS10, p. 85, Algorithm 84.2 lines 3–7]: the parity
of the discrete logarithm is quadratic residuosity.

**Proof sketch.** Euler's criterion (`ZMod.euler_criterion_units`): `g^e ∈ QR_p` iff
`(g^e)^{(p−1)/2} = (g^{(p−1)/2})^e = (−1)^e = 1`, iff `e` is even (`−1 ≠ 1`). -/
theorem pow_mem_QR_iff (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) (e : ℕ) :
    g ^ e ∈ QR p ↔ Even e := by
  have hhalf : p / 2 = (p - 1) / 2 := by
    have := hp.out.two_le
    obtain ⟨k, hk⟩ := hp.out.eq_two_or_odd'.resolve_left hp2
    omega
  rw [mem_QR_iff, ZMod.euler_criterion_units, hhalf, ← pow_mul, mul_comm, pow_mul,
    pow_half_eq_neg_one hp2 hg]
  exact neg_one_pow_eq_one_iff_even (neg_one_ne_one_units hp2)

omit [NeZero (p - 1)] in
/-- **The square roots of `g^{2x}` are `g^x` and `−g^x`** [PS10, p. 85, "`y` has two square
roots: `g^x` and `g^{x + p/2}`"]. -/
theorem sq_eq_pow_two_mul_iff (g z : (ZMod p)ˣ) (x : ℕ) :
    z ^ 2 = g ^ (2 * x) ↔ z = g ^ x ∨ z = -(g ^ x) := by
  rw [mul_comm, pow_mul]
  exact Units.sq_eq_sq_iff_eq_or_eq_neg

omit [NeZero (p - 1)] in
/-- **`−g^x = g^{x + (p−1)/2}`** [PS10, p. 85]: the second root has the larger exponent. -/
theorem neg_pow_eq (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) (x : ℕ) :
    -(g ^ x) = g ^ (x + (p - 1) / 2) := by
  rw [pow_add, pow_half_eq_neg_one hp2 hg, mul_neg_one]

/-! ### Algorithm 84.2 -/

/-- **The root step of [PS10, Algorithm 84.2]** (lines 3–9): make `y` a square by dividing by
`g` if necessary, then take the square root `y^{(p+1)/4}` of [PS10, Theorem 58.2]
(`NumberTheory.sq_pow_div_four_succ`, valid for `p ≡ 3 (mod 4)`). -/
noncomputable def dlRoot (g y : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (if y ∈ QR p then y else y * g⁻¹) ^ (p / 4 + 1)

/-- **The loop of [PS10, Algorithm 84.2]** with an oracle `O` for `half_{p−1}` of the
discrete logarithm, answering with per-round coins `κ`: for `k` rounds, record the parity bit
(`1` iff `y` is a non-square), take the root `dlRoot g y`, keep it if the oracle says
"lower half" (`true`) and its negative otherwise, and recurse; the output is the exponent
rebuilt from its bits (least significant first).

The root selection is the text's line 11 read literally: "IF `b = 0` THEN `y_{k−1} ← −y_{k−1}`"
keeps the root exactly when `A` answers `1` (= lower half, `half`'s convention) and negates it
otherwise (run-3 audit P8-3: the run-2 docstring wrongly called this a deviation).

**Deviation:** `k` is an explicit round count (the text's `k = |p|` decremented to `0`). -/
noncomputable def dlLoop (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    (k : ℕ) → (ZMod p)ˣ → (Fin k → κ) → ℕ
  | 0, _, _ => 0
  | k + 1, y, c =>
    2 * dlLoop g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) +
      (if y ∈ QR p then 0 else 1)

/-- The sequence of roots submitted to the oracle by `dlLoop` (round `j` queries the root
taken at round `j`); the union bound over rounds is stated on these queries. -/
noncomputable def dlQueries (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    (k : ℕ) → (ZMod p)ˣ → (Fin k → κ) → Fin k → (ZMod p)ˣ
  | 0, _, _ => Fin.elim0
  | k + 1, y, c =>
    Fin.cons (dlRoot g y)
      (dlQueries g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ))

/-- **The perfect oracle**: `half_{p−1}` of the discrete logarithm. -/
noncomputable def halfOracle (g y : (ZMod p)ˣ) : Bool := halfBit (p - 1) (dlog g y)

/-- **Algorithm 84.2 with a perfect oracle** [PS10, Algorithm 84.2, "let us first assume that
`A` is always correct"]: `k` rounds of `dlLoop` driven by `halfOracle`. -/
noncomputable def dlBits (g : (ZMod p)ˣ) (k : ℕ) (y : (ZMod p)ˣ) : ℕ :=
  dlLoop g (fun y (_ : Unit) => halfOracle g y) k y (fun _ => ())

omit [NeZero (p - 1)] in
/-- Unfolding: `dlLoop` at `k + 1`. -/
theorem dlLoop_succ (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) :
    dlLoop g O (k + 1) y c =
      2 * dlLoop g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) +
        (if y ∈ QR p then 0 else 1) := rfl

omit [NeZero (p - 1)] in
/-- Unfolding: the first query of `dlQueries` is the root of the input. -/
theorem dlQueries_zero (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) : dlQueries g O (k + 1) y c 0 = dlRoot g y := by
  simp [dlQueries]

omit [NeZero (p - 1)] in
/-- Unfolding: the later queries of `dlQueries` are those of the recursive call. -/
theorem dlQueries_succ (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) (j : Fin k) :
    dlQueries g O (k + 1) y c j.succ =
      dlQueries g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) j := by
  simp [dlQueries]

omit [NeZero (p - 1)] in
/-- **The noisy loop agrees with the perfect one whenever every query is answered
correctly**: if `O` answers `half_{p−1}(dlog)` on each of its `k` queries, then
`dlLoop g O k y c = dlBits g k y`.

**Proof sketch.** Induction on `k` generalizing `y, c`: both loops query `dlRoot g y` first
(`dlQueries_zero`), the hypothesis at `0` makes them select the same root, and the hypothesis
at `j.succ` (`dlQueries_succ`) is the hypothesis of the recursive call. -/
theorem dlLoop_eq_dlBits (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    ∀ (k : ℕ) (y : (ZMod p)ˣ) (c : Fin k → κ),
      (∀ j, O (dlQueries g O k y c j) (c j) = halfOracle g (dlQueries g O k y c j)) →
        dlLoop g O k y c = dlBits g k y
  | 0, _, _, _ => rfl
  | k + 1, y, c, h => by
    have h0 := h 0
    rw [dlQueries_zero] at h0
    rw [dlLoop_succ, dlBits, dlLoop_succ, h0]
    congr 2
    rw [← dlBits]
    apply dlLoop_eq_dlBits g O k
    intro j
    have hj := h j.succ
    rw [dlQueries_succ, h0] at hj
    exact hj

omit [NeZero (p - 1)] in
/-- **Correctness of Algorithm 84.2 with a perfect oracle** [PS10, p. 85, "we can iteratively
divide, take square roots, and then choose the root with smaller discrete log until we
eventually end up at `1`"]: for `p ≡ 3 (mod 4)`, a generator `g` and `e < p − 1` with
`e < 2^k`, `dlBits g k (g^e) = e`.

**Proof sketch.** Induction on `k` generalizing `e`. At `k = 0`, `e = 0`. At `k + 1`: if `e`
is even, `g^e ∈ QR_p` (`pow_mem_QR_iff`) and `dlRoot g (g^e) = (g^e)^{(p+1)/4}` is a root of
`g^e = g^{2(e/2)}` (`sq_pow_div_four_succ`), hence `g^{e/2}` or `−g^{e/2} = g^{e/2 + (p−1)/2}`
(`sq_eq_pow_two_mul_iff`, `neg_pow_eq`); the perfect oracle answers `true` on `g^{e/2}`
(`dlog_expo`, `2(e/2) ≤ e < p − 1`) and `false` on the other root (its exponent
`e/2 + (p−1)/2 < p − 1` has `2 · (e/2 + (p−1)/2) ≥ p − 1`), so the kept root is `g^{e/2}`;
the recorded bit is `0`, the recursive call returns `e/2 < 2^k`, and `2(e/2) + 0 = e`. If `e`
is odd, `g^e ∉ QR_p`, the loop divides by `g` (`g^e · g⁻¹ = g^{e−1}`, even exponent) and the
same argument gives `2((e−1)/2) + 1 = e`. -/
theorem dlBits_pow (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g) {k e : ℕ}
    (he : e < p - 1) (hk : e < 2 ^ k) : dlBits g k (g ^ e) = e := by
  sorry

/-! ### The majority test of p. 85 and the range reduction -/

/-- **The randomized majority test** replacing line 10 of Algorithm 84.2 [PS10, p. 85]: on
the root `y`, draw `ℓ` fresh `r_i ← Z_{p−1}` and coins for `A`, set `z_i = y · g^{r_i}`, and vote
"lower half" (`true`) for each `i` with `A(z_i) = half_{p−1}(r_i)`; decide by majority.

The text's counter `lo` is incremented when `(b_i = 0 ∧ r_i < p/2) ∨ (b_i = 1 ∧ r_i ≥ p/2)`,
i.e. on a *disagreement* `b_i ≠ half(r_i)`, and `b = 0` (upper half) is chosen when `lo > ℓ/2`:
voting on agreements and deciding "lower half" by majority is the same test. Its analysis on
p. 86 bounds `Pr[noinc | low]` by `1/2 − ε/2`, which is the complementary event of this
increment rule (source error 27; run-3 audit P8-3) — `uprob_trial_ge` states the correct
direction.

**Deviation:** ties go to "upper half" (`HardcoreBit.majority`; the text gives `b = 1` on a
tie `lo = ℓ/2`). -/
def majOracle (g : (ZMod p)ˣ) {ρ : Type*} [Fintype ρ] (A : (ZMod p)ˣ → ρ → Bool) (ℓ : ℕ) :
    (ZMod p)ˣ → (Fin ℓ → ZMod (p - 1) × ρ) → Bool :=
  fun y c => HardcoreBit.majority fun i =>
    decide (A (y * g ^ (c i).1.val) (c i).2 = halfBit (p - 1) (c i).1)

/-- **One trial of the majority test is correct with probability at least `1/2 + ε/2`**
(Lem-84.1.3, [PS10, p. 86, "`Pr[noinc | low(y_{k−1})] ≤ 1/2 − ε + 2(ε/4) = 1/2 − ε/2`"]): if
`A` predicts `half_{p−1}` from `g^x` with probability at least `1/2 + ε` over uniform `x`, and
the exponent `e` of the root lies in `[0, s)` or in `[(p−1)/2, (p−1)/2 + s)` with
`4s ≤ ε(p−1)`, then a trial on `g^e` votes `half_{p−1}(e)` with probability at least `1/2 + ε/2`.

**Proof sketch.** The exponent of `z = g^e · g^r` is `e + r` in `Z_{p−1}` and `r ↦ e + r` is a
bijection (`HardcoreBit.pushesUniform_add_right`), so `Pr_{r, c}[A(z, c) = half(e + r)] =
predProb (expo g) half A ≥ 1/2 + ε` (`uprob_comp_equiv`). For `e < s`, `half(e + r) ≠ half(r)`
only for `r ∈ [(p−1)/2 − e, (p−1)/2) ∪ [p − 1 − e, p − 1)`, at most `2s` values, probability
`≤ 2s/(p−1) ≤ ε/2` (`uprob_eq_card_filter`, `Finset.card_le_card`); for `e` in the upper
window, `e = (p−1)/2 + e'` and `half(e + r) ≠ ¬half(r)` only on `2e' ≤ 2s` values. The union
bound `uprob_or_le` (through `uprob_not`) gives
`Pr[vote = half(e)] ≥ 1/2 + ε − ε/2`. -/
theorem uprob_trial_ge {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ : Type*} [Fintype ρ]
    (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A)
    {s : ℕ} (hs : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) {e : ℕ} (he' : e < p - 1)
    (he : e < s ∨ ((p - 1) / 2 ≤ e ∧ e < (p - 1) / 2 + s)) :
    1 / 2 + ε / 2 ≤ uprob fun c : ZMod (p - 1) × ρ =>
      decide (A (g ^ e * g ^ c.1.val) c.2 = halfBit (p - 1) c.1) = halfBit (p - 1) (e : ZMod (p - 1)) := by
  sorry

/-- **The majority test fails with probability at most `1/(ε² ℓ)`** (Alg-85.a, [PS10, p. 86,
"by setting the number of samples `ℓ = (1/ε)²`, then by the corollary of the Chernoff bound …
`b` will be correct with probability very close to `1`"]) on a root `g^e` whose exponent lies
in the windows of `uprob_trial_ge`.

**Deviation:** Chebyshev's inequality for pairwise independent trials
(`HardcoreBit.uprob_majority_fails_le`, [PS10, Appendix A, p. 189]) with the explicit bound
`1/(4 (ε/2)² ℓ)`, instead of the garbled [PS10, Lemma 189.8].

**Proof sketch.** The `ℓ` votes are functions of the coordinates `c i` of a uniform tuple,
hence pairwise independent (`HardcoreBit.pairwiseUniform_eval`,
`PairwiseUniform.pairwiseIndep`) with the "correct vote" probability `≥ 1/2 + ε/2` each
(`uprob_trial_ge` transported by `pushesUniform_eval`); if the majority is wrong then at most
half of the votes are correct (`two_mul_card_le_of_majority_ne`), whose probability is
`≤ 1/(4 (ε/2)² ℓ) = 1/(ε² ℓ)`. -/
theorem uprob_majOracle_ne_le {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ : Type*} [Fintype ρ]
    [Nonempty ρ] (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hε : 0 < ε)
    (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A) {s : ℕ}
    (hs : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) {ℓ : ℕ} (hℓ : 0 < ℓ) {e : ℕ} (he' : e < p - 1)
    (he : e < s ∨ ((p - 1) / 2 ≤ e ∧ e < (p - 1) / 2 + s)) :
    uprob (fun c : Fin ℓ → ZMod (p - 1) × ρ =>
      majOracle g A ℓ (g ^ e) c ≠ halfBit (p - 1) (e : ZMod (p - 1))) ≤ 1 / (ε ^ 2 * ℓ) := by
  sorry

/-- **The range reduction** (Lem-84.1.4, [PS10, p. 85, "such an algorithm suffices to solve the
discrete log problem, since we can guess and map any instance into this range" — never
shown]): from a solver `B₀` for instances with exponent in `[0, s)`, the inverter that guesses
`t ← [0, T)`, runs `B₀` on `y · g^{−ts}` and returns `B₀(…) + ts`. -/
def shiftInverter (g : (ZMod p)ˣ) {ρ' : Type*} (B₀ : (ZMod p)ˣ → ρ' → ℕ) (s T : ℕ) :
    (ZMod p)ˣ → Fin T × ρ' → ZMod (p - 1) :=
  fun y c => ((B₀ (y * (g ^ (c.1.val * s))⁻¹) c.2 : ℕ) : ZMod (p - 1)) + ((c.1.val * s : ℕ) : ZMod (p - 1))

/-- **The range reduction succeeds with probability at least `(1 − δ)/T`** (Lem-84.1.4): if
`B₀` recovers every exponent `e' < s` from `g^{e'}` with probability at least `1 − δ`, and
`T s ≥ p − 1`, then `shiftInverter g B₀ s T` inverts `expo g` with probability at least
`(1 − δ)/T`.

**Proof sketch.** For `y = g^e` (`e < p − 1`) the guess `t = ⌊e/s⌋ < T` has probability `1/T`
(`pushesUniform_fst`, `uprob_eq_one_div_card`); then `y · g^{−ts} = g^{e − ts}` with
`e − ts < s`, and on `B₀`'s success the output is `(e − ts) + ts = e` in `Z_{p−1}`
(`Nat.cast_sub`, `Nat.div_add_mod`). `uprob_prod` over `(e, t)` and `uprob_mono` with the
event `t = ⌊e/s⌋ ∧ B₀ succeeds` (`OneWay.uprob_and_le_mul`-style product of the two
independent factors, `h (e % s)`). -/
theorem invProb_shiftInverter_ge {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ' : Type*} [Fintype ρ']
    (B₀ : (ZMod p)ˣ → ρ' → ℕ) {s T : ℕ} (hs : 0 < s) (hT : p - 1 ≤ T * s) {δ : ℝ}
    (h : ∀ e' < s, 1 - δ ≤ uprob fun c : ρ' => B₀ (g ^ e') c = e') :
    (1 - δ) / T ≤ invProb (expo g) (shiftInverter g B₀ s T) := by
  sorry

/-- **The inverter `B` of [PS10, Lemma 84.1]**: the range reduction applied to the loop of
Algorithm 84.2 driven by the majority test with `ℓ` trials per round and `k` rounds. -/
noncomputable def dlInverter (g : (ZMod p)ˣ) {ρ : Type*} [Fintype ρ] (A : (ZMod p)ˣ → ρ → Bool)
    (s T ℓ k : ℕ) : (ZMod p)ˣ → Fin T × (Fin k → Fin ℓ → ZMod (p - 1) × ρ) → ZMod (p - 1) :=
  shiftInverter g (dlLoop g (majOracle g A ℓ) k) s T

/-- **The concrete core of [PS10, Lemma 84.1]**: for `p ≡ 3 (mod 4)` prime, a generator `g`
of `Z_p^*` and a predictor `A` of `half_{p−1}` from `g^x` with success at least `1/2 + ε`, the
inverter `dlInverter g A s T ℓ k` recovers the discrete logarithm of a uniform `g^x` with
probability at least `(1 − k/(ε² ℓ))/T`, for any window `0 < s` with `4s ≤ ε(p−1)`, `T s ≥ p − 1`
and `s ≤ 2^k` rounds. (With `s ≈ ε(p−1)/4`, `T ≈ 4/ε + 1`, `k = |p|` and `ℓ = 4|p|/ε²` this is
`≥ 3ε/20`.)

**Proof sketch.** `invProb_shiftInverter_ge` with `B₀ := dlLoop g (majOracle g A ℓ) k` and
`δ := k/(ε² ℓ)`: for `e' < s ≤ 2^k`, `dlBits g k (g^{e'}) = e'` (`dlBits_pow`), and
`dlLoop_eq_dlBits` reduces the failure of `B₀` to the failure of some round's majority vote on
its query (`uprob_exists_le` over the `k` rounds, `Fin.cons` bookkeeping). Along the correct
path the query of round `j` is `dlRoot` of `g^{e_j}` with `e_j = e'/2^j < s`, i.e. `g^{e_j/2}`
or `g^{e_j/2 + (p−1)/2}` (`sq_eq_pow_two_mul_iff`, `neg_pow_eq`), an instance of the windows of
`uprob_majOracle_ne_le`; the coins of round `j` are an independent uniform coordinate
(`pushesUniform_eval`), so each round fails with probability `≤ 1/(ε² ℓ)`. -/
theorem invProb_dlInverter_ge (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hε : 0 < ε)
    (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A) {s T ℓ k : ℕ} (hs : 0 < s)
    (hs4 : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) (hT : p - 1 ≤ T * s) (hk : s ≤ 2 ^ k) (hℓ : 0 < ℓ) :
    (1 - k / (ε ^ 2 * ℓ)) / T ≤ invProb (expo g) (dlInverter g A s T ℓ k) := by
  sorry

end Concrete

/-- **Good instances** (Lem-84.1.5, missing in the text): if the predictor's success, averaged
over the instances `(p, g)` drawn by the generator, is at least `1/2 + ε`, then a set of
instances of probability at least `ε/2` has per-instance success at least `1/2 + ε/2`
(`HardcoreBit.half_le_uprob_threshold` with `c = 1/2`). The reduction fixes `(p, g)` from its
input, so the concrete lemma is applied on this set. -/
theorem good_instances {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → ℝ) (hq : ∀ i, q i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (h : 1 / 2 + ε ≤ uexp q) :
    ε / 2 ≤ uprob fun i => 1 / 2 + ε / 2 ≤ q i :=
  HardcoreBit.half_le_uprob_threshold q hq (by norm_num) hε h

/-! ## The asymptotic form: the full-group collection and Lemma 84.1 -/

/-- A **full-group instance** `⟨p, ⟨p − 1, g⟩⟩`: a valid index whose order is `p − 1` (so `g`
generates `Z_p^*`, the setting of [PS10, Lemma 84.1 and Algorithm 84.2]) with `p ≡ 3 (mod 4)`
(square roots by [PS10, Theorem 58.2]).

**Deviation:** `p ≡ 3 (mod 4)` (decision log, open question 3). -/
def FullGroupValid (i : List Bool) : Prop := ExpValid i ∧ dlM i = dlP i - 1 ∧ dlP i % 4 = 3

/-- A full-group instance is a valid instance. -/
theorem FullGroupValid.expValid {i : List Bool} (h : FullGroupValid i) : ExpValid i := h.1

/-- **Full-group instance generators**: PPTs outputting primes `p ≡ 3 (mod 4)` of length `n`
with a generator of `Z_p^*` (the index set `{(p, g)}` of the collection of
[PS10, Lemma 84.1]). -/
abbrev FullGroupGen : Type 1 := ExpGroupGen FullGroupValid

/-- **The discrete-log assumption in `Z_p^*`** — the hypothesis of [PS10, Lemma 84.1] ("under
the DL assumption (52.2)"): every non-uniform PPT solves
`Pr[(p, g) ← Gen(1^n); x ← Z_{p−1} : A(1^n, ⟨⟨p, ⟨p − 1, g⟩⟩, g^x⟩) = x]` with negligible
probability.

**Deviation:** Assumption 52.2 is for prime-order groups; the lemma needs discrete-log
hardness for a uniform generator of the full group `Z_p^*` (source error 27), stated here
relative to a full-group instance generator. -/
def FullDLAssumption (G : FullGroupGen) : Prop := G.DLHard

/-- **The discrete-log collection in `Z_p^*`** [PS10, Lemma 84.1, "the exponentiation function
`f_{p,g}(x) = g^x mod p` from the discrete-log collection `DL`"]: domains `Z_{p−1}`,
`f_{p,g}(x) = g^x mod p`, the instance generator `G`. -/
noncomputable def fullDLCollection (H : ArithmeticFP) (G : FullGroupGen) : Collection :=
  expCollection H G fun _ h => h.expValid

/-- The full-group collection is one-way under the full-group discrete-log assumption
([PS10, Theorem 52.3] for `Z_p^*`): `expCollection_oneWay`. -/
theorem fullDLCollection_oneWay (H : ArithmeticFP) (G : FullGroupGen) (hDL : FullDLAssumption G) :
    (fullDLCollection H G).OneWay :=
  expCollection_oneWay H G (fun _ h => h.expValid) hDL

/-- **The predicate `half_{p−1}` on the collection**: `h_i(x) = [2x + 2 ≤ p]`, which is
`[2x < p − 1]` at every full-group index (`halfPred_eq`) and is computable from the numerals
of `p` and `x` at every string index (`halfStr_spec`). -/
noncomputable def halfPred (i : List Bool) (x : ZMod (expOrd i)) : Bool :=
  decide (2 * x.val + 2 ≤ dlP i)

/-- At a prime index `half_{p−1}(x) = [2x < p − 1]`, the predicate `halfBit (p − 1)` of the
concrete layer. -/
theorem halfPred_eq {i : List Bool} (h : ExpValid i) (x : ZMod (expOrd i)) :
    halfPred i x = decide (2 * x.val < dlP i - 1) := by
  have := h.1.two_le
  simp only [halfPred, decide_eq_decide]
  omega

/-- **The evaluator of `half_{p−1}`** on `⟨⟨p, ⟨m, g⟩⟩, x⟩`: `[2x + 2 ≤ p]` on the numerals
(Lem-84.1.0, [PS10, p. 84, "it is easy to compute `half_{p−1}()` given `x`"]). -/
def halfStr (z : List Bool) : List Bool :=
  [decide (2 * listToNat (pairSndD z) + 2 ≤ listToNat (pairFstD (pairFstD z)))]

/-- The evaluator computes `halfPred` on encoded elements at every index (the efficiency
clause of `Collection.HardCore`). -/
theorem halfStr_spec (i : List Bool) (x : ZMod (expOrd i)) :
    halfStr (pairEncode i (expEnc i x)) = [halfPred i x] := by
  simp only [halfStr, halfPred, expEnc, dlP, pairFstD_pairEncode, pairSndD_pairEncode,
    listToNat_natToList (val_lt_two_pow_dlW i x)]

/-- **`half_{p−1}` is polynomial-time computable** (Lem-84.1.0) given the arithmetic bundle.

**Proof sketch.** `2x + 2 ≤ p ⟺ ¬ (p / 2 ≤ x)`: `p / 2` is the quotient of `divModStr ⟨p, 1 0⟩`
(`H.divMod` with the constant numeral of `2`, `polyTimeComputable_const`), the comparison is
`H.le` on `⟨p / 2, x⟩` (`polyTimeComputable_pairFstD`, `_pairSndD`, `.pairEncode`), and the
negation of a one-bit string is `polyTimeComputable_ite` on `polyTimeComputable_pairEq` with
`[true]`. -/
theorem polyTimeComputable_halfStr (H : ArithmeticFP) : PolyTimeComputable halfStr := by
  sorry

/-- **Lemma 84.1** [PS10, Lemma 84.1]: under the discrete-log assumption in `Z_p^*` (and the
arithmetic hypotheses), `half_{p−1}` is a hard-core predicate for the exponentiation
`f_{p,g}(x) = g^x mod p` of the discrete-log collection: for every non-uniform PPT `A` there is
a negligible `ε` with `Pr[(p, g) ← Gen(1^n); x ← Z_{p−1} : A(1^n, ⟨⟨p, ⟨p−1, g⟩⟩, g^x⟩) =
half_{p−1}(x)] ≤ 1/2 + ε(n)` for all `n`.

**Deviation:** Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma
and Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`;
"`ε = s(n)`" should be `1/s(n)`; the range reduction "as we will show later" is never shown;
the good-instance averaging over `(p, g)` is missing; the p. 86 analysis is stated for the
complementary event of its own increment rule (module docstring, run-3 audit P8-3). Also:
`p ≡ 3 (mod 4)`; `p` of full length `n` except on a set of the generator's coins of negligible
probability `δ n` (`hbig`, `ExpGroupGen.FullLengthExcept`); the collection form of
Definition 78.3 (`Collection.HardCore`: `A` receives `1^n` and the index).

Repair (run-3 audit P8-2): the hypothesis `hbig : G.FullLength` (full length on every coin
string, not known to be satisfiable) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`; the
proof discards the short-prime coins, which contribute at most `δ n` to the good-instance set.

**Proof sketch.** *Easy:* `halfStr` with `polyTimeComputable_halfStr H` and `halfStr_spec`.
*Hard:* by contradiction with `not_negligible_iff` (through the quantifier form
`Ensemble.indist_iff_exists_negligible`-style of `HardCore`): suppose `A : NUPPT` has
`1/2 + n^{-c} ≤ E_r[Pr_{x, ρ}[A(1^n, ⟨i, f_i x⟩) = half_i x]]` for infinitely many `n ≥ n₀`.
Set `ε := n^{-c}/2`. By `good_instances` (over the generator's coins `r`, index `i = Gen(1^n; r)`)
a set of coins of probability `≥ ε` has per-instance success `≥ 1/2 + ε`; removing the coins
with `p < 2^{n−1}` (probability `≤ δ n` by `hbig`, and `δ n ≤ ε/2` for large `n` since `δ` is
negligible) leaves a *good* set of probability `≥ ε/2` (`uprob_not`, `uprob_or_le`). At such an
index `i = ⟨p, ⟨p−1, g⟩⟩` (valid, `dlW i = n`, `p ≡ 3 (mod 4)`, `2^{n−1} ≤ p < 2^n` on the good
set and by `WellFormedIndex`), the domain is `Z_{p−1}` (`expOrd_of_valid`), `f_i x` is the numeral of
`expo g_u x` with `g_u := expUnit` a generator (`orderOf_expUnit`, `IsGenerator` by
`orderOf_eq_card_of_forall_mem_zpowers`-converse `zpowers_eq_top_of_prime_card`-free counting:
`Nat.card_zpowers`), and `half_i x = halfBit (p−1) x` (`halfPred_eq`), so `A`'s per-instance
success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
Apply `invProb_dlInverter_ge` with `ε := n^{-c}/2`, `s := ⌊(p−1)/(8n^c)⌋` (so `4s ≤ ε(p−1)`),
`T := ⌈(p−1)/s⌉` (so `Ts ≥ p − 1`), `k := n` (`s ≤ p − 1 < 2^n`) and `ℓ := 16 n^{2c+1}`
(so `k/(ε²ℓ) = 1/4`). For large `n` the good instances have `p − 1 ≥ 2^{n−1} − 1 ≥ 16 n^c`, so
`(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16 n^c) ≥ 1` and `T ≤ K(n) := 16 n^c < 2^n`; the inverter then
succeeds with probability `≥ (3/4)/T ≥ 3/(4K(n))` on each good instance, with ideal coins.
The machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, ⟦8n^c⟧_n⟩`
(the `n`-bit numeral of `8n^c`: the bundle has no unary-to-binary conversion); coins
`n·n + n·ℓ·(n·n + A.coins)` (a `PolyExpr`, `c` being fixed): one block of `n·n` coins for `t`
and, for each of the `n·ℓ` trials, a block of `n·n` coins for `r_{j,i}` and `A.coins` coins for
`ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`; computes `s` and `T` (`H.sub`,
`H.divMod`, `H.add`); outputs `0^n` unless `1 ≤ s` and `T < 2^n` (the analysis uses only the
good instances); samples `t := (sampleBelowL T (Nat.size T) n n ·).getD 0` and
`r_{j,i} := (sampleBelowL (p−1) (Nat.size (p−1)) n n ·).getD 0` (`H.le`, `H.size`,
`polyTimeComputable_iterateFind`); shifts `y · g^{−ts}` (`H.modExp`, `H.xgcd`); and runs the
`n` rounds of `dlLoop` (`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`,
D11): quadratic residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by
`H.modExp` (`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
`⟨⟨⟨1^n, ⟨i, z_{j,i}⟩⟩, A.advice n⟩, ρ_{j,i}⟩` (`polyTimeComputable_iterateEmit`,
`NUPPT.polyTimeComputable_layout`), the comparison with `half(r_{j,i})` (`halfStr`), the
majority (`polyTimeComputable_majority`), the negation `p − z` and the bit assembly; finally
`(bits + ts) mod (p−1)` as an `n`-bit numeral (`decodeFin n` reads it back,
`bitsToNat_natToBits`). Sampling: each of the `1 + nℓ` sampled coordinates is within `(1/2)^n`
of uniform (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`); the coins of
`A` are exact; `StatClose.prod` and `StatClose.abs_uprob_sub_le_prod` give a loss of at most
`(1 + 16 n^{2c+2})(1/2)^n` at every instance. Averaging over the good set (probability
`≥ ε/2`, `HardcoreBit.uprob_mul_le_uexp`):
`G.dlProb B n ≥ (ε/2)·3/(4K(n)) − (1 + 16 n^{2c+2})(1/2)^n`
`= 3/(256 n^{2c}) − (1 + 16 n^{2c+2})(1/2)^n`
for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`. -/
theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) :
    (fullDLCollection H G).HardCore halfPred := by
  sorry

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Candidates/ElGamal.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.NumberTheory.QuadraticResidues
import TCSlib.Cryptography.Asymptotic.Ensembles
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The DDH assumption and El Gamal encryption

[PS10, §3.11]: the *decisional Diffie–Hellman assumption* in the order-`q` subgroup `G_q` of
`Z_p^*` for a safe prime `p = 2q + 1` [PS10, Assumption 105.1], the group facts behind it
(p. 106: `G_q` is the subgroup of squares, cyclic of prime order, every element `≠ 1`
generates, squaring is `2`-to-`1` onto it), the El Gamal public-key encryption scheme
[PS10, Algorithm 106.2] and its security under DDH [PS10, Theorem 107.3, "we leave the formal
proof as an exercise"].

**Instances and the two generators.** Safe primes come from a safe-prime instance generator
`G : SafePrimeGen` (`TCSlib.Cryptography.Candidates.DiscreteLog`; the text's "pick a safe
prime `p = 2q + 1` of length `n`"); El Gamal's `Gen` follows the text and draws its own
`h = g²` for a uniform unit `g` (the generator component of `G`'s output is ignored). The DDH
assumption is stated for the *derived* generator `egGroupGen H G`, which outputs the same
`(p, q)` and `h = g²`, replaced by the fixed generator `4 = 2²` on the event `g² = 1`
(probability `1/q`, Claim-107.a): the law of its `h` is the "`y ← Gen_q`" of
Assumption 105.1 up to this term, which is where the `1/q` of Theorem 107.3 comes from.

**Message space.** With arbitrary `m ∈ Z_p^*` the scheme is insecure under DDH on `G_q` (the
Legendre symbol of `c₂` reveals the coset of `m`, source error 28), so the message space is
`G_q`: `Enc` canonicalises its message (`egCanon`: a numeral not reading as an element of
`G_q` is encrypted as `1`). Since the message space depends on the key, security is stated
in the chosen-message form `GroupPKScheme.Secure`: the two messages are produced by a
non-uniform PPT *selector* `M(1^n, pk)`; the constant selectors (messages hard-wired as
advice) recover the quantifier form of [PS10, Definition 102.2] (`GroupPKScheme.Secure.const`).

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the DDH ensembles draw `(p, q, y)` from the instance
generator (the text's ideal `p ← Π̃_n; y ← Gen_q`) and the exponents `a, b, z ∈ Z_q` by
rejection from blocks of `n · n` seed coins, within `2^{-n}` of uniform at the generated
instance (`ddhExpo`, D10 — the inventory's recommendation for Assumption 105.1; equivalent to
the ideal-exponent form up to a negligible statistical term), encoded as
`⟨⟨p, ⟨q, y⟩⟩, ⟨y^a, ⟨y^b, y^c⟩⟩⟩` of `n`-bit numerals, length `15n + 14`; El Gamal's `Gen`
draws `g ← Z_p^*` by rejection (the text's `g ∈ Z_p` may be `0, ±1`, source error 28) and
`a, b ← Z_q` by the same rejection sampler (D10); `pk = ⟨⟨p, ⟨q, h⟩⟩, h^a⟩` carries `q`; `Dec`
is a deterministic string function; messages are canonicalised into `G_q`; security is the
chosen-message form; the safe prime has full length `n` except on a negligible set of the
generator's coins (`ExpGroupGen.FullLengthExcept`).

**Run-3 audit repairs.** P8-1: the run-2 DDH ensembles had dependent-sum seeds
`Σ r, Z_{q_r} × Z_{q_r}` (resp. three factors), on which the uniform seed gives the coin string
`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — so the two ensembles
could have different instance laws, and when `q` varies non-negligibly with the coins (two
orders `q`, `3q/2` on half the coins each give the laws `(4/13, 9/13)` and `(8/35, 27/35)`) a
threshold test `[q ≥ θ_n]` distinguished them, making `DDHAssumption` false for reasons
unrelated to DDH. The seeds are now product types (uniform coins for the generator, D6)
with the exponents read by `ddhExpo`. P8-2: `elGamal_secure`'s hypothesis `G.FullLength`
(full length on every coin string) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.

## Main definitions

* `TCSlib.Cryptography.Candidates.ddhTuple`, `ddhLen`, `ddhExpo`, `ddhReal`, `ddhRandom`,
  `TCSlib.Cryptography.Candidates.DDHAssumption` — [PS10, Assumption 105.1].
* `TCSlib.Cryptography.Candidates.GroupPKScheme`, `GroupPKScheme.challenge`,
  `GroupPKScheme.Secure`, `constSelector` — public-key schemes with a key-dependent message
  space and their security (the form of [PS10, Definition 102.2] for `G_q`).
* `TCSlib.Cryptography.Candidates.egUnit`, `egCanon`, `egGenParts`, `egGen`, `egEncParts`,
  `egEnc`, `egDecStr`, `elGamal` — El Gamal [PS10, Algorithm 106.2].
* `TCSlib.Cryptography.Candidates.egSquareGen`, `egGroupParts`, `egGroupGen` — the derived
  safe-prime instance generator with `h = g²` (fallback `4`).

## Main results

* `TCSlib.Cryptography.Candidates.card_QR_safe`, `mem_QR_iff_pow_eq_one`,
  `orderOf_eq_of_mem_QR`, `zpowers_eq_QR`, `eq_QR_of_card`, `card_sqrt_safe`,
  `pushesUniform_sqTo_safe` — the group facts of p. 106 (NT-105.a, proved).
* `TCSlib.Cryptography.Candidates.uprob_sq_eq_one`, `statClose_of_uprob_ne`,
  `statClose_sq_generator` — the generator-versus-square term `1/q` (Claim-107.a).
* `TCSlib.Cryptography.Candidates.ddhExpo_statClose` — the DDH exponents are within `(1/2)^n`
  of uniform at a generated instance (D10).
* `TCSlib.Cryptography.Candidates.egSquareGen_valid` — the derived generator is valid
  (proved); `egGroupGen_runAt`, `egGen_runAt`, `egEnc_runAt`, `egDecStr_apply` — unfolding.
* `TCSlib.Cryptography.Candidates.elGamal_correct` — correctness of [PS10, Algorithm 106.2].
* `TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const` — constant messages.
* `TCSlib.Cryptography.Candidates.elGamal_secure` — [PS10, Theorem 107.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.11: Assumption 105.1, the remarks on p. 106, Algorithm 106.2, Theorem 107.3;
  §3.10: Definitions 102.1 and 102.2; §3.1: Definition 69.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage) and
  Lemma 3.2 (closure under post-processing).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## The group `G_q` of a safe prime (NT-105.a, [PS10, p. 106]) -/

section SafePrime

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- A safe prime `p = 2q + 1` is odd. -/
theorem safe_ne_two (hpq : p = 2 * q + 1) : p ≠ 2 := by
  have := hq.out.two_le
  omega

/-- `5 ≤ p` for a safe prime `p = 2q + 1`. -/
theorem five_le_safe (hpq : p = 2 * q + 1) : 5 ≤ p := by
  have := hq.out.two_le
  omega

/-- `(p − 1)/2 = q` and `p/2 = q` for `p = 2q + 1`. -/
theorem safe_half (hpq : p = 2 * q + 1) : (p - 1) / 2 = q ∧ p / 2 = q := by omega

/-- **`|G_q| = q`** [PS10, p. 106, "`G` has a subgroup `G_q` of order `q`"]: the subgroup of
squares of `Z_p^*` has `(p − 1)/2 = q` elements (`NumberTheory.card_QR_prime`). -/
theorem card_QR_safe (hpq : p = 2 * q + 1) : Nat.card (QR p) = q := by
  rw [card_QR_prime (safe_ne_two hpq), (safe_half hpq).1]

/-- **`x ∈ G_q ↔ x^q = 1`** [PS10, p. 106, "the subgroup `G_q` consists of all of the squares
modulo `p`"]: Euler's criterion with `p/2 = q`. -/
theorem mem_QR_iff_pow_eq_one (hpq : p = 2 * q + 1) (x : (ZMod p)ˣ) : x ∈ QR p ↔ x ^ q = 1 := by
  rw [mem_QR_iff, ZMod.euler_criterion_units, (safe_half hpq).2]

/-- **Every element `≠ 1` of `G_q` has order `q`** [PS10, p. 106, "since `q` is prime, `G_q`
will be a cyclic group … every element is a generator"]. -/
theorem orderOf_eq_of_mem_QR (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) (hx1 : x ≠ 1) :
    orderOf x = q :=
  orderOf_eq_prime ((mem_QR_iff_pow_eq_one hpq x).1 hx) hx1

/-- **Every element `≠ 1` of `G_q` generates `G_q`** [PS10, p. 106]. -/
theorem zpowers_eq_QR (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = QR p := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx)
  rw [Nat.card_zpowers, orderOf_eq_of_mem_QR hpq hx hx1, card_QR_safe hpq]

/-- **`G_q` is the unique subgroup of order `q`** of `Z_p^*` [PS10, p. 106]: a subgroup of
order `q` consists of `q`-th roots of unity, hence lies in `G_q`, and has its size. -/
theorem eq_QR_of_card (hpq : p = 2 * q + 1) (K : Subgroup (ZMod p)ˣ) (hK : Nat.card K = q) :
    K = QR p := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [mem_QR_iff_pow_eq_one hpq]
    have h1 := pow_card_eq_one' (G := K) (x := ⟨x, hx⟩)
    rw [hK] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · rw [hK, card_QR_safe hpq]

/-- **Squaring is `2`-to-`1` onto `G_q`** [PS10, p. 106, "choosing a generator involves simply
picking a random element `a ∈ G` and computing `a²`"]: every square has exactly two roots. -/
theorem card_sqrt_safe (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) :
    (univ.filter fun y : (ZMod p)ˣ => y ^ 2 = x).card = 2 :=
  card_sqrt_eq_two (safe_ne_two hpq) hx

/-- **The square of a uniform unit is a uniform element of `G_q`** (Claim-107.a, first part; inventory lemma
C5 of chapter 2). -/
theorem pushesUniform_sqTo_safe (hpq : p = 2 * q + 1) : HardcoreBit.PushesUniform (sqTo p) := by
  refine pushesUniform_of_card_fiber (sqTo p) (c := 2) (by norm_num) fun y => ?_
  rw [← card_sqrt_safe hpq y.2]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  rw [Subtype.ext_iff, coe_sqTo]

/-- **`g² = 1` with probability `1/q`** for a uniform unit `g` (Claim-107.a): the two roots
`±1` among the `p − 1 = 2q` units. -/
theorem uprob_sq_eq_one (hpq : p = 2 * q + 1) :
    uprob (fun g : (ZMod p)ˣ => g ^ 2 = 1) = 1 / (q : ℝ) := by
  rw [uprob_eq_card_filter, card_sqrt_safe hpq (one_mem _), ZMod.card_units]
  have h : p - 1 = 2 * q := by omega
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  rw [h]
  push_cast
  field_simp

end SafePrime

/-- **Two samplers on the same seeds are statistically close within the probability that they
differ**: `|Pr[T(X)] − Pr[T(Y)]| ≤ Pr[X ≠ Y]` (the device for the `1/q` term of
Theorem 107.3: the scheme's `h = g²` and the derived generator's `h` differ only on `g² = 1`). -/
theorem statClose_of_uprob_ne {σ γ : Type*} [Fintype σ] (X Y : σ → γ) :
    StatClose X Y (uprob fun s => X s ≠ Y s) := by
  intro T
  have key : ∀ (X Y : σ → γ), uprob (fun s => T (X s)) ≤
      uprob (fun s => T (Y s)) + uprob (fun s => X s ≠ Y s) := by
    intro X Y
    refine (uprob_mono fun s h => ?_).trans (uprob_or_le (fun s => T (Y s)) (fun s => X s ≠ Y s))
    by_cases hxy : X s = Y s
    · exact Or.inl (hxy ▸ h)
    · exact Or.inr hxy
  have h1 := key X Y
  have h2 := key Y X
  have hsymm : uprob (fun s => Y s ≠ X s) = uprob (fun s => X s ≠ Y s) :=
    OneWay.uprob_congr fun s => ne_comm
  rw [hsymm] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **The square of a uniform unit is within `1/q` of a uniform generator of `G_q`**
(Claim-107.a, missing in the text): the uniform element of `G_q` (`pushesUniform_sqTo_safe`)
and the uniform element of `G_q ∖ {1}` (the text's "`y ← Gen_q`") are within statistical
distance `1/q`.

**Proof sketch.** For a test set `S ⊆ G_q`, the two probabilities are `|S|/q` and
`|S ∖ {1}|/(q − 1)`; both lie between `|S ∖ {1}|/q` and `|S ∖ {1}|/q + 1/q`
(`uprob_eq_card_filter`, `card_QR_safe`, `Fintype.card_subtype_compl`); transport the first
along `pushesUniform_sqTo_safe` (`PushesUniform.uprob_eq`). -/
theorem statClose_sq_generator {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p = 2 * q + 1) :
    StatClose (sqTo p) (fun y : {y : QR p // y ≠ 1} => (y : QR p)) (1 / (q : ℝ)) := by
  sorry

/-! ## The DDH assumption [PS10, Assumption 105.1] -/

/-- The DDH tuple `⟨⟨p, ⟨q, y⟩⟩, ⟨y^a, ⟨y^b, y^c⟩⟩⟩` at the instance `i` with exponents
`a, b, c ∈ Z_q` (the text's `(p, y, y^a, y^b, y^c)`), with `n`-bit numerals. -/
noncomputable def ddhTuple (i : List Bool) (a b c : ZMod (expOrd i)) : List Bool :=
  pairEncode i (pairEncode (expF i a) (pairEncode (expF i b) (expF i c)))

/-- The length `15n + 14` of a DDH tuple of `n`-bit numerals. -/
def ddhLen : PolyExpr := .add (.mul (.const 15) .var) (.const 14)

/-- `ddhLen.eval n = 15n + 14`. -/
@[simp] theorem eval_ddhLen (n : ℕ) : ddhLen.eval n = 15 * n + 14 := rfl

/-- A DDH tuple at a well-formed index has length exactly `15n + 14` (the padding of the
ensembles is lossless). -/
theorem length_ddhTuple {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) (a b c : ZMod (expOrd i)) :
    (ddhTuple i a b c).length = 15 * n + 14 := by
  have hw := h.dlW_eq
  simp only [ddhTuple, expF, length_pairEncode, length_natToList, h.length_eq, hw]
  ring

/-- **An exponent of `Z_{expOrd i}` from a block of `n · n` coins** by rejection: `n` trials of
`n`-bit blocks, each reading the bit length of `expOrd i` bits (`sampleBelowL`), with the
fallback `0` — the exponent sampler of El Gamal's `Gen` and `Enc` (`egGenParts`, `egEncParts`:
`sampleBelowL (dlM i) (Nat.size (dlM i)) n n` on an `n · n`-bit coin segment, the same numbers
at a valid index by `expOrd_of_valid`) on typed coins. Its law is within `(1/2)^n` of uniform
at a valid well-formed index (`ddhExpo_statClose`, D10).

Repair (run-3 audit P8-1): the exponents of the DDH ensembles are read from fixed-length coin
blocks instead of being ideal coordinates of a dependent-sum seed (module docstring). -/
noncomputable def ddhExpo (n : ℕ) (i : List Bool) (b : Fin (n * n) → Bool) : ZMod (expOrd i) :=
  (((sampleBelowL (expOrd i) (Nat.size (expOrd i)) n n (List.ofFn b)).getD 0 : ℕ) : ZMod (expOrd i))

/-- `((x : ℕ) : ZMod m) = x` for `x : ZMod m` read through `ZMod.finEquiv` (the identification
of the uniform `Fin m` with the uniform `ZMod m` used by `ddhExpo_statClose`). -/
private theorem natCast_val_finEquiv_symm {m : ℕ} [NeZero m] (t : ZMod m) :
    ((((ZMod.finEquiv m).symm t : Fin m) : ℕ) : ZMod m) = t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  exact ZMod.natCast_zmod_val t

/-- **The DDH exponents are close to uniform**: at a valid index of `n`-bit numerals,
`ddhExpo n i` is within statistical distance `(1/2)^n` of the uniform element of
`Z_{expOrd i}` (D10).

**Proof sketch.** `0 < expOrd i = dlM i < dlP i < 2^n` (`expOrd_of_valid`, `dlP_lt_two_pow`,
`WellFormedIndex.dlW_eq`), so `statClose_sampleBelowL` applies; map both samplers by
`Nat.cast : ℕ → ZMod (expOrd i)` (`StatClose.map`) and identify the image of the uniform
`Fin (expOrd i)` with the uniform `ZMod (expOrd i)` along `ZMod.finEquiv`
(`StatClose.comp_equiv_right`, `natCast_val_finEquiv_symm`). -/
theorem ddhExpo_statClose {n : ℕ} {i : List Bool} (hv : ExpValid i) (hw : WellFormedIndex n i) :
    StatClose (ddhExpo n i) (id : ZMod (expOrd i) → ZMod (expOrd i)) ((1 / 2 : ℝ) ^ n) := by
  have hm : 0 < expOrd i := NeZero.pos _
  have hmn : expOrd i < 2 ^ n := by
    rw [expOrd_of_valid hv, ← hw.dlW_eq]
    exact hv.2.2.1.trans (dlP_lt_two_pow i)
  have h := ((statClose_sampleBelowL hm hmn).map fun v : ℕ => (v : ZMod (expOrd i))).comp_equiv_right
    (ZMod.finEquiv (expOrd i)).symm.toEquiv
  have hY : (fun t : ZMod (expOrd i) =>
      ((((ZMod.finEquiv (expOrd i)).symm.toEquiv t : Fin (expOrd i)) : ℕ) : ZMod (expOrd i))) = id :=
    funext fun t => natCast_val_finEquiv_symm t
  rw [hY] at h
  exact h

/-- **The DDH ensemble** `{p ← Π̃_n; y ← Gen_q; a, b ← Z_q : (p, y, y^a, y^b, y^{ab})}` of
[PS10, Assumption 105.1]: a seed is the generator's coin string together with two blocks of
`n · n` coins from which the exponents `a, b ∈ Z_q` of the generated instance are read by
rejection (`ddhExpo`); the sample is the DDH tuple padded to `15n + 14` bits (exactly its
length from `n₀` on, `length_ddhTuple`). The seed type is a product of coin types, so the
uniform seed gives the generator uniform coins (D6) and is nonempty (`Ensemble.nonempty`,
run-3 audit P2-2, by instance resolution).

Repair (run-3 audit P8-1): the run-2 seed type `Σ r : G.gen.Coins n, Z_{q_r} × Z_{q_r}` gave
the coin string `r` probability `q_r² / Σ_r q_r²` under the uniform seed, so the instance law
depended on the fibre sizes and differed from `ddhRandom`'s (cubes), which could make
`DDHAssumption` false for reasons unrelated to DDH (DESIGN §5 item 20). -/
noncomputable def ddhReal (G : SafePrimeGen) : Ensemble ddhLen where
  σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))
  X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1) (ddhExpo n (G.gen.runAt n [] z.1) z.2.2)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1 * ddhExpo n (G.gen.runAt n [] z.1) z.2.2))

/-- **The random ensemble** `{p ← Π̃_n; y ← Gen_q; a, b, z ← Z_q : (p, y, y^a, y^b, y^z)}` of
[PS10, Assumption 105.1]: the generator's coins and three blocks of `n · n` coins for the
exponents `a, b, z` (`ddhExpo`); seeds nonempty by instance resolution (run-3 audit P2-2).

Repair (run-3 audit P8-1): product seeds instead of the dependent sum (see `ddhReal`). -/
noncomputable def ddhRandom (G : SafePrimeGen) : Ensemble ddhLen where
  σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool) × (Fin (n * n) → Bool))
  X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1) (ddhExpo n (G.gen.runAt n [] z.1) z.2.2.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.2.2))

/-- **The decisional Diffie–Hellman assumption** [PS10, Assumption 105.1] relative to a
safe-prime instance generator `G`: the ensembles `{(p, y, y^a, y^b, y^{ab})}` and
`{(p, y, y^a, y^b, y^z)}` are computationally indistinguishable (`Ensemble.Indist`,
[PS10, Definition 69.4]).

**Deviation:** the instance law is the generator's (the text's ideal `p ← Π̃_n; y ← Gen_q`);
the exponents are read from `n · n`-bit seed blocks by rejection, within `2^{-n}` of uniform
in `Z_q` (`ddhExpo`, D10; run-3 audit P8-1 — equivalent to the ideal-exponent form up to a
negligible statistical term); the tuple is a bit string of `15n + 14` bits; the
distinguisher receives `1^n` (D5). -/
def DDHAssumption (G : SafePrimeGen) : Prop := (ddhReal G).Indist (ddhRandom G)

/-! ## Public-key schemes with a key-dependent message space -/

/-- A **public-key encryption scheme with a key-dependent message space** (the shape of
[PS10, Definition 102.1] for El Gamal, whose messages are elements of the group `G_q`
determined by the public key): a PPT key generator `Gen(1^n) = ⟨pk, sk⟩`, a PPT encryptor
`Enc_pk(m)` activated on `⟨pk, m⟩`, and a deterministic polynomial-time decryptor on
`⟨sk, c⟩`. Correctness is stated per scheme (`elGamal_correct`), since it only holds for the
messages of the key's group.

**Deviation:** `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the
canonical message — here the message space is key-dependent and correctness is stated as a
separate theorem. -/
structure GroupPKScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(m)`, activated on `⟨pk, m⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec

namespace GroupPKScheme

/-- The challenge distribution `{(pk, sk) ← Gen(1^n); ⟨m₀, m₁⟩ ← M(1^n, pk) : ⟨pk, Enc_pk(m_b)⟩}`
for a message selector `M` and the bit `b` (the sampler over the coins of `Gen`, `M` and `Enc`). -/
def challenge (S : GroupPKScheme) (n : ℕ) (M : NUPPT) (b : Bool) :
    S.gen.Coins n × (M.Coins n × S.enc.Coins n) → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1))
      (if b then pairSndD (M.runAt n (pairFstD (S.gen.runAt n [] r.1)) r.2.1)
        else pairFstD (M.runAt n (pairFstD (S.gen.runAt n [] r.1)) r.2.1))) r.2.2)

/-- **Security with a key-dependent message space** (the form of [PS10, Definition 102.2]
used for El Gamal): for every non-uniform PPT message selector `M` and distinguisher `D` there
is a negligible `ε` with, for all `n`, advantage at most `ε(n)` between `⟨pk, Enc_pk(m₀)⟩` and
`⟨pk, Enc_pk(m₁)⟩` for `⟨m₀, m₁⟩ ← M(1^n, pk)`.

**Deviation:** the text's "for all `m₀, m₁ ∈ {0,1}^n`" becomes "for all selectors `M`"
(the messages must lie in the group of the key, so they are functions of `pk`; constant
messages are the selectors returning their advice, `Secure.const`); `D` receives `1^n`. -/
def Secure (S : GroupPKScheme) : Prop :=
  ∀ M D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    distAdv (S.challenge n M false) (S.challenge n M true) (D.distinguisherL n) ≤ ε n

end GroupPKScheme

/-- **The constant message selector**: the non-uniform PPT with no coins returning its advice
`⟨m₀(n), m₁(n)⟩` (length bounded by the syntactic polynomial `b`), whatever the public key. -/
noncomputable def constSelector (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) : NUPPT :=
  NUPPT.ofPolyTime NUPPT.polyTimeComputable_inAdvice (.const 0) b (fun n => pairEncode (m₀ n) (m₁ n)) hb

/-- The constant selector outputs `⟨m₀(n), m₁(n)⟩` on every input. -/
theorem constSelector_runAt (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (n : ℕ) (pk : List Bool)
    (r : (constSelector m₀ m₁ b hb).Coins n) :
    (constSelector m₀ m₁ b hb).runAt n pk r = pairEncode (m₀ n) (m₁ n) := by
  rw [NUPPT.runAt_eq]
  unfold constSelector
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.inAdvice]

/-- The coins of the constant selector form a one-element type. -/
instance constSelector_unique (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (n : ℕ) :
    Unique ((constSelector m₀ m₁ b hb).Coins n) :=
  haveI : IsEmpty (Fin ((constSelector m₀ m₁ b hb).coinLen n)) :=
    ⟨fun i => absurd i.2 (by simp [constSelector, NUPPT.coinLen])⟩
  Pi.uniqueOfIsEmpty _

/-- **Constant messages** (the quantifier form of [PS10, Definition 102.2]): a secure scheme
has, for every pair of message families `m₀, m₁` of polynomially bounded length and every
distinguisher `D`, a negligible `ε` with advantage at most `ε(n)` between `⟨pk, Enc_pk(m₀(n))⟩`
and `⟨pk, Enc_pk(m₁(n))⟩`.

**Proof sketch.** Apply `h` to `constSelector m₀ m₁ b hb` and `D`; by `constSelector_runAt`
the challenge samplers are the constant-message samplers composed with the projection that
forgets the selector's (unique) coin, so `acceptProb_comp_equiv` with
`Equiv.prodCongr (Equiv.refl _) (Equiv.uniqueProd _ _).symm` identifies the advantages. -/
theorem GroupPKScheme.Secure.const {S : GroupPKScheme} (h : S.Secure) (m₀ m₁ : ℕ → List Bool)
    (b : PolyExpr) (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      distAdv (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
          (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₀ n)) r.2))
        (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
          (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₁ n)) r.2))
        (D.distinguisherL n) ≤ ε n := by
  obtain ⟨ε, hε, hle⟩ := h (constSelector m₀ m₁ b hb) D
  refine ⟨ε, hε, fun n => le_of_eq_of_le ?_ (hle n)⟩
  let e : S.gen.Coins n × S.enc.Coins n ≃
      S.gen.Coins n × ((constSelector m₀ m₁ b hb).Coins n × S.enc.Coins n) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.uniqueProd _ _).symm
  unfold distAdv
  rw [← acceptProb_comp_equiv e (S.challenge n (constSelector m₀ m₁ b hb) false),
    ← acceptProb_comp_equiv e (S.challenge n (constSelector m₀ m₁ b hb) true)]
  have h0 : (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
        (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₀ n)) r.2)) =
      fun s => S.challenge n (constSelector m₀ m₁ b hb) false (e s) := by
    funext r; simp [e, GroupPKScheme.challenge, constSelector_runAt]
  have h1 : (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
        (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₁ n)) r.2)) =
      fun s => S.challenge n (constSelector m₀ m₁ b hb) true (e s) := by
    funext r; simp [e, GroupPKScheme.challenge, constSelector_runAt]
  rw [h0, h1]

/-! ## El Gamal [PS10, Algorithm 106.2] -/

/-- A uniform unit `g ∈ Z_p^*` by rejection: `1 + v` for `v` sampled below `p − 1`
(`sampleBelowL`, `n` trials of `n`-bit blocks); the fallback `g = 1` on failure.

**Deviation:** the text draws "a random element `g ∈ Z_p`" (possibly `0, ±1`, source
error 28). -/
def egUnit (n p : ℕ) (r : List Bool) : ℕ :=
  (sampleBelowL (p - 1) (Nat.size (p - 1)) n n r).getD 0 + 1

/-- `0 < egUnit n p r`. -/
theorem egUnit_pos (n p : ℕ) (r : List Bool) : 0 < egUnit n p r := Nat.succ_pos _

/-- `egUnit n p r < p` for `p ≥ 2`. -/
theorem egUnit_lt {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (r : List Bool) : egUnit n p r < p := by
  unfold egUnit
  match h : sampleBelowL (p - 1) (Nat.size (p - 1)) n n r with
  | some v => have := sampleBelowL_lt h; simp only [Option.getD_some]; omega
  | none => simp only [Option.getD_none]; omega

/-- **Canonicalisation of a message into `G_q`**: `m` itself when `0 < m < p` and `m^q ≡ 1
(mod p)` (i.e. `m ∈ G_q`, `mem_QR_iff_pow_eq_one`), and `1` otherwise.

**Deviation:** the message space is `G_q` (source error 28); a numeral outside it is
encrypted as the identity. -/
def egCanon (p q m : ℕ) : ℕ := if 0 < m ∧ m < p ∧ m ^ q % p = 1 then m else 1

/-- **The key material of El Gamal's `Gen`** [PS10, Algorithm 106.2] from the numerals `a, b`
of `p, q` and two coin segments: `g ← Z_p^*` (`egUnit`), `h = g² mod p`, `x ← Z_q`
(`sampleBelowL`), `pk = ⟨⟨p, ⟨q, h⟩⟩, h^x mod p⟩`, `sk = ⟨⟨p, ⟨q, h⟩⟩, x⟩`.

**Deviation:** `pk` carries `q` and `sk` carries `q` (the text's `(p, h, a)`); the exponent
is sampled by rejection with the fallback `0`. -/
def egGenParts (n : ℕ) (a b r₁ r₂ : List Bool) : List Bool × List Bool :=
  (pairEncode (pairEncode a (pairEncode b (natToList n (egUnit n (listToNat a) r₁ ^ 2 % listToNat a))))
      (natToList n ((egUnit n (listToNat a) r₁ ^ 2 % listToNat a) ^
        (sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂).getD 0 % listToNat a)),
    pairEncode (pairEncode a (pairEncode b (natToList n (egUnit n (listToNat a) r₁ ^ 2 % listToNat a))))
      (natToList n ((sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂).getD 0)))

/-- The coins of El Gamal's `Gen`: the instance generator's coins, then `n · n` coins for `g`
and `n · n` coins for `a`. -/
def egGenCoins (G : SafePrimeGen) : PolyExpr := .add G.gen.coins (.add (.mul .var .var) (.mul .var .var))

/-- The string function of El Gamal's `Gen` on the raw layout `⟨⟨⟨1^n, []⟩, α⟩, r⟩`: run the
safe-prime generator on the first coin segment to get `⟨p, ⟨q, _⟩⟩`, then `egGenParts` on the
next two segments; output `⟨pk, sk⟩`. -/
def egGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
  pairEncode
    (egGenParts (NUPPT.inParam z).length
      (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
      (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
      (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
        ((NUPPT.inParam z).length * (NUPPT.inParam z).length))
      ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length +
        (NUPPT.inParam z).length * (NUPPT.inParam z).length))).1
    (egGenParts (NUPPT.inParam z).length
      (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
      (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
      (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
        ((NUPPT.inParam z).length * (NUPPT.inParam z).length))
      ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length +
        (NUPPT.inParam z).length * (NUPPT.inParam z).length))).2

/-- **El Gamal's `Gen` is polynomial-time** given the arithmetic bundle.

**Proof sketch.** Cut the coins at the unary lengths `1^{coins(n)}` and `1^{n·n}`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly` on `⟨1^n, r⟩`); run `G.gen.output` on the
layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`); the two
rejection loops are `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the
test `H.le` (the decrement `p − 1` and the bit length `Nat.size`: `H.sub`, `H.size`);
`h = g² mod p` and `h^x mod p` by `H.modExp`; the numerals are padded to width `n`
(`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
theorem polyTimeComputable_egGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
    PolyTimeComputable (egGenRaw G) := by
  sorry

/-- **El Gamal's key generator** `Gen(1^n) = ⟨pk, sk⟩` as a uniform `NUPPT`. -/
noncomputable def egGen (H : ArithmeticFP) (G : SafePrimeGen) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egGenRaw H G) (egGenCoins G)

/-- The activation of `Gen`: `⟨pk, sk⟩ = egGenParts` on the safe-prime generator's output and
the coin segments. -/
theorem egGen_runAt (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : (egGen H G).Coins n) :
    (egGen H G).runAt n [] r =
      pairEncode
        (egGenParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
          (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
          (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
          ((List.ofFn r).drop (G.gen.coinLen n + n * n))).1
        (egGenParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
          (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
          (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
          ((List.ofFn r).drop (G.gen.coinLen n + n * n))).2 := by
  rw [NUPPT.runAt_eq]
  unfold egGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [egGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.Uniform.runAtL_eq G.gen_uniform, NUPPT.coinLen]

/-- **The ciphertext of El Gamal's `Enc`** [PS10, Algorithm 106.2] on the public key
`pk = ⟨⟨p, ⟨q, h⟩⟩, A⟩` (`A = h^a`), the message numeral `m` and coins `r`: `b ← Z_q`
(`sampleBelowL`), output `⟨h^b mod p, A^b · m' mod p⟩` with `m' = egCanon p q m`. -/
def egEncParts (n : ℕ) (pk m r : List Bool) : List Bool :=
  pairEncode
    (natToList n (dlG (pairFstD pk) ^
      (sampleBelowL (dlM (pairFstD pk)) (Nat.size (dlM (pairFstD pk))) n n r).getD 0 % dlP (pairFstD pk)))
    (natToList n (listToNat (pairSndD pk) ^
      (sampleBelowL (dlM (pairFstD pk)) (Nat.size (dlM (pairFstD pk))) n n r).getD 0 *
        egCanon (dlP (pairFstD pk)) (dlM (pairFstD pk)) (listToNat m) % dlP (pairFstD pk)))

/-- The string function of `Enc` on the raw layout `⟨⟨⟨1^n, ⟨pk, m⟩⟩, α⟩, r⟩`. -/
def egEncRaw (z : List Bool) : List Bool :=
  egEncParts (NUPPT.inParam z).length (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z)) (NUPPT.inCoins z)

/-- **El Gamal's `Enc` is polynomial-time** given the arithmetic bundle.

**Proof sketch.** The exponent `b` by the rejection loop (`polyTimeComputable_iterateFind`,
`H.le`); `h^b`, `A^b`, the membership test `m^q mod p = 1` (`H.modExp`, `polyTimeComputable_pairEq`,
`H.le` for `0 < m < p`, `polyTimeComputable_ite` for the canonicalisation); the product by
`H.mul` and the reduction modulo `p` by `H.divMod`; width-`n` padding by
`polyTimeComputable_unaryPoly`/`_blockMap`; pair. -/
theorem polyTimeComputable_egEncRaw (H : ArithmeticFP) : PolyTimeComputable egEncRaw := by
  sorry

/-- **El Gamal's encryptor** as a uniform `NUPPT` with `n · n` coins. -/
noncomputable def egEnc (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egEncRaw H) (.mul .var .var)

/-- The activation of `Enc` on `⟨pk, m⟩`. -/
theorem egEnc_runAt (H : ArithmeticFP) (n : ℕ) (pk m : List Bool) (r : (egEnc H).Coins n) :
    (egEnc H).runAt n (pairEncode pk m) r = egEncParts n pk m (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold egEnc
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [egEncRaw, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]

/-- **El Gamal's `Dec`** [PS10, Algorithm 106.2, `Dec_sk(c₁, c₂) = c₂ / c₁^a mod p`] as a
composition of the bundle's string functions on `⟨⟨⟨p, ⟨q, h⟩⟩, a⟩, ⟨c₁, c₂⟩⟩`:
`c₁^a mod p` (`modExpStr`), its inverse modulo `p` (`xgcdStr`, second component), the product
with `c₂` (`mulStr`) reduced modulo `p` (`divModStr`, second component). -/
def egDecStr (z : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode
    (mulStr (pairEncode (pairSndD (pairSndD z))
      (pairSndD (xgcdStr (pairEncode
        (modExpStr (pairEncode (pairFstD (pairSndD z))
          (pairEncode (pairSndD (pairFstD z)) (pairFstD (pairFstD (pairFstD z))))))
        (pairFstD (pairFstD (pairFstD z))))))))
    (pairFstD (pairFstD (pairFstD z)))))

/-- Transport of polynomial-time computability along a pointwise equation (used to avoid
the unifier unfolding the arithmetic string functions when matching a composition chain
against a definition; integration note, run 2). -/
private theorem polyTimeComputable_of_forall_eq {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (h : ∀ x, f x = g x) : PolyTimeComputable g :=
  (funext h : f = g) ▸ hf

/-- **`Dec` is polynomial-time** given the arithmetic bundle (a composition of its functions).

The chain is assembled in composition form and transported to `egDecStr` pointwise
(`polyTimeComputable_of_forall_eq` with `Function.comp_apply`): matching the composition
directly against the unfolded definition makes the unifier unfold `xgcdStr`/`modExpStr`
and does not terminate in practice. -/
theorem polyTimeComputable_egDecStr (H : ArithmeticFP) : PolyTimeComputable egDecStr := by
  have hp := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have ha := polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hc₁ := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hc₂ := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hexp := H.modExp.comp (hc₁.pairEncode (ha.pairEncode hp))
  have hinv := polyTimeComputable_pairSndD.comp (H.xgcd.comp (hexp.pairEncode hp))
  have hmul := H.mul.comp (hc₂.pairEncode hinv)
  refine polyTimeComputable_of_forall_eq
    (polyTimeComputable_pairSndD.comp (H.divMod.comp (hmul.pairEncode hp))) (fun z => ?_)
  simp only [Function.comp_apply, egDecStr]

/-- **Unfolding `Dec`**: on `⟨⟨⟨p, t⟩, a⟩, ⟨c₁, c₂⟩⟩` with `0 < p` it returns the numeral of
`c₂ · (c₁^a mod p)⁻¹ mod p` of the width of `p`'s numeral, the inverse being that of `Z_p`
(`ZMod.inv`).

**Proof sketch.** `modExpStr_pairEncode` gives the numeral `v` of `c₁^a mod p < p < 2^{|p|}`
(`listToNat_natToList`); `xgcdStr` returns the numeral of `(v : Z_p)⁻¹.val < p`; `mulStr_pairEncode`
gives the lossless product (`mul_lt_two_pow_add`); `divModStr`'s second component reduces it
modulo `p`. -/
theorem egDecStr_apply (pstr t a c₁ c₂ : List Bool) (hp : 0 < listToNat pstr) :
    egDecStr (pairEncode (pairEncode (pairEncode pstr t) a) (pairEncode c₁ c₂)) =
      natToList pstr.length (listToNat c₂ *
        (((listToNat c₁ ^ listToNat a % listToNat pstr : ℕ) : ZMod (listToNat pstr))⁻¹).val %
          listToNat pstr) := by
  sorry

/-- **El Gamal** [PS10, Algorithm 106.2] from a safe-prime instance generator `G` (used for
`(p, q)` only) and the arithmetic bundle: `Gen(1^n) = ⟨⟨⟨p, ⟨q, h⟩⟩, h^a⟩, ⟨⟨p, ⟨q, h⟩⟩, a⟩⟩` with
`h = g²` for `g ← Z_p^*` and `a ← Z_q`; `Enc_pk(m) = ⟨h^b, (h^a)^b · m⟩` for `b ← Z_q`;
`Dec_sk(c₁, c₂) = c₂ / c₁^a`.

**Deviation:** module docstring (rejection-sampled `g`, `a`, `b`; `q` in the keys;
canonicalised messages; the generator component of `G` is ignored). -/
noncomputable def elGamal (H : ArithmeticFP) (G : SafePrimeGen) : GroupPKScheme where
  gen := egGen H G
  enc := egEnc H
  dec := egDecStr
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := polyTimeComputable_egDecStr H

/-- **Correctness of El Gamal** [PS10, Algorithm 106.2, "`Dec_sk(c) = c₂ / c₁^a mod p`"]: for
`n ≥ n₀`, every key pair and every message `m` of the key's group `G_q` (`egCanon p q m = m`),
`Dec_sk(Enc_pk(m))` decodes to the `n`-bit numeral of `m`.

**Proof sketch.** By `egGen_runAt` (the first coin segment has length `coinLen n`, so it is
`List.ofFn r'` for a typed `r'` and `G.valid`/`G.wellFormed` apply: `p = 2q + 1` prime,
`n`-bit numerals) the keys are `pk = ⟨⟨p, ⟨q, h⟩⟩, h^a⟩`, `sk = ⟨⟨p, ⟨q, h⟩⟩, a⟩` with
`h = g² mod p`, `0 < h < p` (`egUnit_pos`, `egUnit_lt`, `Nat.Prime.dvd_of_dvd_pow`); by
`egEnc_runAt` the ciphertext is `⟨h^b mod p, (h^a mod p)^b · m mod p⟩` (`dlP`, `dlM`, `dlG`
read back by `listToNat_natToList`), and by `egDecStr_apply` the decryption is
`c₂ · ((h^b mod p)^a mod p)⁻¹ mod p`. In `Z_p` (units `h_u`, `m_u`):
`(h^a)^b · m · ((h^b)^a)⁻¹ = m` (`pow_mul`, `mul_comm`, `Units.mul_inv_cancel_right`,
`ZMod.natCast_mod`), so the result is the numeral of `m < p < 2^n` (`natToList n m`), decoded
by `decodeFin_ofFn`. -/
theorem elGamal_correct (H : ArithmeticFP) (G : SafePrimeGen) {n : ℕ} (hn : G.n₀ ≤ n)
    (rg : (egGen H G).Coins n) (re : (egEnc H).Coins n) (m : ℕ)
    (hm : egCanon (dlP (pairFstD (pairFstD ((egGen H G).runAt n [] rg))))
      (dlM (pairFstD (pairFstD ((egGen H G).runAt n [] rg)))) m = m) :
    decodeFin n (egDecStr (pairEncode (pairSndD ((egGen H G).runAt n [] rg))
      ((egEnc H).runAt n (pairEncode (pairFstD ((egGen H G).runAt n [] rg)) (natToList n m)) re))) =
      some (natToBits n m) := by
  sorry

/-! ## The derived instance generator and Theorem 107.3 -/

/-- The generator `h` of `G_q` derived from a unit `g`: `g² mod p`, replaced by `4 = 2²` when
`g² ≡ 1` (the text's `h = g²` with the degenerate case `h = 1` removed; Claim-107.a). -/
def egSquareGen (p g : ℕ) : ℕ := if g ^ 2 % p = 1 then 4 else g ^ 2 % p

/-- **The derived generator is a generator of `G_q`** (NT-105.a and Claim-107.a): for a safe
prime `p = 2q + 1` and `0 < g < p`, `h = egSquareGen p g` satisfies `0 < h < p` and
`orderOf (h : Z_p) = q`.

**Proof sketch.** Let `u` be the unit `g mod p`. If `g² mod p ≠ 1`, then `h = g² mod p` is the
value of `u² ∈ G_q` (`ZMod.natCast_mod`, `ZMod.coe_unitOfCoprime`), nonzero since `p ∤ g²`
(`Nat.Prime.dvd_of_dvd_pow`), different from `1` (`ZMod.val_natCast_of_lt`), of order `q`
(`orderOf_eq_of_mem_QR`, `sq_mem_QR`, `orderOf_units`). Otherwise `h = 4 = 2²` with `5 ≤ p`
(`five_le_safe`), the value of the square of the unit `2`, different from `1`, of order `q`
likewise. -/
theorem egSquareGen_valid {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p = 2 * q + 1)
    {g : ℕ} (hg0 : 0 < g) (hgp : g < p) :
    0 < egSquareGen p g ∧ egSquareGen p g < p ∧ orderOf ((egSquareGen p g : ℕ) : ZMod p) = q := by
  have h5 := five_le_safe hpq
  -- the order of the square of a unit `u` with `u² ≠ 1`
  have key : ∀ (u : (ZMod p)ˣ) (h : ℕ), ((h : ℕ) : ZMod p) = (u : ZMod p) ^ 2 → h < p → h ≠ 1 →
      orderOf ((h : ℕ) : ZMod p) = q := by
    intro u h hu hhp hh1
    have hne : u ^ 2 ≠ 1 := by
      intro h1
      apply hh1
      have h2 : ((h : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        rw [hu, ← Units.val_pow_eq_pow_val, h1, Units.val_one, Nat.cast_one]
      have h3 := congrArg ZMod.val h2
      rwa [ZMod.val_natCast_of_lt hhp, ZMod.val_natCast_of_lt (by omega)] at h3
    rw [hu, ← Units.val_pow_eq_pow_val, orderOf_units]
    exact orderOf_eq_of_mem_QR hpq (sq_mem_QR u) hne
  have hcop : Nat.Coprime g p :=
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt hg0 hgp)).symm
  by_cases h1 : g ^ 2 % p = 1
  · have hval : egSquareGen p g = 4 := if_pos h1
    refine ⟨by rw [hval]; norm_num, by rw [hval]; omega, ?_⟩
    have hcop2 : Nat.Coprime 2 p :=
      (Nat.coprime_primes Nat.prime_two hp.out).2 (by omega)
    rw [hval]
    refine key (ZMod.unitOfCoprime 2 hcop2) 4 ?_ (by omega) (by norm_num)
    rw [ZMod.coe_unitOfCoprime]
    norm_num
  · have hval : egSquareGen p g = g ^ 2 % p := if_neg h1
    have hlt : g ^ 2 % p < p := Nat.mod_lt _ hp.out.pos
    refine ⟨?_, by rw [hval]; exact hlt, ?_⟩
    · rw [hval]
      apply Nat.pos_of_ne_zero
      intro h0
      have hdvd : p ∣ g := hp.out.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0)
      exact absurd (Nat.le_of_dvd hg0 hdvd) (not_le.2 hgp)
    · rw [hval]
      refine key (ZMod.unitOfCoprime g hcop) (g ^ 2 % p) ?_ hlt h1
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_mod, Nat.cast_pow]

/-- The index `⟨p, ⟨q, h⟩⟩` of the derived generator from the numerals `a, b` of `p, q` and
the coin segment of `g`. -/
def egGroupParts (n : ℕ) (a b r₁ : List Bool) : List Bool :=
  pairEncode a (pairEncode b (natToList n (egSquareGen (listToNat a) (egUnit n (listToNat a) r₁))))

/-- The string function of the derived generator on `⟨⟨⟨1^n, []⟩, α⟩, r⟩`: the safe-prime
generator on the first coin segment, then `egGroupParts` on the next `n · n` coins. -/
def egGroupGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
  egGroupParts (NUPPT.inParam z).length
    (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
    (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
    (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
      ((NUPPT.inParam z).length * (NUPPT.inParam z).length))

/-- **The derived generator is polynomial-time** given the arithmetic bundle (the first two
steps of `polyTimeComputable_egGenRaw`, plus the test `g² mod p = 1` by `H.modExp` and
`polyTimeComputable_pairEq` with the constant numeral of `4` on `polyTimeComputable_ite`). -/
theorem polyTimeComputable_egGroupGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
    PolyTimeComputable (egGroupGenRaw G) := by
  sorry

/-- The machine of the derived generator: a uniform `NUPPT` with `G`'s coins plus `n · n`. -/
noncomputable def egGroupGenMachine (H : ArithmeticFP) (G : SafePrimeGen) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egGroupGenRaw H G) (.add G.gen.coins (.mul .var .var))

/-- The activation of the derived generator's machine. -/
theorem egGroupGenMachine_runAt (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) :
    (egGroupGenMachine H G).runAt n [] r =
      egGroupParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
        (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
        (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n)) := by
  rw [NUPPT.runAt_eq]
  unfold egGroupGenMachine
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [egGroupGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.Uniform.runAtL_eq G.gen_uniform, NUPPT.coinLen]

/-- A string of the right length is the encoding of a typed coin string. -/
private theorem exists_ofFn_eq {ℓ : ℕ} (w : List Bool) (h : w.length = ℓ) :
    ∃ x : Fin ℓ → Bool, List.ofFn x = w := by
  subst h
  exact ⟨fun j => w.get j, List.ofFn_get w⟩

/-- The first coin segment of the derived generator is a coin string of `G.gen`. -/
private theorem exists_take_coins (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) :
    ∃ r' : G.gen.Coins n, List.ofFn r' = (List.ofFn r).take (G.gen.coinLen n) := by
  apply exists_ofFn_eq
  simp only [List.length_take, List.length_ofFn, NUPPT.coinLen, egGroupGenMachine,
    NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_add]
  omega

/-- **The derived generator outputs safe-prime instances** from `G.n₀` on: the index
`⟨p, ⟨q, egSquareGen p g⟩⟩` is valid.

**Proof sketch.** The first coin segment is a typed coin string of `G.gen` (`exists_take_coins`),
so `G.valid` and `G.wellFormed` give `⟨a, ⟨b, c⟩⟩` with `p = 2q + 1` prime; reading the output
back (`pairFstD_pairEncode`, `listToNat_natToList`) reduces the claim to `egSquareGen_valid`
with `0 < g < p` from `egUnit_pos`, `egUnit_lt`. -/
theorem egGroupGen_valid (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) (hn : G.n₀ ≤ n) :
    SafePrimeValid ((egGroupGenMachine H G).runAt n [] r) := by
  obtain ⟨r', hr'⟩ := exists_take_coins H G n r
  rw [egGroupGenMachine_runAt, ← hr', ← NUPPT.runAt_eq]
  have hv := G.valid n r' hn
  obtain ⟨a, b, c, ho, ha, hb, -⟩ := G.wellFormed n r' hn
  rw [ho] at hv ⊢
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, egGroupParts]
  simp only [SafePrimeValid, ExpValid, dlP, dlM, dlG, pairFstD_pairEncode, pairSndD_pairEncode] at hv ⊢
  -- the occurrence of `p` inside the type `ZMod (dlP …)` is not reached by `simp`; `rw` abstracts it
  rw [pairFstD_pairEncode]
  haveI : Fact (listToNat a).Prime := ⟨hv.1.1⟩
  haveI : Fact (listToNat b).Prime := ⟨hv.2.1⟩
  have hpq := hv.2.2
  have hg0 := egUnit_pos n (listToNat a) (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
  have hgp := egUnit_lt hv.1.1.two_le n (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
  obtain ⟨hh0, hhp, hord⟩ := egSquareGen_valid hpq hg0 hgp
  have hlt : egSquareGen (listToNat a) (egUnit n (listToNat a) (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))) <
      2 ^ n := by
    have h2 : listToNat a < 2 ^ n := by
      rw [← ha]
      exact listToNat_lt_two_pow a
    exact hhp.trans h2
  rw [listToNat_natToList hlt]
  exact ⟨⟨hv.1.1, hv.1.2.1, hv.1.2.2.1, hh0, hhp, hord⟩, hv.2.1, hpq⟩

/-- **The derived generator outputs well-formed indices** from `G.n₀` on. -/
theorem egGroupGen_wellFormed (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) (hn : G.n₀ ≤ n) :
    WellFormedIndex n ((egGroupGenMachine H G).runAt n [] r) := by
  obtain ⟨r', hr'⟩ := exists_take_coins H G n r
  rw [egGroupGenMachine_runAt, ← hr', ← NUPPT.runAt_eq]
  obtain ⟨a, b, c, ho, ha, hb, -⟩ := G.wellFormed n r' hn
  rw [ho]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, egGroupParts]
  exact ⟨a, b, _, rfl, ha, hb, length_natToList _ _⟩

/-- **The derived safe-prime instance generator** of El Gamal: the same `(p, q)` as `G`,
`h = g²` for `g ← Z_p^*` with the fallback `4` on `g² = 1`. The DDH assumption of
Theorem 107.3 is relative to this generator; its `h` is the text's "`y ← Gen_q`" up to the
`1/q` term of Claim-107.a. -/
noncomputable def egGroupGen (H : ArithmeticFP) (G : SafePrimeGen) : SafePrimeGen where
  gen := egGroupGenMachine H G
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  n₀ := G.n₀
  valid := egGroupGen_valid H G
  wellFormed := egGroupGen_wellFormed H G

/-- **Theorem 107.3** [PS10, Theorem 107.3]: if the DDH assumption holds (for the derived
generator) then El Gamal with message space `G_q` is secure, for safe primes of full length
except on a negligible set of the generator's coins (and under the arithmetic hypotheses).

**Deviation:** message space `G_q` and the chosen-message form of security (the text's
`m ∈ Z_p` is insecure, source error 28); the DDH assumption is relative to `egGroupGen H G`
and samples its exponents by rejection (`ddhExpo`, D10); `hbig` (`ExpGroupGen.FullLengthExcept`)
is used to make the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of
probability `δ n` (a convenience: if `E[1/q]` were not negligible, a DDH distinguisher finding
`a` by exhaustive search when `q ≤ 2n^c` would contradict the DDH assumption, so `hbig` could be
dropped; gate 03f1 review, M1; ruling R-03f1-1 (A) keeps it); the text leaves the proof as
an exercise and omits the generator-versus-square term.

Repair (run-3 audit P8-1, P8-2): the DDH ensembles' seeds became products (so hybrid 1 below
is exact up to the event `g² = 1`), and `hbig : G.FullLength` became
`∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.

**Proof sketch.** Fix `M, D`. For each bit `b` build the DDH distinguisher `D_b` (advice
`⟨M.advice n, ⟨D.advice n, [b]⟩⟩`, coins `M.coins + D.coins`): on a tuple `t`
(parsed by `pairFstD`/`pairSndD`, the last numeral cut to `n` bits by
`polyTimeComputable_pairTakePoly var`) with `t = ⟨i, ⟨A, ⟨B, Z⟩⟩⟩`, set `pk := ⟨i, A⟩`, run
`M(1^n, pk)` (`NUPPT.exists_seq`), take the `b`-th message, canonicalise it (`H.modExp`,
`H.le`, `polyTimeComputable_ite`), and output `D(1^n, ⟨pk, ⟨B, Z · m' mod p⟩⟩)` (`H.mul`,
`H.divMod`, `NUPPT.exists_comp`). *Hybrid 1* (the square-versus-generator event): the coins of
`challenge n M b` — `G`'s coins, the `n · n`-bit segments of `g` and `a` (`egGen_runAt`), `M`'s
coins and the `n · n` coins of `Enc` for `b'` (`egEnc_runAt`) — are in bijection with the seeds
`(r', (e₁, e₂))` of `ddhReal (egGroupGen H G)` together with `D_b`'s coins
(`acceptProb_comp_equiv`), `r'` being `G`'s coins followed by the segment of `g`
(`egGroupGenMachine_runAt`). Under this bijection the two experiments run `D` on the *same*
string unless `g² ≡ 1 (mod p)`: `ddhExpo` is the very sampler `sampleBelowL q (Nat.size q) n n`
of `egGenParts`/`egEncParts` (`expOrd_of_valid` at the valid index), `h^{(ab' mod q)} = h^{ab'}`
since `h` has order `q` (`egSquareGen_valid`), and `egSquareGen p g = g² mod p` unless
`g² ≡ 1`. Hence `|Pr[D(challenge b)] − Pr[D_b(ddhReal)]| ≤ Pr[g² ≡ 1]` (`uprob_mono`,
`statClose_of_uprob_ne`); `egUnit` is within `(1/2)^n` of the uniform unit
(`statClose_sampleBelowL` with `m = p − 1`, `StatClose.map`), so `Pr[g² ≡ 1] ≤ 1/q + (1/2)^n`
(`uprob_sq_eq_one`, `card_sqrt_safe`), and `hbig` gives, for `n ≥ n₀`, a set of `G`'s coins of
probability `≤ δ n` outside which `2^{n−1} ≤ p = 2q + 1` and `1/q ≤ 8 (1/2)^n`; altogether the
hybrid-1 gap is at most `9 (1/2)^n + δ n =: η n`. *Hybrid 2* (DDH): `hDDH D_b` through
`Ensemble.indist_iff_exists_negligible` gives `ε_b` with
`|Pr[D_b(ddhReal)] − Pr[D_b(ddhRandom)]| ≤ ε_b n`. *Hybrid 3* (the two random worlds coincide
up to the exponent sampler): in `ddhRandom`, `Z = h^z` with `z = ddhExpo n i e₃` independent
of the rest; replacing `z` by an ideal uniform `z ∈ Z_q` costs `(1/2)^n` (`ddhExpo_statClose`,
`StatClose.abs_uprob_sub_le_prod`) in each world, and for ideal `z` and a fixed rest,
`z ↦ h^z · m'_b` is a bijection of `G_q` for `m'_b ∈ G_q` (`expF_injective`, `card_QR_safe`,
`Equiv.mulRight`, or `HardcoreBit.pushesUniform_add_right` on the exponent `z + dlog m'_b`), so
`uprob_prod` and `uprob_comp_equiv` give `|Pr[D_0(ddhRandom)] − Pr[D_1(ddhRandom)]| ≤ 2 (1/2)^n`.
Hence the advantage is at most `2 η n + ε_0 n + ε_1 n + 2 (1/2)^n` for `n ≥ n₀` (and `≤ 1`
below), negligible by `negligible_two_pow_neg`, `Negligible.const_mul`, `Negligible.add`,
`Negligible.mono`. -/
theorem elGamal_secure (H : ArithmeticFP) (G : SafePrimeGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ)
    (hDDH : DDHAssumption (egGroupGen H G)) : (elGamal H G).Secure := by
  sorry

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Candidates/Concrete.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.OneWayFunctions.Amplification
import TCSlib.Cryptography.NumberTheory.Chebyshev
import TCSlib.Cryptography.NumberTheory.Units
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Candidates.Arithmetic
import Mathlib.Logic.Equiv.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete lemmas for the factoring-based candidates

The concrete-layer content of the reductions of [PS10, §2.3–§2.4, §2.7] (Theorems 33.5,
36.3, 51.1), stated as exact inequalities at one security parameter in the style of
[Gar26] and consumed by `TCSlib.Cryptography.Candidates.Factoring`:

* *conditioning* (lemma C1 of the chapter 2 inventory): the probability of an event on the
  uniform subtype `{a // E a}` is `Pr[E ∧ S] / Pr[E]`, and is at least
  `1 - (1 - Pr[S]) / δ` when `Pr[E] ≥ δ` — the step of [PS10, Theorem 33.5] turning an
  inverter of `f_mult` on uniform pairs into a factorer on uniform *prime* pairs;
* the *diagonal*: a uniform pair of elements of a finite type coincides with probability
  `1 / |γ|` (the switch from `Π_n × Π_n` to pairs of distinct primes);
* *random-position planting with a good set* (lemma C3): the one-call reduction of
  [PS10, Algorithm 37.4] (plant the challenge at a uniform position of a fresh tuple,
  `OneWay.yaoTry`) inverts `f` on a uniform *good* input with probability at least
  `(μ - (1 - Pr[G])^m) / m`, `μ` the success of the inverter of the direct product
  `prodFun f m` — the mirror of `OneWay.invProb_prodFun_le` [Gar26, Theorem 2.1] with the
  bad set replaced by the complement of the good set;
* the *tail bound* `(1 - 1/a)^{a k} ≤ e^{-k}` (lemma C8) and its instance
  `(1 - 1/(4n²))^{4n³} ≤ e^{-n}` [PS10, Claim 36.2], with `e^{-n} ≤ 2^{-n}`;
* the *prime-pair density* on `n`-bit strings and the identification of the uniform subtype
  of prime pairs with `Π_n × Π_n` (`primesPairEquiv`);
* the type `DistinctPrimes n` of pairs of distinct primes of `Π_n` (the restriction `p ≠ q`
  of the decision log "Rabin/RSA scope") with its string encoding, its `NeZero`/`Fact`
  instances and `Φ(pq) = (p−1)(q−1)` (moved here from `RSA.lean`, run-3 audit P7-6);
* *block rejection sampling* on coin lists (`rejectBlocksL`, run-3 audit P7-6): the one
  sampler behind the honest samplers of `Z_N^*`, `Z*_{Φ(N)}` and the restricted prime classes
  of [PS10, §2.9–§2.12], with its closeness lemma `statClose_rejectBlocksL` (lemma C4 on
  coin lists).

## Main definitions

* `TCSlib.Cryptography.Candidates.primesPairEquiv` — prime pairs of `n`-bit strings as
  `Π_n × Π_n`.
* `TCSlib.Cryptography.Candidates.DistinctPrimes` — pairs of distinct primes of `Π_n` (the
  index distribution of the factoring assumption and of the RSA/Rabin moduli), with
  `DistinctPrimes.default`, `encodeDistinctPrimes`, `decodeDistinctPrimes`.
* `TCSlib.Cryptography.Candidates.rejectBlocksL` — block rejection sampling on a coin list.

## Main results

* `TCSlib.Cryptography.Candidates.uprob_and_eq_mul_subtype`,
  `TCSlib.Cryptography.Candidates.one_sub_div_le_uprob_subtype` (C1),
  `TCSlib.Cryptography.Candidates.uprob_le_uprob_subtype_add`,
  `TCSlib.Cryptography.Candidates.uprob_subtype_prod_eq` — conditioning on an event.
* `TCSlib.Cryptography.Candidates.uprob_diag` — the diagonal of a uniform pair.
* `TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant` (C3) — random-position
  planting with a good set [PS10, Algorithm 37.4, Theorem 36.3].
* `TCSlib.Cryptography.Candidates.one_sub_one_div_pow_le_exp_neg` (C8),
  `TCSlib.Cryptography.Candidates.claim_36_2` [PS10, Claim 36.2],
  `TCSlib.Cryptography.Candidates.exp_neg_le_half_pow`.
* `TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits`,
  `TCSlib.Cryptography.Candidates.one_div_card_primes_le` — density facts in the forms
  the reductions use.
* `TCSlib.Cryptography.Candidates.decodeDistinctPrimes_encode`,
  `TCSlib.Cryptography.Candidates.DistinctPrimes.isEmpty_of_lt` — the encoding of distinct
  prime pairs is lossless; `Π_n` has no two distinct primes for `n < 2`.
* `TCSlib.Cryptography.Candidates.DistinctPrimes.totient_mul`,
  `TCSlib.Cryptography.Candidates.DistinctPrimes.one_lt_totient` — `Φ(pq) = (p−1)(q−1) ≥ 2`.
* `TCSlib.Cryptography.Candidates.rejectBlocksL_spec`,
  `TCSlib.Cryptography.Candidates.statClose_rejectBlocksL` — accepted values satisfy the
  test; the total sampler is within `(1 − Pr[E])^T` of uniform on `E`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3.1–§2.3.2, Theorem 33.5, Algorithm 33.6; §2.4.2, Claim 36.2, Theorem 36.3,
  Algorithm 37.4; §2.7, Theorem 51.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1 and Figure 2.2: planting at a uniform
  position).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing Finset TCSlib.Cryptography.OneWay NumberTheory

/-! ## Conditioning on an event (lemma C1) -/

section Conditioning

variable {α ρ : Type*} [Fintype α] [Fintype ρ]

/-- **Conditioning, multiplicative form**: `Pr[E ∧ S] = Pr[E] · Pr[S | E]`, where `Pr[S | E]`
is the probability of `S` under the uniform distribution on the subtype `{a // E a}`
(lemma C1 of the chapter 2 inventory, [PS10, proof of Theorem 33.5]: "`A'` feeds `A` a
uniformly distributed input … and replaces `xy` with `z` if both are prime"). -/
theorem uprob_and_eq_mul_subtype (E S : α → Prop) [DecidablePred E] :
    uprob (fun a => E a ∧ S a) = uprob E * uprob (fun z : {a // E a} => S z.1) := by
  unfold uprob
  rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter E S)]
  rcases (Fintype.card {a // E a}).eq_zero_or_pos with h0 | hpos
  · haveI : IsEmpty {a // E a} := Fintype.card_eq_zero_iff.mp h0
    have h1 : Nat.card {z : {a // E a} // S z.1} = 0 := Nat.card_of_isEmpty
    have h2 : Nat.card {a // E a} = 0 := Nat.card_of_isEmpty
    rw [h1, h2]
    simp
  · rw [Nat.card_eq_fintype_card (α := {a // E a})]
    have hc : (Fintype.card {a // E a} : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

/-- **Conditioning, lower bound** (lemma C1, [PS10, proof of Theorem 33.5, the union
bound]): if `Pr[E] ≥ δ > 0` then `Pr[S | E] ≥ 1 - (1 - Pr[S]) / δ`. With `Pr[E] ≥ 1/(4n²)`
and `1 - Pr[S] ≤ 1/(8(n+1)²)` this gives `Pr[S | E] ≥ 1/2`.

**Proof sketch.** `Pr[S] ≤ Pr[E ∧ S] + Pr[¬E] = Pr[E]·Pr[S | E] + 1 - Pr[E]`, so
`Pr[E]·(1 - Pr[S | E]) ≤ 1 - Pr[S]`; divide by `Pr[E] ≥ δ`. -/
theorem one_sub_div_le_uprob_subtype (E S : α → Prop) [DecidablePred E] {δ : ℝ} (hδ : 0 < δ)
    (hE : δ ≤ uprob E) : 1 - (1 - uprob S) / δ ≤ uprob (fun z : {a // E a} => S z.1) := by
  haveI : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : uprob E = 0 := by
      unfold uprob
      simp
    linarith
  have hES := uprob_and_eq_mul_subtype E S
  have hsplit : uprob S ≤ uprob (fun a => E a ∧ S a) + uprob (fun a => ¬ E a) := by
    refine (uprob_mono ?_).trans (uprob_or_le _ _)
    intro a ha
    by_cases hEa : E a
    · exact Or.inl ⟨hEa, ha⟩
    · exact Or.inr hEa
  rw [uprob_not, hES] at hsplit
  have hEpos : 0 < uprob E := lt_of_lt_of_le hδ hE
  have h1 : 1 - uprob (fun z : {a // E a} => S z.1) ≤ (1 - uprob S) / uprob E := by
    rw [le_div_iff₀ hEpos]
    nlinarith
  have h2 : (1 - uprob S) / uprob E ≤ (1 - uprob S) / δ :=
    div_le_div_of_nonneg_left (by linarith [uprob_le_one S]) hδ hE
  linarith

/-- **Dropping a conditioning**: `Pr[S] ≤ Pr[S | E] + Pr[¬E]` (the switch from the uniform
pair of primes `Π_n × Π_n` to the uniform pair of *distinct* primes, whose complement — the
diagonal — has probability `1/|Π_n|`). -/
theorem uprob_le_uprob_subtype_add (E S : α → Prop) [DecidablePred E] :
    uprob S ≤ uprob (fun z : {a // E a} => S z.1) + uprob (fun a => ¬ E a) := by
  have hES := uprob_and_eq_mul_subtype E S
  have hsplit : uprob S ≤ uprob (fun a => E a ∧ S a) + uprob (fun a => ¬ E a) := by
    refine (uprob_mono ?_).trans (uprob_or_le _ _)
    intro a ha
    by_cases hEa : E a
    · exact Or.inl ⟨hEa, ha⟩
    · exact Or.inr hEa
  have h1 : uprob (fun a => E a ∧ S a) ≤ uprob (fun z : {a // E a} => S z.1) := by
    rw [hES]
    exact mul_le_of_le_one_left (uprob_nonneg _) (uprob_le_one _)
  linarith

/-- Conditioning on the first coordinate of a product: the uniform subtype `{a // E a}` with
independent auxiliary coins `ρ` is the uniform subtype of pairs whose first coordinate
satisfies `E` (relabelling by `Equiv.prodSubtypeFstEquivSubtypeProd`). -/
theorem uprob_subtype_prod_eq (E : α → Prop) [DecidablePred E] (S : α × ρ → Prop) :
    uprob (fun z : {a // E a} × ρ => S (z.1.1, z.2)) =
      uprob (fun z : {w : α × ρ // E w.1} => S z.1) :=
  uprob_comp_equiv (Equiv.prodSubtypeFstEquivSubtypeProd (p := E)).symm fun z => S z.1

/-- **The diagonal**: a uniform pair of elements of a nonempty finite type consists of equal
elements with probability `1 / |γ|`. -/
theorem uprob_diag {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ] :
    uprob (fun z : γ × γ => z.2 = z.1) = 1 / Fintype.card γ := by
  rw [uprob_prod]
  simp only [uprob_eq_one_div_card]
  exact uexp_const _

end Conditioning

/-! ## Random-position planting with a good set (lemma C3) -/

section Planting

variable {α β ρ : Type*} [Fintype α] [Fintype ρ] {m : ℕ}

/-- **Random-position planting with a good set** (lemma C3 of the chapter 2 inventory; the
concrete content of [PS10, Theorem 36.3] with the one-call reduction of
[PS10, Algorithm 37.4] planting the challenge at a *uniform* position): if `B` inverts the
direct product `prodFun f m` with probability `μ`, then either every coordinate of the
uniform tuple is outside the good set `G` (probability `(1 - Pr[G])^m`) or the one-call
reduction `yaoTry f B` (plant `f x` at the uniform position `i` of a fresh tuple, call `B`,
return the `i`-th answer) inverts `f(x)` for a uniform `x` lying in `G`:
`μ ≤ (1 - Pr[G])^m + m · Pr_{x, i, xs, r}[x ∈ G ∧ f(yaoTry f B (f x) (i, xs, r)) = f x]`.
Mirror of `OneWay.invProb_prodFun_le` [Gar26, Theorem 2.1] with the bad set replaced by
`¬G`.

**Deviation:** [PS10, Algorithm 37.4] plants at the first prime pair and tests primality;
planting at a uniform position needs no primality test (the text's exercise, p. 37).

**Proof sketch.** Success of `B` on `(xs, r)` means that every `xs i` is outside `G` or that
some position `i` has `xs i ∈ G` and the `i`-th answer inverts `f (xs i)`
(`uprob_mono`, `uprob_or_le`, `uprob_exists_le`). The first event has probability
`(1 - Pr[G])^m` (`uprob_fst`, `OneWay.uprob_pi_forall`, `uprob_not`). For fixed `i`, planting
a fresh uniform `x` at position `i` leaves the tuple uniform (`OneWay.uprob_update`,
`OneWay.prodFun_update`), which rewrites the `i`-th event as the planted experiment; summing
over `i` makes the position uniform (`OneWay.sum_uprob_eq_card_mul`), and a relabelling of
the coin space finishes. -/
theorem invProb_prodFun_le_plant [Nonempty α] [Nonempty ρ] (f : α → β)
    (B : (Fin m → β) → ρ → (Fin m → α)) (G : α → Prop) :
    invProb (prodFun f m) B ≤ (1 - uprob G) ^ m +
      m * uprob (fun z : α × (Fin m × ((Fin m → α) × ρ)) =>
        G z.1 ∧ f (yaoTry f B (f z.1) z.2) = f z.1) := by
  classical
  unfold invProb
  calc uprob (fun z : (Fin m → α) × ρ =>
        prodFun f m (B (prodFun f m z.1) z.2) = prodFun f m z.1)
      ≤ uprob (fun z : (Fin m → α) × ρ => (∀ i, ¬ G (z.1 i)) ∨
          ∃ i ∈ (univ : Finset (Fin m)),
            G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) := by
        apply uprob_mono
        rintro ⟨xs, r⟩ h
        by_cases hall : ∀ i, ¬ G (xs i)
        · exact Or.inl hall
        · push_neg at hall
          obtain ⟨i, hi⟩ := hall
          exact Or.inr ⟨i, mem_univ _, hi, congrFun h i⟩
    _ ≤ uprob (fun z : (Fin m → α) × ρ => ∀ i, ¬ G (z.1 i)) +
          ∑ i, uprob (fun z : (Fin m → α) × ρ =>
            G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) :=
        (uprob_or_le _ _).trans (add_le_add_left (uprob_exists_le _ _) _)
    _ ≤ _ := by
        apply add_le_add
        · rw [uprob_fst (fun xs : Fin m → α => ∀ i, ¬ G (xs i)),
            uprob_pi_forall (ι := Fin m) (fun x => ¬ G x), uprob_not, Fintype.card_fin]
        · have hplant : ∀ i, uprob (fun z : (Fin m → α) × ρ =>
              G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) =
              uprob (fun z : α × ((Fin m → α) × ρ) =>
                G z.1 ∧ f (yaoTry f B (f z.1) (i, z.2)) = f z.1) := by
            intro i
            rw [← uprob_update i (fun xs r =>
              G (xs i) ∧ f (B (prodFun f m xs) r i) = f (xs i))]
            apply uprob_congr
            rintro ⟨x, xs, r⟩
            simp [yaoTry, prodFun_update]
          simp only [hplant]
          rw [sum_uprob_eq_card_mul, Fintype.card_fin]
          let e : α × (Fin m × ((Fin m → α) × ρ)) ≃ Fin m × (α × ((Fin m → α) × ρ)) :=
            { toFun := fun z => (z.2.1, (z.1, z.2.2))
              invFun := fun z => (z.2.1, (z.1, z.2.2))
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          rw [← uprob_comp_equiv e]
          exact le_rfl

end Planting

/-! ## Tail bounds (lemma C8, Claim 36.2) -/

/-- **Tail bound** (lemma C8 of the chapter 2 inventory): `(1 - 1/a)^{a·k} ≤ e^{-k}` for
`a ≥ 1` (the inequality `1 - t ≤ e^{-t}` raised to the power `a·k`,
`Real.one_sub_div_pow_le_exp_neg`). -/
theorem one_sub_one_div_pow_le_exp_neg (a k : ℕ) (ha : 0 < a) :
    (1 - 1 / (a : ℝ)) ^ (a * k) ≤ Real.exp (-(k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h := Real.one_sub_div_pow_le_exp_neg (n := a * k) (t := (k : ℝ))
    (by push_cast; nlinarith [(by exact_mod_cast ha : (1 : ℝ) ≤ a), (by exact_mod_cast hk : (0 : ℝ) < k)])
  have heq : (1 - (k : ℝ) / ((a * k : ℕ) : ℝ)) = 1 - 1 / (a : ℝ) := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
  rw [heq] at h
  exact h

/-- **Claim 36.2** [PS10, (36.2)]: `(1 - 1/(4n²))^{4n³} = ((1 - 1/(4n²))^{4n²})^n ≤ e^{-n}`:
with `4n³` pairs of random `n`-bit numbers, the probability that none of them is a pair of
primes is at most `e^{-n}` (given the density `1/(4n²)` of prime pairs). -/
theorem claim_36_2 (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (4 * (n : ℝ) ^ 2)) ^ (4 * n ^ 3) ≤ Real.exp (-(n : ℝ)) := by
  have h := one_sub_one_div_pow_le_exp_neg (4 * n ^ 2) n (by positivity)
  have hexp : 4 * n ^ 2 * n = 4 * n ^ 3 := by ring
  rw [hexp] at h
  push_cast at h
  exact h

/-- `e^{-n} ≤ (1/2)^n` (the negligible form of the tail bounds, `negligible_two_pow_neg`). -/
theorem exp_neg_le_half_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  have h1 : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h1]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg]
  have := Real.add_one_le_exp (1 : ℝ)
  rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
  linarith

/-- **Claim 36.2, negligible form**: `(1 - 1/(4n²))^{4n³} ≤ 2^{-n}`. -/
theorem claim_36_2_half_pow (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (4 * (n : ℝ) ^ 2)) ^ (4 * n ^ 3) ≤ (1 / 2 : ℝ) ^ n :=
  (claim_36_2 n hn).trans (exp_neg_le_half_pow n)

/-! ## Prime pairs of bit strings -/

/-- **Prime-pair density on bit strings** [PS10, proof of Theorem 33.5]: for `n ≥ 2`, a
uniform pair of `n`-bit strings reads (`bitsToNat`) as a pair of primes with probability at
least `1/(4n²)` (`NumberTheory.one_div_le_uprob_prime_pair` transported along
`bitsEquiv`). -/
theorem one_div_le_uprob_prime_pair_bits (n : ℕ) (hn : 2 ≤ n) :
    1 / (4 * (n : ℝ) ^ 2) ≤
      uprob (fun z : (Fin n → Bool) × (Fin n → Bool) =>
        (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime) := by
  have h := one_div_le_uprob_prime_pair n hn
  rw [← uprob_comp_equiv (Equiv.prodCongr (bitsEquiv n) (bitsEquiv n))] at h
  simpa using h

/-- The uniform subtype of prime pairs of `n`-bit strings is `Π_n × Π_n`: read each string as
a number (`bitsEquiv`) and split the conjunction (`Equiv.subtypeProdEquivProd`). -/
noncomputable def primesPairEquiv (n : ℕ) :
    {z : (Fin n → Bool) × (Fin n → Bool) // (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime} ≃
      Primes n × Primes n :=
  (Equiv.subtypeEquiv (Equiv.prodCongr (bitsEquiv n) (bitsEquiv n)) (fun z => by simp)).trans
    Equiv.subtypeProdEquivProd

/-- The components of `primesPairEquiv` are the numbers read from the two strings. -/
@[simp] theorem primesPairEquiv_apply_val (n : ℕ)
    (z : {z : (Fin n → Bool) × (Fin n → Bool) // (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime}) :
    ((primesPairEquiv n z).1.1 : ℕ) = bitsToNat z.1.1 ∧
      ((primesPairEquiv n z).2.1 : ℕ) = bitsToNat z.1.2 := by
  simp [primesPairEquiv, Equiv.subtypeProdEquivProd]

/-- `1/|Π_n| ≤ 2n/2^n` for `n ≥ 2` (`NumberTheory.two_pow_le_two_mul_card_primes`): the
probability that two independent uniform primes coincide is negligible. -/
theorem one_div_card_primes_le (n : ℕ) (hn : 2 ≤ n) :
    1 / (Fintype.card (Primes n) : ℝ) ≤ 2 * n / 2 ^ n := by
  have h := two_pow_le_two_mul_card_primes n hn
  have h' : (2 : ℝ) ^ n ≤ 2 * n * Fintype.card (Primes n) := by exact_mod_cast h
  have hpos : (0 : ℝ) < Fintype.card (Primes n) := by
    have : 0 < Fintype.card (Primes n) := by
      by_contra h0
      push_neg at h0
      have : Fintype.card (Primes n) = 0 := by omega
      rw [this, mul_zero] at h
      exact absurd h (not_le.mpr (Nat.two_pow_pos n))
    exact_mod_cast this
  rw [div_le_div_iff₀ hpos (by positivity), one_mul]
  linarith

/-! ## Pairs of distinct primes -/

/-- Pairs of **distinct** primes of `Π_n`: the index distribution of the factoring
assumption and of the RSA/Rabin moduli `N = pq` (decision log "Rabin/RSA scope": `p ≠ q`). -/
abbrev DistinctPrimes (n : ℕ) : Type := {z : Primes n × Primes n // (z.1.1 : ℕ) ≠ z.2.1}

namespace DistinctPrimes

variable {n : ℕ}

/-- The first prime `p`. -/
def p (z : DistinctPrimes n) : ℕ := z.1.1.1

/-- The second prime `q`. -/
def q (z : DistinctPrimes n) : ℕ := z.1.2.1

/-- `p` is prime. -/
theorem p_prime (z : DistinctPrimes n) : z.p.Prime := z.1.1.2

/-- `q` is prime. -/
theorem q_prime (z : DistinctPrimes n) : z.q.Prime := z.1.2.2

/-- `p < 2^n`. -/
theorem p_lt (z : DistinctPrimes n) : z.p < 2 ^ n := z.1.1.1.2

/-- `q < 2^n`. -/
theorem q_lt (z : DistinctPrimes n) : z.q < 2 ^ n := z.1.2.1.2

/-- `p ≠ q`. -/
theorem p_ne_q (z : DistinctPrimes n) : z.p ≠ z.q := z.2

/-- The modulus `N = pq < 2^{2n}`. -/
theorem mul_lt (z : DistinctPrimes n) : z.p * z.q < 2 ^ (2 * n) := by
  rw [two_mul]; exact mul_lt_two_pow_add z.p_lt z.q_lt

/-! ### Instances and the totient (moved from `RSA.lean`, run-3 audit P7-6) -/

/-- The modulus `pq` is nonzero. -/
instance neZero_mul (z : DistinctPrimes n) : NeZero (z.p * z.q) :=
  ⟨mul_ne_zero z.p_prime.ne_zero z.q_prime.ne_zero⟩

/-- `Φ(pq)` is nonzero. -/
instance neZero_totient (z : DistinctPrimes n) : NeZero (Nat.totient (z.p * z.q)) :=
  ⟨(Nat.totient_pos.2 (NeZero.pos _)).ne'⟩

/-- `p` is prime (as a `Fact`). -/
instance fact_p_prime (z : DistinctPrimes n) : Fact z.p.Prime := ⟨z.p_prime⟩

/-- `q` is prime (as a `Fact`). -/
instance fact_q_prime (z : DistinctPrimes n) : Fact z.q.Prime := ⟨z.q_prime⟩

/-- `Φ(pq) = (p−1)(q−1)` for a pair of distinct primes [PS10, p. 47]. -/
theorem totient_mul (z : DistinctPrimes n) : Nat.totient (z.p * z.q) = (z.p - 1) * (z.q - 1) :=
  totient_prime_mul_prime z.p_prime z.q_prime z.p_ne_q

/-- `Φ(pq) ≥ 2`: one of two distinct primes is at least `3`. -/
theorem one_lt_totient (z : DistinctPrimes n) : 1 < Nat.totient (z.p * z.q) := by
  rw [z.totient_mul]
  have hp := z.p_prime.two_le
  have hq := z.q_prime.two_le
  have hne := z.p_ne_q
  rcases Nat.lt_or_ge 2 z.p with h | h
  · calc 1 < 2 * 1 := by norm_num
      _ ≤ (z.p - 1) * (z.q - 1) := Nat.mul_le_mul (by omega) (by omega)
  · have h2 : z.p = 2 := by omega
    have h3 : 3 ≤ z.q := by omega
    calc 1 < 1 * 2 := by norm_num
      _ ≤ (z.p - 1) * (z.q - 1) := Nat.mul_le_mul (by omega) (by omega)

/-- A pair of distinct primes is determined by `(p, q)`. -/
theorem ext {z w : DistinctPrimes n} (hp : z.p = w.p) (hq : z.q = w.q) : z = w := by
  rcases z with ⟨⟨⟨⟨p, hp'⟩, hpp⟩, ⟨⟨q, hq'⟩, hqq⟩⟩, hne⟩
  rcases w with ⟨⟨⟨⟨p', _⟩, _⟩, ⟨⟨q', _⟩, _⟩⟩, _⟩
  simp only [DistinctPrimes.p, DistinctPrimes.q] at hp hq
  subst hp hq
  rfl

/-- `Π_n` has no two distinct primes for `n < 2`. -/
theorem isEmpty_of_lt (hn : n < 2) : IsEmpty (DistinctPrimes n) := by
  refine ⟨fun z => ?_⟩
  have h1 := z.p_prime.two_le
  have h2 := z.q_prime.two_le
  have h3 := z.p_lt
  have h4 := z.q_lt
  have h5 := z.p_ne_q
  interval_cases n <;> omega

/-- The pair `(2, 3)` for `n ≥ 2` (the default element of the collection's domain). -/
def default (hn : 2 ≤ n) : DistinctPrimes n :=
  ⟨(⟨⟨2, lt_of_lt_of_le (by norm_num) ((Nat.pow_le_pow_right (by norm_num) hn).trans_eq' rfl)⟩,
      Nat.prime_two⟩,
    ⟨⟨3, lt_of_lt_of_le (by norm_num) ((Nat.pow_le_pow_right (by norm_num) hn).trans_eq' rfl)⟩,
      Nat.prime_three⟩), (by norm_num : (2 : ℕ) ≠ 3)⟩

end DistinctPrimes

/-! ### Encoding pairs of distinct primes -/

/-- Decode `⟨a, b⟩` as a pair of distinct primes of `Π_m`: both components must be `m`-bit
strings (`decodeFin`) reading as distinct primes; anything else is a failure. -/
def decodeDistinctPrimes (m : ℕ) (w : List Bool) : Option (DistinctPrimes m) :=
  match decodeFin m (pairFstD w), decodeFin m (pairSndD w) with
  | some a, some b =>
    if h : (bitsToNat a).Prime ∧ (bitsToNat b).Prime ∧ bitsToNat a ≠ bitsToNat b then
      some ⟨(⟨⟨bitsToNat a, bitsToNat_lt a⟩, h.1⟩, ⟨⟨bitsToNat b, bitsToNat_lt b⟩, h.2.1⟩), h.2.2⟩
    else none
  | _, _ => none

/-- Encode a pair of distinct primes of `Π_m` as `⟨p, q⟩` with `m`-bit numerals. -/
def encodeDistinctPrimes (m : ℕ) (z : DistinctPrimes m) : List Bool :=
  pairEncode (natToList m z.p) (natToList m z.q)

/-- Decoding inverts encoding. -/
theorem decodeDistinctPrimes_encode (m : ℕ) (z : DistinctPrimes m) :
    decodeDistinctPrimes m (encodeDistinctPrimes m z) = some z := by
  unfold decodeDistinctPrimes encodeDistinctPrimes natToList
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, decodeFin_ofFn,
    bitsToNat_natToBits z.p_lt, bitsToNat_natToBits z.q_lt]
  rw [dif_pos ⟨z.p_prime, z.q_prime, z.p_ne_q⟩]
  congr 1

/-- **Decoding is canonical**: a string that `decodeDistinctPrimes m` decodes to `z` is
`encodeDistinctPrimes m z` (the clause `Collection.encD_decD` of the factoring collection;
gate 03b, finding 1).

**Proof sketch.** Both components decode as `m`-bit strings `a`, `b`, so they are `List.ofFn a`,
`List.ofFn b` (`ofFn_of_decodeFin_eq_some`), the numerals of `p = bitsToNat a`, `q = bitsToNat b`
at width `m` (`natToList_length_listToNat`); the first is nonempty (`Π_m` has two distinct
primes only for `m ≥ 2`, `DistinctPrimes.isEmpty_of_lt`), so the string is the pair of its
components (`eq_pairEncode_of_pairFstD_ne`). -/
theorem encodeDistinctPrimes_of_decode {m : ℕ} {w : List Bool} {z : DistinctPrimes m}
    (h : decodeDistinctPrimes m w = some z) : encodeDistinctPrimes m z = w := by
  have hm : 2 ≤ m := by
    by_contra hm
    exact (DistinctPrimes.isEmpty_of_lt (not_le.1 hm)).false z
  have hnum : ∀ a : Fin m → Bool, natToList m (bitsToNat a) = List.ofFn a := fun a => by
    have := natToList_length_listToNat (List.ofFn a)
    rwa [List.length_ofFn, ← bitsToNat_eq_listToNat] at this
  unfold decodeDistinctPrimes at h
  rcases ha : decodeFin m (pairFstD w) with _ | a <;> rcases hb : decodeFin m (pairSndD w) with _ | b <;>
    simp only [ha, hb, reduceCtorEq] at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have hne : pairFstD w ≠ [] := fun h0 => by
    have := length_eq_of_decodeFin_eq_some ha
    rw [h0, List.length_nil] at this
    omega
  show pairEncode (natToList m (bitsToNat a)) (natToList m (bitsToNat b)) = w
  rw [hnum, hnum, ofFn_of_decodeFin_eq_some ha, ofFn_of_decodeFin_eq_some hb]
  exact (eq_pairEncode_of_pairFstD_ne hne).symm

/-! ## Block rejection sampling on coin lists (run-3 audit P7-6) -/

/-- **Block rejection sampling** on a coin list, the common shape of the honest samplers of
the candidates [PS10, Theorem 53.2 (`Z_N^*`, `Z*_{Φ(N)}`), Theorem 61.7, Theorem 63.10 (Blum
primes), Theorem 52.3 (`Z_q`)]: `T` trials, trial `t` reading the first `k` bits of the
`t`-th block of `B` bits of `r` as a number `v` (`listToNat`), accepted iff `E v`; `none` if
every trial is rejected. With `k ≤ B` and `r` uniform, the `T` values are independent and
uniform below `2^k`, so the output is `firstHit E` on `Fin (2^k)` (`statClose_rejectBlocksL`).
Repair (run-3 audit P7-6): the one sampler behind `sampleUnitL` (RSA, Rabin) and
`samplePrimePL` (Rabin); `sampleBelowL` (discrete log) has the same shape. -/
def rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) : Option ℕ :=
  (List.range T).findSome? fun t =>
    if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
    else none

/-- Block rejection sampling unfolded: `rejectBlocksL E k B T r` is the first `some v` over
`t ∈ [0, T)` (`List.findSome?` over `List.range T`) with `v` the number read from the first `k`
bits of the `t`-th block of `B` bits of `r`, kept iff `E v`. -/
theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
      else none :=
  rfl

/-- An accepted value satisfies the test and is below `2^k` (it is read from at most `k`
bits, `listToNat_lt_two_pow`). -/
theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r : List Bool} {v : ℕ}
    (h : rejectBlocksL E k B T r = some v) : E v ∧ v < 2 ^ k := by
  unfold rejectBlocksL at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  split_ifs at ht with hc
  rw [Option.some.injEq] at ht
  subst ht
  refine ⟨hc, lt_of_lt_of_le (listToNat_lt_two_pow _) ?_⟩
  exact Nat.pow_le_pow_right (by norm_num) (List.length_take_le _ _)

/-- **Block rejection sampling is close to uniform on `E`** (lemma C4 of the chapter 2
inventory on coin lists; the sampling clauses of [PS10, Theorems 52.3, 53.2, 61.7, 63.10]):
for `k ≤ B`, a uniform coin string of `T · B` bits and a default `d < 2^k` with `E d`, the
total sampler `(rejectBlocksL E k B T r).getD d` is within `(1 − Pr_{v < 2^k}[E v])^T` of the
uniform element of `{v < 2^k | E v}`. Repair (run-3 audit P7-6): stated once here instead of
in each consumer.

**Proof sketch.** For `r = List.ofFn r'`, `(r.drop (t·B)).take k = List.ofFn (π_t r')` where
`π_t r'` is the `k`-bit prefix of block `t` (`List.ext_get`, `List.getElem_take`,
`List.getElem_drop`, `List.getElem_ofFn`; the length is `k` since `t < T` and `k ≤ B`), so
`rejectBlocksL E k B T r = (firstHit (fun x : Fin (2^k) => E x) (fun t => bitsEquiv k (π_t r'))).map Fin.val`
(`List.map_coe_finRange`, `List.findSome?_map`, `bitsToNat_eq_listToNat`, `bitsEquiv_val`) and
`(·).getD d = Fin.val ((firstHit …).getD ⟨d, hdk⟩)` (`Option.getD_map`). The map
`r' ↦ (π_t r')_t` from `Fin (T·B) → Bool` to `Fin T → Fin k → Bool` pushes the uniform
distribution to the uniform one — it is the first projection of a splitting equivalence
`(Fin (T·B) → Bool) ≃ (Fin T → Fin k → Bool) × (Fin T → Fin (B − k) → Bool)` (`uprob_comp_equiv`,
`uprob_fst`; alternatively `pushesUniform_of_card_fiber`) — as does
`Equiv.piCongrRight (fun _ => bitsEquiv k)`; conclude from `statClose_firstHit` (default
`⟨d, hdk⟩`, `hd`) by `StatClose.comp_pushesUniform` and `StatClose.map Fin.val`. -/
theorem statClose_rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (hkB : k ≤ B)
    {d : ℕ} (hd : E d) (hdk : d < 2 ^ k) :
    StatClose (fun r : Fin (T * B) → Bool => (rejectBlocksL E k B T (List.ofFn r)).getD d)
      (fun e : {v : Fin (2 ^ k) // E (v : ℕ)} => ((e : Fin (2 ^ k)) : ℕ))
      ((1 - uprob fun v : Fin (2 ^ k) => E (v : ℕ)) ^ T) := by
  sorry

end TCSlib.Cryptography.Candidates

## ===== briefs/pass-shelat/inventory-ch2.md =====

# Inventory — [PS10] Chapter 2, *Computational Hardness* (§2.1–§2.13, plus the Appendix items Chapter 2 uses)

Run 1 (understand & design), 2026-10-27. Source: `blueprint/src/references/pass-shelat-2010-ch2.raw.md`
(pages 21–65) and `…-appendix.raw.md`. Read-only survey of the Lean tree; nothing under `TCSlib/` was
touched. Conventions: `n` is the security parameter; "nuPPT" is [PS10, Def 26.8] in the advice
formulation (plan D4); "PPT" is [PS10, Def 23.4/23.5] with the random tape as an input component
(plan D3); `{0,1}^n` is `Fin n → Bool` (plan D5); `Π_n = {p < 2^n | p prime}`; `Z_N^* = (ZMod N)ˣ`;
"negl" = `TCSlib.Cryptography.Negligible`. Paths are relative to the worktree
`/Users/dehmelf/Research/tcslib-pass-shelat`; Mathlib paths are relative to
`.lake/packages/mathlib/Mathlib`.

Scope labels: **core** = mandatory per the plan; **optional** = feasible and useful, or already
formalized (cite only); **deferred** = not needed downstream and/or research-level.

---

## 0. Headline findings for the planners (read first)

**F1. There are no binary-arithmetic machines in the library.** `TCSlib/Complexity` contains no
`FinTM` computing addition, comparison, multiplication, division/mod, gcd, or modular exponentiation on
binary strings (the only counters are `Turing.FinTM.computesFunInTime_incFixed`, `…_lengthBits`,
`…_polyUnary`, `…_polyBits` in `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`, which handle
lengths and fixed-width increments). Every "easy to compute / sample / evaluate / invert with
trapdoor" clause of §2.3 and §2.6–§2.12 (f_mult, Euclid, modexp, Miller–Rabin, SamplePrime, factoring/
DL/RSA/Rabin collections) needs them, and so do the *reductions* of Thms 33.5, 36.3, 55.2, 61.8
(they multiply, divide, take gcds). Building them in the `Build/` style is a research-level effort
(the pairing primitives alone are 7.6k lines). **Recommendation (Q1):** a hypothesis bundle
`TCSlib.Cryptography.Candidates.ArithmeticFP` (fields: `PolyTimeComputable` for binary `mul`,
`divMod`, `xgcd`, `modExp`, comparison, and the decoding of binary numerals), taken as an explicit
hypothesis by every candidate theorem (no axiom; `#print axioms` stays clean), with its discharge a
deferred build target. The asymptotic OWF/collection *definitions* remain machine-based; only the
number-theoretic *instances* are conditional.

**F2. Algorithm 64.2 (universal one-way function) is wrong as printed** and the proof of Theorem 63.1
does not go through for it: `f_universal(⟨M, x⟩) = M(x)` lets an inverter return `⟨M', x'⟩` with a
different machine `M'`, which yields no preimage under `M_g`. The standard (Levin/Goldreich) definition
outputs `⟨M, M(x)⟩`; with it the text's union-bound argument is valid. Formalize the corrected
function (Deviation recorded in the docstring; listed in `text_errors`).

**F3. Security parameter vs input length (Q2).** Thm 35.1's `f'` lives on `({0,1}^n)^{m(n)}` and
Thm 42.2's `g` on `{0,1}^{ℓ₁(n)+ℓ₂(n)}`; the text's `f : {0,1}* → {0,1}*` with hardness "at every n"
cannot be met by these functions at lengths outside the image of `ℓ`. Recommended shape: an
asymptotic one-way function is a family `f n : (Fin (ℓ n) → Bool) → List Bool` with an explicit
polynomial input length `ℓ n = C·(n+1)^c` (default `ℓ n = n`), "easy" = some `FinTM Bool` computes
`pairEncode 1^n (ofFn x) ↦ f n x` within `Ct·(n+1)^ct`, "hard" = for every nuPPT receiving
`pairEncode 1^n (f n x)`, negligible in `n`. For `ℓ n = n` this is the text's definition (the honest
evaluator additionally reads `1^n`, harmless). Alternative: `ℓ` strictly increasing and the evaluator
on bare `x` (recover `n` by search; `computesFunInTime_splitSolveWith` is the model primitive).

**F4. Dyadic samplers are never exactly uniform on `Π_n`, `Z_q`, `Z*_{Φ(N)}`, `Z_N^*`, `QR_N` (Q3).**
Keep the hardness experiments on the *ideal* uniform distributions (as the text), and formalize the
"easy to sample" clauses as PPT samplers within statistical distance `2^{-n}` of uniform (strict
PPT with truncated rejection loops; Deviation). One bridging lemma (any success probability moves by
at most the statistical distance; `distAdv_le_statDist` is the model) connects the two. The needed
density facts are elementary: `|Π_n| ≥ 2^n/(2n)` (Chebyshev), `φ(m)/m ≥ 1/(log₂ m + 1)` (new, for
`Z*_{Φ(N)}`), `φ(pq)/pq ≥ 1/4` (for `Z_N^*`), 4-to-1 squaring (for `QR_N`).

**F5. Rabin needs more than the text states (Q4).** Thms 60.5/60.6/61.7/61.8/63.10 need `p ≠ q`
odd; Thm 61.8 (⇐) needs square roots modulo arbitrary primes but the text only proves `p ≡ 3 (mod 4)`;
Thm 63.10's `Gen` must sample primes `≡ 3 (mod 4)`, whose density is not available in Mathlib (no
Dirichlet-type bound). Formalize the Rabin results for Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`),
with the factoring assumption restricted to that index distribution, and take the density of
`3 (mod 4)` primes as an explicit hypothesis of the `Gen`-efficiency clause of Thm 63.10.

**F6. Primality testing (Q6).** The text relies on "primality testing is in polynomial time" (AKS,
unproved here) for SamplePrime and the `Gen` of Thms 51.1/53.2/57.2/61.7/63.10, and on Miller–Rabin
whose composite-case lemma (50.15b) is deferred by the plan. Recommended: a hypothesis
`PrimalityFP : PolyTimeComputable (fun w => [decide (Nat.ofBits w).Prime])` inside the Q1 bundle;
Miller–Rabin is formalized as a sampler with its prime-case correctness (core) and the composite
bound (deferred). Thms 33.5 and 36.3 are formalized with the one-call / random-planting reductions
that need no primality test (plan decision).

**F7. Uniform position in Thm 35.1 (Q7).** `OneWay.yaoTry` draws `i : Fin q` uniformly; coins of
polynomial length give exact uniformity only for `q` a power of two. Choose `m(n) := 2^{⌈log₂(2n q(n))⌉}`
(any larger `m` is allowed by the theorem), or route through Q3's statistical bridge.

**F8. Concrete-layer additions.** Garg files are frozen; new concrete lemmas go in a new file
`TCSlib/Cryptography/Candidates/Concrete.lean` (reductions and probability lemmas used by the
candidates) and in `TCSlib/Cryptography/Asymptotic/OneWay.lean` itself (small ones). List in §4.

**F9. Closure/Repetition requirements consumed by Chapter 2** are listed in §5 so that the machine
layer (Randomized/Closure.lean, Repetition.lean) can be sized before the skeletons are written.

---

## 1. Inventory table

Columns: ID · kind · title · proposed file (under `TCSlib/`) · difficulty 1–5 · scope · existing Lean
(short; full paths in §2) · note key. `(cite)` = already formalized, nothing to do beyond citing.

| ID | kind | title | proposed file | diff | scope | existing Lean |
|---|---|---|---|---|---|---|
| Def-21.1 | definition | Algorithm = deterministic TM over {0,1} | (cite) `Complexity/TuringMachine/Finite.lean` | 1 | optional | `Turing.FinTM Bool` |
| Def-21.2 | definition | Running time; polynomial time | (cite) `Complexity/ClassNP/PolyTime.lean` | 1 | optional | `FinTM.ComputesFunInTime`, `Complexity.PolyTimeComputable`, `Complexity.P` |
| Def-21.3 | definition | Deterministic computation of f | (cite) | 1 | optional | `FinTM.ComputesFunInTime`, `FinTM.Computes` |
| Rem-22.1 | claim | §2.1.1 background: Halting, time hierarchy, SAT | (cite) | 1 | optional | `Complexity.HALT_not_computable`, `Complexity.P_ssubset_EXP`, `Complexity.SAT_NPComplete` |
| Def-23.4 | definition | PPT (randomized TM with coin input) | `Complexity/Randomized/PPT.lean` | 3 | core | pattern: `FinTM.DecidesWithAdviceInTime` |
| Def-23.5 | definition | Running time of a randomized TM (worst case over coins) | `Complexity/Randomized/PPT.lean` | 1 | core | — |
| Def-24.6 | definition | PPT computes f with probability 1 | `Complexity/Randomized/PPT.lean` | 2 | core | — (needs C7) |
| Rem-24.2 | claim | Majority amplification 1/2+1/poly → 1−2^{-n} | `Complexity/Randomized/Repetition.lean` | 4 | deferred | — (Chernoff) |
| Def-24.7 | definition | Efficient private-key encryption | `Cryptography/Asymptotic/Encryption.lean` | 2 | core | — |
| Def-26.8 | definition | Non-uniform PPT (advice form) | `Complexity/Randomized/NonUniform.lean` | 3 | core | pattern: `FinTM.DecidesWithAdviceInTime`, `Complexity.PAdvicePoly` |
| Rem-26.2 | claim | Machine-sequence ⟺ advice formulation of nuPPT | — | 4 | deferred | `Turing.timed_universal` (for ⇒) |
| Claim-26.3 | infrastructure | nuPPT closure calculus (pre/post, pairing, coins, advice, repetition) | `Complexity/Randomized/{Closure,Repetition}.lean` | 5 | core | `computesFunInTime_comp/cond`, `exists_loopFindTM`, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM`, `PolyTimeComputable.*` |
| Def-26.1 | definition | Worst-case one-way function | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `invProb` |
| Rem-27.1 | claim | NP ⊄ BPP ⟺ worst-case OWF exist ("show this!") | — | 5 | deferred | `Complexity.NP` |
| Def-27.2 | definition | Negligible / non-negligible | (cite) `Cryptography/Foundations/Negligible.lean` | 1 | optional | `Negligible`, `not_negligible_iff`, `negligible_two_pow_neg` |
| Def-27.3 | definition | Strong one-way function | `Cryptography/Asymptotic/OneWay.lean` | 3 | core | `invProb` |
| Rem-28.1 | claim | (t,s,ε)-one-wayness (concrete security) | (cite) | 1 | optional | `invProb` (the concrete layer is this) |
| Def-28.4 | definition | Weak one-way function | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `invProb` |
| Def-29.1 | definition | f_mult | `Cryptography/Candidates/Factoring.lean` | 1 | core | — |
| Rem-29.2 | claim | f_mult is not strongly one-way (3/4 attack) | — | 2 | deferred | — |
| Def-29.3 | definition | Π_n and the uniform distribution on it | `Cryptography/NumberTheory/Chebyshev.lean` | 1 | core | `Nat.primesBelow`, `Nat.primeCounting'` |
| Asm-30.1 | assumption | Factoring assumption | `Cryptography/Candidates/Factoring.lean` | 2 | core | `uprob`, `Negligible` |
| Thm-31.3 | theorem | Chebyshev: π(x) > x/(2 log₂ x) | `Cryptography/NumberTheory/Chebyshev.lean` | 4 | core | `Nat.four_pow_lt_mul_centralBinom`, `Nat.prod_pow_factorization_centralBinom`, `Nat.pow_factorization_choose_le`, `Nat.primesBelow_card_eq_primeCounting'` |
| Claim-32.4 | claim | p^{ν_p(C(2x,x))} ≤ 2x | (cite) | 1 | optional | `Nat.pow_factorization_choose_le`, `Nat.factorization_choose_le_log` |
| Claim-33.1 | corollary | Prime density: \|Π_n\| ≥ 2^n/(2n) | `Cryptography/NumberTheory/Chebyshev.lean` | 3 | core | as Thm-31.3 |
| Rem-33.2 | claim | Primality testing in polynomial time (AKS) | hypothesis in `Cryptography/Candidates/Arithmetic.lean` | 5 | deferred | — |
| Thm-33.5 | theorem | Factoring ⟹ f_mult weakly one-way | `Cryptography/Candidates/Factoring.lean` | 3 | core | `uprob_and_le_mul`, `uprob_pi_forall`, `not_negligible_iff` + C1 |
| Alg-33.6 | algorithm | A′ (and the one-call A″) | `Cryptography/Candidates/Factoring.lean` | 1 | core | — |
| Claim-34.1 | claim | f_mult(x′,y′) = pq ⟹ x′ ∈ {p,q} | `Cryptography/Candidates/Factoring.lean` | 2 | core | `Nat.Prime.dvd_mul`, `Nat.Prime.eq_one_or_self_of_dvd` |
| Thm-35.1 | theorem | Weak → strong (Yao direct product) | `Cryptography/Asymptotic/OneWay.lean` | 4 | core | `OneWay.yao_amplification`, `prodFun`, `yaoInverter`, `invProb_prodFun_le`, `one_sub_invProb_yaoInverter_le` |
| Thm-35.2 | theorem | g(x,y) = (f x, f y) strong if f strong | `Cryptography/Asymptotic/OneWay.lean` | 3 | core | pattern `OneWay.invProb_pad_le` + C2 |
| Thm-36.3 | theorem | Factoring ⟹ f_mult^{4n³} strongly one-way | `Cryptography/Candidates/Factoring.lean` | 3 | core | `uprob_update`, `sum_uprob_eq_card_mul`, `uprob_pi_forall`, `uprob_and_le_mul` + C3, C8 |
| Claim-36.2 | claim | (1−1/(4n²))^{4n³} ≤ e^{−n} | `Cryptography/Candidates/Concrete.lean` | 1 | core | `Real.one_sub_le_exp_neg`, `Real.exp_nat_mul` (pattern `yao_amplification_exp`) |
| Alg-37.4 | algorithm | A′(z′) with planting (random-position variant) | `Cryptography/Candidates/Factoring.lean` | 1 | core | `uprob_update` |
| Alg-38.5 | algorithm | A₀(f, y) and its 2nm²p(n)-fold repetition | (cite) `Cryptography/OneWayFunctions/Amplification.lean` | 1 | optional | `OneWay.yaoTry`, `OneWay.yaoInverter` |
| Claim-38.2 | claim | PS10 parameters instantiate `yao_amplification` | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `OneWay.yao_amplification`, exp bounds |
| Claim-39.1 | claim | Pr[A fails \| x good] ≤ (1−θ)^T ≈ e^{−n} | (cite) | 1 | optional | `OneWay.one_sub_invProb_yaoInverter_le` |
| Claim-39.2 | claim | Many good elements: \|G_n\| ≥ 2^n(1−1/(2q)) | (cite) | 1 | optional | `OneWay.invProb_prodFun_le` |
| Def-41.1 | definition | Collection of one-way functions | `Cryptography/Asymptotic/Collections.lean` | 4 | core | `HardcoreBit.PushesUniform`, `invProb` (pattern) |
| Thm-42.2 | theorem | Collection of OWFs ⟺ strong OWF | `Cryptography/Asymptotic/Collections.lean` | 4 | core | `PolyTimeComputable.pairEncode/.comp`, `uprob_prod`, `PushesUniform.uprob_eq` |
| Fact-42.1 | fact | Modular arithmetic laws | (cite) | 1 | optional | `Nat.add_mod`, `Nat.mul_mod` |
| Alg-43.2 | algorithm | ExtendedEuclid | `Cryptography/NumberTheory/Euclid.lean` | 2 | core | `Nat.xgcd`, `Nat.gcdA/gcdB`, `Nat.gcd_eq_gcd_ab`, `ZMod.inv` |
| Claim-43.3 | claim | ≤ 2n recursive calls when a < 2^n | `Cryptography/NumberTheory/Euclid.lean` | 3 | core | — |
| Claim-44.4 | claim | gcd(a,b) = gcd(b, a mod b) | (cite) | 1 | optional | `Nat.gcd_rec`, `Nat.gcd_comm` |
| Claim-44.5 | claim | Correctness ax+by = gcd (induction) | `Cryptography/NumberTheory/Euclid.lean` | 2 | core | `Nat.gcd_eq_gcd_ab` (Mathlib's own xgcd) |
| Rem-43.6 | claim | Euclid runs in poly(log a + log b) (machine) | Q1 hypothesis | 5 | deferred | — |
| Alg-45.5 | algorithm | Modular exponentiation (repeated squaring) | `Cryptography/NumberTheory/ModExp.lean` | 2 | core | `Nat.pow_mod`, `Nat.ModEq.pow` |
| Thm-45.6 | theorem | ≤ 2(⌊log₂ x⌋+1) modular multiplications; O(log x log² N) | `Cryptography/NumberTheory/ModExp.lean` | 2 | optional | `TimeM` (`Cryptography/RSA.lean`) cost model, optional |
| Def-46.7 | definition | Group | (cite) | 1 | optional | `Group`, `CommGroup` |
| Ex-46.1 | example | (Z_N, +) | (cite) | 1 | optional | `ZMod N` |
| Thm-46.8 | theorem | (Z_N^*, ×) is a group; Z_N^* = {x ∈ [1,N−1] \| gcd(x,N)=1} | `Cryptography/NumberTheory/Units.lean` | 1 | optional | `(ZMod N)ˣ`, `ZMod.unitsEquivCoprime`, `ZMod.unitOfCoprime`, `ZMod.mul_inv_eq_gcd` |
| Def-46.9 | definition | Prime | (cite) | 1 | optional | `Nat.Prime` |
| Claim-47.1 | claim | p ∣ ab ⟹ p ∣ a ∨ p ∣ b (exercise) | (cite) | 1 | optional | `Nat.Prime.dvd_mul` |
| Claim-47.2 | claim | Φ(p) = p−1; Φ(pq) = (p−1)(q−1) (p ≠ q) | `Cryptography/NumberTheory/Units.lean` | 1 | core | `Nat.totient_prime`, `Nat.totient_mul`, `Nat.coprime_primes`, `ZMod.card_units_eq_totient` |
| Thm-47.10 | theorem | Euler | (cite) | 1 | optional | `ZMod.pow_totient`, `Nat.ModEq.pow_totient` |
| Cor-48.11 | corollary | Fermat | (cite) | 1 | optional | `ZMod.pow_card_sub_one_eq_one` |
| Cor-48.12 | corollary | a^x ≡ a^{x mod Φ(N)} (mod N), a ∈ Z_N^* | `Cryptography/NumberTheory/Units.lean` | 1 | core | `ZMod.pow_totient`, `Nat.div_add_mod` |
| Rem-48.2 | claim | Given Φ(N), a^x mod N efficient for any x (machine) | Q1 hypothesis | 5 | deferred | Cor-48.12 + Alg-45.5 |
| Ex-48.3 | example | 2^{61241} mod 21 (garbled) | — | 1 | optional | `decide` |
| Def-49.1 | definition | Miller–Rabin liar set L_N (corrected) | `Cryptography/NumberTheory/Primality.lean` | 2 | core | — |
| Alg-49.13 | algorithm | Miller–Rabin test (t rounds) | `Cryptography/NumberTheory/Primality.lean` | 2 | core | `uprob_pi_forall` |
| Thm-49.14 | theorem | MR correct on primes; errs on composites w.p. ≤ 2^{−t} | `Cryptography/NumberTheory/Primality.lean` | 2 | core (prime and composite; the composite error bound `uprob_millerRabin_le` for every composite `N > 2`, proved; gate 03f2, F02) | `uprob_pi_forall` |
| Lem-50.15a | lemma | N odd prime ⟹ L_N = Z_N^* | `Cryptography/NumberTheory/Primality.lean` | 3 | core | `ZMod.pow_card_sub_one_eq_one`, `mul_self_eq_one_iff`, `sq_eq_sq_iff_eq_or_eq_neg` |
| Lem-50.15b | lemma | N odd composite ⟹ \|L_N\| ≤ (N−1)/2 | `Cryptography/NumberTheory/Primality.lean` | 5 | core (proved as `two_mul_card_mrLiars_le`, odd composites, non-strict `≤`; the oddness restriction is a convenience, gate 03f2, F01–F02) | `Subgroup.card_subgroup_dvd_card` |
| Rem-49.3 | claim | Infinitely many Carmichael numbers | — | 5 | deferred | (weaker) `Nat.exists_infinite_pseudoprimes` |
| Rem-50.2 | claim | AKS deterministic primality | — | 5 | deferred | — |
| Alg-50.16 | algorithm | SamplePrime(n) (truncated strict-PPT form) | `Cryptography/NumberTheory/Primality.lean` | 3 | core | C4, C8 |
| Lem-51.17 | lemma | SamplePrime: uniform prime, failure ≤ 2^{−n}, poly time | `Cryptography/NumberTheory/Primality.lean` | 3 (+4 machine) | core | C4; Claim-33.1; `exists_loopFindTM` |
| Thm-51.1 | theorem | Factoring collection | `Cryptography/Candidates/Factoring.lean` | 3 | core | Lem-51.17, Claim-34.1, Def-41.1 |
| Def-52.1 | definition | Generator of a group; Gen_G | (cite) | 1 | optional | `Subgroup.zpowers`, `IsCyclic.exists_generator` |
| Rem-52.2 | claim | Prime-order groups; Z_p^* order p−1; safe primes, squares subgroup | `Cryptography/NumberTheory/Units.lean` | 2 | optional | `isCyclic_of_prime_card`, `ZMod.card_units`, `orderOf_dvd_card` |
| Asm-52.2 | assumption | Discrete-log assumption (relative to a group family) | `Cryptography/Candidates/DiscreteLog.lean` | 3 | core | — |
| Thm-52.3 | theorem | DL collection | `Cryptography/Candidates/DiscreteLog.lean` | 3 | core | Def-41.1, Asm-52.2 |
| Claim-53.1 | claim | Safe-prime generator test g ≠ ±1, g^q ≠ 1 | `Cryptography/NumberTheory/Units.lean` | 2 | optional | `orderOf_dvd_of_pow_eq_one`, `ZMod.card_units` |
| Claim-53.2 | claim | x ↦ g^x : Z_q → G_q is a bijection (DL is a permutation) | `Cryptography/Candidates/DiscreteLog.lean` | 2 | optional | `zmodCyclicMulEquiv`, `orderOf_eq_card_of_forall_mem_zpowers`, `pow_eq_pow_iff_modEq` |
| Asm-53.1 | assumption | RSA assumption | `Cryptography/Candidates/RSA.lean` | 3 | core | `ZMod.unitsEquivCoprime` |
| Thm-53.2 | theorem | RSA collection | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-54.3, `HardcoreBit.pushesUniform_equiv`, C9 |
| Thm-54.3 | theorem | x ↦ x^e permutes Z_N^* when e ∈ Z*_{Φ(N)} | `Cryptography/NumberTheory/Units.lean` | 2 | core | `ZMod.pow_totient`, `RSA.rsa_crt_pow`, `RSA.rsa_correctness` |
| Def-55.1 | definition | Collection of one-way permutations | `Cryptography/Asymptotic/Collections.lean` | 1 | core | Def-41.1 |
| Thm-55.2 | theorem | RSA assumption ⟹ factoring assumption | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-54.3, `ZMod.inv`/`Nat.gcdA`, `uprob_fst` |
| Alg-55.3 | algorithm | A′(N, e, y) via factoring | `Cryptography/Candidates/RSA.lean` | 1 | core | — |
| Def-56.1 | definition | Collection of trapdoor permutations | `Cryptography/Asymptotic/Collections.lean` | 2 | core | Def-55.1 |
| Thm-57.2 | theorem | RSA is a TDP collection ("exercise") | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-53.2, Thm-54.3, Alg-43.2 |
| Def-57.0 | definition | QR_p | `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | core | `MonoidHom.range`, `powMonoidHom` |
| Lem-57.1 | lemma | QR_p subgroup of size (p−1)/2; two roots each | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | `legendreSym.card_sqrts`, `ZMod.euler_criterion`, `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.card_units` |
| Claim-58.1 | claim | x² = y² in Z_p ⟹ x = ±y | (cite) | 1 | optional | `sq_eq_sq_iff_eq_or_eq_neg` |
| Thm-58.2 | theorem | p = 4k+3: (y^{k+1})² = y for y ∈ QR_p | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.pow_card_sub_one_eq_one` |
| Ex-58.3 | exercise | Square roots for p ≡ 1 (mod 4) | — | 4 | deferred | — |
| Thm-58.3 | theorem | Chinese Remainder (k pairwise coprime moduli) | (cite; k = 2 bridge) `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | optional | `ZMod.chineseRemainder`, `Nat.chineseRemainderOfList`, `Nat.chineseRemainder` |
| Claim-59.1 | claim | Explicit CRT inverse y = Σ b_i n_i a_i; two Euclid calls | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | optional | `Nat.chineseRemainder` |
| Ex-59.2 | example | p = 7, q = 11 | — | 1 | optional | `decide` |
| Def-59.3 | definition | QR_N | `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | core | — |
| Thm-59.4 | theorem | x ∈ QR_N ⟺ x mod p ∈ QR_p ∧ x mod q ∈ QR_q | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.chineseRemainder`, `Units.map`, `RingEquiv.map_pow` |
| Thm-60.5 | theorem | Squaring on Z_N^* is 4-to-1 (p ≠ q odd) | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | Lem-57.1, Thm-59.4 |
| Cor-60.6 | corollary | \|QR_N\| = \|Z_N^*\|/4 | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `Finset.card_eq_sum_card_fiberwise` |
| Claim-60.7 | claim | Roots mod N from roots mod p, q via CRT | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.chineseRemainder` |
| Ex-60.8 | example | N = 77 example (garbled) | — | 1 | optional | `decide` |
| Thm-61.7 | theorem | Rabin collection is one-way under factoring | `Cryptography/Candidates/Rabin.lean` | 4 | core | C5, C6, Claim-62.1 |
| Thm-61.8 | theorem | Rabin one-way ⟺ factoring (Blum integers) | `Cryptography/Candidates/Rabin.lean` | 4 (⇒) / 3 (⇐, Blum) | core | Thm-58.2, Claim-60.7, C6 |
| Alg-62.9 | algorithm | Factoring adversary A′(N) from a root finder | `Cryptography/Candidates/Rabin.lean` | 1 | core | — |
| Claim-62.1 | claim | x² ≡ z², z ≢ ±x ⟹ gcd(x−z, N) ∈ {p,q} | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `Nat.Prime.dvd_mul`, `Int.gcd`, `ZMod.chineseRemainder` |
| Claim-62.2 | claim | Half the time the root differs from ±x (symmetry lemma) | `Cryptography/Candidates/Rabin.lean` · `rabin_symmetry` (corrected on gate 03f1, finding 2; audited at gate 03f2) | 3 | core | `uprob_comp_equiv`, `uprob_or_le` |
| Thm-63.10 | theorem | Rabin TDP on Blum integers | `Cryptography/Candidates/Rabin.lean` | 4 | core | Claim-63.1, C5, Thm-58.2, `ZMod.euler_criterion` |
| Claim-63.1 | claim | Blum N: each square has exactly one root in QR_N | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | `ZMod.exists_sq_eq_neg_one_iff`, Lem-57.1, Thm-59.4 |
| Thm-63.1 | theorem | Universal one-way function (corrected) | `Cryptography/Asymptotic/Universal.lean` | 5 | core | `Turing.timed_universal(_concrete)`, `EffectiveMachineCode`, `exists_effectiveMachineCode`, `MachineCode.decode_encode_pad`, `exists_codeTM`, `FinTM.one_work_tape_binary`, `OneWay.card_log_bits_le` |
| Alg-64.2 | algorithm | f_universal (definition + poly-time computability) | `Cryptography/Asymptotic/Universal.lean` | 4 | core | `Turing.timed_universal_concrete`, `universalBlockBound`, `computesFunInTime_polyBits`, `PolyTimeComputable.pairEncode` |
| Lem-64.3 | lemma | Strong OWF computable in O(n²) (padding) | `Cryptography/Asymptotic/Universal.lean` | 3 | core | `OneWay.pad`, `OneWay.padInverter`, `OneWay.invProb_pad_le`, `FinTM.one_work_tape_binary`, `exists_codeTM` |
| Claim-65.1 | claim | PickG: Pr[code field = ⟨M_g⟩] ≥ 1/n | `Cryptography/Asymptotic/Universal.lean` | 2 | core | `uprob_eq_one_div_card`, `OneWay.card_log_bits_le`, `decode_encode_pad` |
| Claim-65.2 | claim | Union bound 1/n³ + (1−1/n) and the contradiction | `Cryptography/Asymptotic/Universal.lean` | 2 | core | `uprob_or_le`, `not_negligible_iff` |
| App-A.1 | fact | Union bound | (cite) | 1 | optional | `uprob_or_le`, `uprob_exists_le` |
| App-A.2 | fact | Markov; Chebyshev's inequality | (cite) | 1 | optional | `HardcoreBit.uprob_mul_le_uexp`, `HardcoreBit.uprob_le_abs_le` |
| Thm-188.7 | theorem | Chernoff bound | — | 4 | deferred | `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` (measure-theoretic Hoeffding) |
| Lem-189.8 | lemma | Majority vote (garbled statement) | — | 4 | deferred | — |
| App-A.3 | fact | Pairwise-independent sampling inequality | (cite) | 1 | optional | `HardcoreBit.chebyshev_pairwise(_ident)` |
| Thm-189.9 | theorem | Cauchy–Schwarz | (cite) | 1 | optional | `Finset.sum_mul_sq_le_sq_mul_sq` |
| Def-191.10 | definition | DP (= P) | (cite) | 1 | optional | `Complexity.P` |
| Def-191.11 | definition | NP (witness relation, \|y\| ≤ p(\|x\|)) | (cite) | 1 | optional | `Complexity.NP`, `Complexity.mem_NP_iff_exists_length_le` |
| Def-192.12 | definition | BPP | `Complexity/Randomized/PPT.lean` | 2 | deferred | — |

---

## 2. Statements, existing Lean, bridges, and text issues (one entry per item)

Full paths of the existing declarations cited below:

* `Turing.FinTM`, `Turing.FinTM.ComputesInTime`, `.ComputesFunInTime`, `.Computes`, `.ComputesInTime.mono`, `.computesInTime_iff` — `TCSlib/Complexity/TuringMachine/Finite.lean`.
* `Complexity.PolyTimeComputable`, `Complexity.PolyBound`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.comp`, `.output_length_le` — `TCSlib/Complexity/ClassNP/PolyTime.lean`.
* `Complexity.PolyTimeComputable.pairEncode`, `.pairMapSnd`, `.append`, `Complexity.polyTimeComputable_{const,prepend,unary,polyUnary,pairFstD,pairSndD,pairConcat,pairSwap,ite,and,lenLe,lenEq,of_linear}`, `Complexity.pairFstD`, `Complexity.pairSndD`, `Complexity.pairMapSnd` — `TCSlib/Complexity/ClassNP/PolyTimePairing.lean`.
* `Complexity.mem_P_iff_polyTimeComputable`, `preimage_mem_P`, `mem_P_of_test`, `test_of_mem_P`, `inter_mem_P`, `union_mem_P` — `TCSlib/Complexity/ClassNP/PClosure.lean`.
* `Complexity.P`, `Complexity.DTIME`, `Turing.FinTM.DecidesInTime` — `TCSlib/Complexity/ClassP/{P,DTIME}.lean`.
* `Complexity.NP`, `Complexity.P_subset_NP`, `Complexity.mem_NP_iff_exists_length_le` — `TCSlib/Complexity/ClassNP/NP.lean`.
* `Turing.FinTM.DecidesWithAdviceInTime`, `Complexity.DTIMEAdvice`, `Complexity.PAdvicePoly`, `Complexity.P_subset_PAdvicePoly` — `TCSlib/Complexity/CircuitComplexity/Advice.lean`.
* `Turing.pairEncode`, `Turing.pairDecode`, `Turing.pairEncode_injective`, `Turing.length_pairEncode`, `Turing.CodeTM`, `Turing.CodeTM.toFinTM`, `Turing.CodeTM.serialize`, `Turing.MachineCode` (`encode`, `decode`, `decode_encode_pad`), `Turing.MachineCode.decode_encode`, `Turing.EffectiveMachineCode` (`canonizer`, `canonizerTime`, `canonizer_computes`), `Turing.exists_codeTM`, `Turing.length_bits_le_self` — `TCSlib/Complexity/TuringMachine/Encoding.lean`.
* `Turing.exists_effectiveMachineCode` — `TCSlib/Complexity/TuringMachine/MathlibBridge.lean:1099`.
* `Turing.universal`, `Turing.timed_universal`, `Turing.timed_universal_concrete` — `TCSlib/Complexity/TuringMachine/Universal.lean`; `Turing.universalBlockBound` (= `3·|serialize| + 5·(numStates+1) + 20`) — `TCSlib/Complexity/TuringMachine/UniversalBlock.lean:750`.
* `Turing.FinTM.one_work_tape_binary` (`M.ComputesFunInTime f T → ∃ M' c, M'.k = 1 ∧ M'.ComputesFunInTime f (fun n => c*(T n+1)^2)`) — `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:965`.
* `Turing.FinTM.computesFunInTime_{id,const,ifEq,comp}`, `Turing.FinTM.exists_comp_on_image`, `exists_comp_partial`, `exists_cond` — `TCSlib/Complexity/TuringMachine/Composition.lean`.
* `Turing.FinTM.computesFunInTime_cond` — `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:711`.
* `Turing.FinTM.exists_loopTM`, `exists_loopFindTM`, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM` — `TCSlib/Complexity/TuringMachine/Build/Loop.lean` (lines 2519, 2633, 5508, 5645, 5691).
* `Turing.FinTM.computesFunInTime_{prepend,lengthBits,polyUnary,polyBits,pairEncodeFixed,pairFst,pairSnd,pairValid,pairConcat,pairDup,pairMapSnd,pairLenCheck,stripLast,splitSolve,incFixed,splitSolveWith,unaryToken,appendBit}` — `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
* `Complexity.HALT_not_computable` — `TCSlib/Complexity/Uncomputability/Halting.lean:194`; `Complexity.P_ssubset_EXP`, `Complexity.P_ne_EXP` — `TCSlib/Complexity/TimeHierarchy/Separation.lean`; `Complexity.SAT_NPComplete`, `Complexity.SAT3_NPComplete` — `TCSlib/Complexity/CookLevin/Hardness.lean`.
* `TCSlib.Cryptography.Negligible`, `Noticeable`, `Negligible.{mono,add,mul,mul_pow,const_mul}`, `negligible_two_pow_neg`, `Noticeable.not_negligible`, `not_negligible_iff`, `not_negligible_sub`, `exists_not_negligible_not_noticeable` — `TCSlib/Cryptography/Foundations/Negligible.lean`.
* `TCSlib.Cryptography.uprob`, `uexp`, `uprob_eq_card_filter`, `uprob_eq_uexp`, `uprob_nonneg`, `uprob_le_one`, `uprob_true`, `uprob_false`, `uprob_not`, `uprob_mono`, `uprob_or_le`, `uprob_exists_le`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `half_le_uprob_good`, `abs_sub_le_sum_hybrids`, `exists_hybrid_gap` — `TCSlib/Cryptography/Foundations/Probability.lean`.
* `TCSlib.Cryptography.invProb`, `predProb`, `acceptProb`, `distAdv`, `acceptProb_comp_equiv`, `uprob_comp_eq_sum_map`, `distAdv_le_statDist` — `TCSlib/Cryptography/Foundations/Experiments.lean`.
* `TCSlib.Cryptography.OneWay.{uprob_congr,uexp_mono,uexp_add,uexp_const_mul,uexp_const,uexp_indicator,uprob_and_le_mul,sum_uprob_eq_card_mul,uprob_pi_forall,uprob_update,uprob_eq_one_div_card}` — `TCSlib/Cryptography/OneWayFunctions/Basic.lean`.
* `TCSlib.Cryptography.OneWay.{prodFun,yaoTry,yaoInverter,yaoTryProb,yaoBad,yaoInverter_spec,prodFun_update,invProb_prodFun_le,one_sub_invProb_yaoInverter_le,yao_amplification,yao_amplification_exp}` — `TCSlib/Cryptography/OneWayFunctions/Amplification.lean`.
* `TCSlib.Cryptography.OneWay.{pad,padInverter,invProb_pad_le,tableInverter,invProb_tableInverter,card_log_bits_le,exists_inverter_log_output}` — `TCSlib/Cryptography/OneWayFunctions/OutputLength.lean`.
* `TCSlib.Cryptography.OneWay.{patch,patchInverter,invProb_patch_le,invProb_patch_le_of_correction,exists_correction,invProb_update_le}` — `TCSlib/Cryptography/OneWayFunctions/Robustness.lean`.
* `TCSlib.Cryptography.HardcoreBit.{PushesUniform,PushesUniform.uprob_eq,PushesUniform.comp,pushesUniform_equiv,pushesUniform_id,pushesUniform_add_right}` — `TCSlib/Cryptography/HardcoreBit/Basic.lean`; `TCSlib.Cryptography.HardcoreBit.{uprob_mul_le_uexp,uprob_le_abs_le,chebyshev_pairwise,chebyshev_pairwise_ident}` — `TCSlib/Cryptography/HardcoreBit/PairwiseIndependence.lean`.
* `RSA.{rsa_core,rsa_zmod_of_factor,rsa_zmod_p,rsa_zmod_q,rsa_crt,rsa_crt_pow,PublicKey,SecretKey,encrypt,decrypt,rsa_correctness}`, `TimeM` — `TCSlib/Cryptography/RSA.lean` (legacy; no policy header; `SecretKey` carries `p ≠ q` and `e·d = 1 + k(p−1)(q−1)`).
* Mathlib: `Nat.xgcd`, `Nat.gcdA`, `Nat.gcdB`, `Nat.gcd_eq_gcd_ab`, `Nat.exists_mul_emod_eq_gcd`, `Nat.exists_mul_emod_eq_one_of_coprime` (`Data/Int/GCD.lean`); `Nat.gcd_rec` (Lean core `Init/Data/Nat/Gcd.lean`); `ZMod.inv` (defined through `Nat.gcdA`), `ZMod.mul_inv_eq_gcd`, `ZMod.unitOfCoprime`, `ZMod.unitsEquivCoprime`, `ZMod.chineseRemainder : ZMod (m*n) ≃+* ZMod m × ZMod n` (`Data/ZMod/Basic.lean`); `ZMod.pow_totient`, `Nat.ModEq.pow_totient`, `ZMod.pow_card_sub_one_eq_one`, `ZMod.card_units`, `FiniteField.pow_dichotomy`, `FiniteField.unit_isSquare_iff` (`FieldTheory/Finite/Basic.lean`); `ZMod.card_units_eq_totient`, `Nat.totient_prime`, `Nat.totient_mul`, `Nat.totient_eq_card_coprime` (`Data/Nat/Totient.lean`); `Nat.coprime_primes`, `Nat.Prime.dvd_mul`, `Nat.decidablePrime` (`Data/Nat/Prime/{Basic,Defs}.lean`); `Nat.primeCounting`, `Nat.primeCounting'`, `Nat.primesBelow`, `Nat.primesBelow_card_eq_primeCounting'`, `Nat.primeCounting'_add_le` (upper bound only) (`NumberTheory/PrimeCounting.lean`, `NumberTheory/SmoothNumbers.lean`); `Nat.exists_prime_lt_and_le_two_mul`, `Nat.centralBinom_le_of_no_bertrand_prime` (`NumberTheory/Bertrand.lean`); `Nat.four_pow_lt_mul_centralBinom`, `Nat.four_pow_le_two_mul_self_mul_centralBinom`, `Nat.centralBinom_eq_two_mul_choose` (`Data/Nat/Choose/Central.lean`); `Nat.factorization_choose_le_log`, `Nat.pow_factorization_choose_le`, `Nat.factorization_choose_le_one`, `Nat.prod_pow_factorization_choose`, `Nat.prod_pow_factorization_centralBinom` (`Data/Nat/Choose/Factorization.lean`); `primorial_le_4_pow` (`NumberTheory/Primorial.lean`); `ZMod.euler_criterion`, `ZMod.euler_criterion_units`, `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.exists_sq_eq_neg_one_iff`, `legendreSym.card_sqrts` (`NumberTheory/LegendreSymbol/Basic.lean`); `sq_eq_sq_iff_eq_or_eq_neg`, `Units.sq_eq_sq_iff_eq_or_eq_neg`, `mul_self_eq_one_iff` (`Algebra/Ring/Commute.lean`); `IsCyclic.exists_generator`, `isCyclic_of_prime_card`, `orderOf_eq_card_of_forall_mem_zpowers`, `zmodCyclicMulEquiv` (`GroupTheory/SpecificGroups/Cyclic.lean`); `orderOf_dvd_card`, `pow_card_eq_one` (`GroupTheory/OrderOfElement.lean`); `instance : IsCyclic (ZMod p)ˣ` (`RingTheory/ZMod/UnitsCyclic.lean`, `RingTheory/IntegralDomain.lean`); `Nat.chineseRemainder` (`Data/Nat/ModEq.lean`), `Nat.chineseRemainderOfList`, `Nat.chineseRemainderOfFinset` (`Data/Nat/ChineseRemainder.lean`); `Nat.ProbablePrime`, `Nat.FermatPsp`, `Nat.exists_infinite_pseudoprimes` (`NumberTheory/FermatPsp.lean`); `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` (`Probability/Moments/SubGaussian.lean`); `Finset.sum_mul_sq_le_sq_mul_sq` (`Algebra/Order/BigOperators/Ring/Finset.lean`); `Real.one_sub_le_exp_neg`, `Real.exp_nat_mul`. **Absent from this Mathlib revision:** Miller–Rabin / strong pseudoprimes, any lower bound on `π(x)`, `ZMod.prodEquivPi`, `Nat.powMod`, a density bound for primes `≡ 3 (mod 4)`, a lower bound on `φ(m)/m`.

### §2.1 Efficient computation and adversaries

**Def-21.1 (Algorithm).** An algorithm is a deterministic Turing machine with input and output over `{0,1}`. — Existing: `Turing.FinTM Bool` (bundled finite multi-tape TM, append-only output tape). No work; cite. Deviation already recorded in the complexity library (multi-tape, binary alphabet).

**Def-21.2 (Running time, polynomial time).** `A` runs in time `T` if for all `x`, `A(x)` halts within `T(|x|)` steps; polynomial time if `T(n) = n^c` for some `c`. — Existing: `FinTM.ComputesFunInTime f T`, `Complexity.PolyTimeComputable f` (bound `C·(n+1)^c`), `Complexity.P` (`n^c + 1`). The text's literal `n^c` is degenerate at `n = 0` (`Complexity.DTIME_eq_empty_of_exists_zero`); the campaign uses `C·(n+1)^c` everywhere (brief §2). Cite.

**Def-21.3 (Deterministic computation).** `A` computes `f` if for all `x`, `A(x)` outputs `f(x)`. — Existing: `FinTM.ComputesFunInTime`, `FinTM.Computes`. Cite.

**Rem-22.1 (§2.1.1 hard problems).** (i) Halting is uncomputable; (ii) the time hierarchy gives functions computable in exponential but not polynomial time; (iii) SAT is NP-complete, conjectured not in P. — Existing: `Complexity.HALT_not_computable` (relative to an `EffectiveMachineCode`), `Complexity.P_ssubset_EXP`, `Complexity.SAT_NPComplete`. Cite only.

**Def-23.4 (PPT).** *[Superseded by DESIGN D3–D6 (gate 03a, note 23): the frozen form is in `DESIGN.md` §1–§2 and the Lean files.]* A randomized algorithm is a TM with an extra random tape of uniform independent bits. **Formal (D3):** a structure with a `FinTM Bool` `M`, coin-length constants `(Cr, cr)` and time constants `(Ct, ct)` such that for every `x : List Bool` and every `r : Fin (Cr·(|x|+1)^cr) → Bool`, `M` halts on `pairEncode x (ofFn r)` within `Ct·(|x|+1)^ct` steps; `M.run x r` is its completed output; `M(x)` is the sampler `r ↦ M.run x r` (a `(Fin ℓ → Bool) → List Bool`, directly usable by `uprob`). Deviation: coins are an input component (reading a random tape sequentially is a bounded-cost simulation), and the coin length is an explicit polynomial. — Existing pattern: `FinTM.DecidesWithAdviceInTime` (pair input, time in `|x|`). New file `TCSlib/Complexity/Randomized/PPT.lean`. Difficulty 3 (definition + run/sampler API + basic lemmas `run_eq_of_computesInTime`, determinism via `ComputesInTime.output_unique`).

**Def-23.5 (Running time, randomized).** `A` runs in time `T` if for all `x` and *every* random tape, `A(x)` halts within `T(|x|)` steps (worst case over coins). — Folded into Def-23.4's time clause (the clause quantifies over all `r`). Expected polynomial time is not formalized (plan D8).

**Def-24.6 (PPT computes f).** `A` computes `f` if for all `x`, `A(x) = f(x)` with probability 1 over the random tape. **Formal:** `∀ x r, M.run x r = f x`. Lemma (C7): on a finite uniform coin space `uprob (fun r => M.run x r = f x) = 1 ↔ ∀ r, M.run x r = f x`, so the formal clause is the text's. Difficulty 2. Consequence: `PPT.Computes f → PolyTimeComputable (fun x => f x)`-style bridge is *not* automatic (the machine reads coins); provide `PolyTimeComputable_of_PPTComputes` by hard-wiring the all-zero coin string (`computesFunInTime_pairEncodeFixed`-style prepend of coins is on the wrong side — needs a `pairMapSnd`/`append` closure: `x ↦ pairEncode x 0^{ℓ(|x|)}` is `PolyTimeComputable.pairEncode` of `id` and `polyUnary`-then-zeros). Difficulty 2.

**Rem-24.2 (majority amplification).** If a polynomial-time randomized `A` computes `f` with probability `≥ 1/2 + 1/p(n)` on every input, then running `A` `ℓ(n)` times and taking the most frequent output computes `f` with probability `≥ 1 − 2^{−n}` (Chernoff). — Deferred: needs Thm-188.7/Lem-189.8 and Repetition; nothing in Chapters 2–4 core depends on it (Garg's concrete majority arguments use Chebyshev for pairwise independence). Difficulty 4.

**Def-24.7 (Efficient private-key encryption).** `(Gen, Enc, Dec)` are PPTs; `Gen(1^n)` outputs a key `k`; `Enc_k(m)` for `m ∈ {0,1}^n` outputs `c`; `Dec_k(c)` outputs `m ∈ {0,1}^n ∪ {⊥}`; for all `n` and `m ∈ {0,1}^n`, `Pr[k ← Gen(1^n) : Dec_k(Enc_k(m)) = m] = 1` (over the coins of `Gen` and `Enc`). **Formal:** messages `Fin n → Bool`; keys/ciphertexts `List Bool`; `Enc`/`Dec` receive `pairEncode 1^n (pairEncode k m)` (so their polynomial bounds are in `n`; the text says "polynomial in the size of their inputs" — with `|k| ≤ poly(n)` the two readings agree); `Dec` output decoded as an `n`-bit string or `⊥`. Correctness quantifies over all coin strings (Def-24.6 reading). Asymptotic/Encryption.lean (plan). Difficulty 2. Depends on Def-23.4.

**Def-26.8 (nuPPT).** *[Superseded by DESIGN D3–D6 (gate 03a, note 23): the frozen form is in `DESIGN.md` §1–§2 and the Lean files.]* A sequence `{A_i}` of probabilistic machines with `|A_i| < d(i)` and running time `< d(i)` for a polynomial `d`; `A(x)` runs `A_{|x|}(x)`. Equivalently (text): a uniform PPT with a polynomial-length advice string per input length. **Formal (D4):** a PPT `M` plus `α : ℕ → List Bool` with `|α n| ≤ Ca·(n+1)^ca`, run on `pairEncode (pairEncode x (α |x|)) r`, time `Ct·(|x|+1)^ct` for every `r`. Deviation: the machine-sequence formulation is not formalized. — Existing pattern: `FinTM.DecidesWithAdviceInTime`, `Complexity.PAdvicePoly`. New file `TCSlib/Complexity/Randomized/NonUniform.lean`. Difficulty 3. Note the standing convention "any adversarial algorithm is implicitly nuPPT" (p. 26) governs Defs 26.1, 27.3, 28.4, 41.1(4), 56.1(5) and Assumptions 30.1, 52.2, 53.1.

**Rem-26.2 (equivalence of nuPPT formulations).** Deferred (difficulty 4): `⇒` would use `Turing.timed_universal` with the description `A_{|x|}` as advice; `⇐` hard-wires the advice. Not needed downstream under D4.

**Claim-26.3 (closure calculus; implicit throughout).** The class of nuPPT samplers is closed under: (a) post-composition with `PolyTimeComputable` maps (decoding, projections); (b) pre-composition/pairing with `PolyTimeComputable` maps of the input and of computed strings; (c) using fresh coin segments as uniform strings of polynomial length and as uniform elements of `Fin 2^k`; (d) hard-wiring advice; (e) `T(n)` fresh-coin calls of a nuPPT with "first success" (loop) or concatenated outputs; (f) Boolean tests (equality of strings, `f(z) = y`). — Existing building blocks: `Turing.FinTM.computesFunInTime_comp` (budget `c·(T₁ n + T₂ (T₁ n) + 1)`, needs `Monotone T₂`), `computesFunInTime_cond`, `exists_loopFindTM`/`exists_emitLoopTM` (loop with fuel `R |x|` and per-round body contract), `exists_installCallTM`/`exists_emitCallTM` (callable module with clean seams), `PolyTimeComputable.comp/.pairEncode/.append`, `polyTimeComputable_ite/and/lenEq`, `pairFstD/pairSndD`. The plan's `Closure.lean`/`Repetition.lean` are this item; difficulty 5 for (e) (the plan's named risk), 3 for (a)–(d),(f). Every theorem below depends on it.

### §2.2 One-way functions

**Def-26.1 (Worst-case OWF).** `f : {0,1}* → {0,1}*` is worst-case one-way if (1) some PPT computes `f` on all inputs (equivalently `PolyTimeComputable f`, by Def-24.6 and C7), and (2) there is no nuPPT `A` with `∀ x, Pr_r[f(A(f x; r)) = f x] = 1`. **Formal (D5/Q2):** for a family `f n : (Fin (ℓ n) → Bool) → List Bool`: `¬ ∃ A : NUPPT, ∀ n x, ∀ r, decode_n (A.run (pairEncode 1^n (f n x)) r) is some x' with f n x' = f n x`. Note the text gives `A` only `f(x)`; D5 adds `1^n`. Difficulty 2. Nothing downstream uses it except Rem-27.1.

**Rem-27.1.** "Assuming NP ⊄ BPP, worst-case one-way functions exist; in fact the two are equivalent (show this!)." Deferred (difficulty 5): requires Def-192.12 (BPP) and, with nuPPT adversaries (§2.1.3), the correct class is non-uniform (`NP ⊄ BPP/poly`); the text mixes uniform BPP with non-uniform inverters. Recorded as a text issue; nothing downstream.

**Def-27.2 (Negligible).** `ε` is negligible if `∀ c ∃ n₀ ∀ n > n₀, ε(n) ≤ 1/n^c`; non-negligible if `∃ c` with `ε(n_i) > 1/n_i^c` for infinitely many `n_i`. — Existing: `TCSlib.Cryptography.Negligible` (`∀ c ∃ n₀ ∀ n ≥ n₀, |μ n| < 1/n^c`; equivalent on `[0,1]`-valued functions by shifting `c`), `not_negligible_iff` (`≥` form), `negligible_two_pow_neg` (the example `2^{−n}`), `Negligible.add/mul/mul_pow/const_mul`. Optional one-line bridges `negligible_iff_le`, `not_negligible_iff_lt` if a statement needs the text's inequalities verbatim. The example `n^{−log log n}` is optional.

**Def-27.3 (Strong OWF).** (1) easy: as Def-26.1(1); (2) for every nuPPT `A` there is a negligible `ε` with, for all `n`, `Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y] ≤ ε(n)`. **Formal:** `StrongOWF f ℓ := PolyTimeComputable-easy ∧ ∀ A : NUPPT, Negligible (fun n => invProb (f n) (A.inverter n))` where `A.inverter n : List Bool → coins → (Fin (ℓ n) → Bool)` decodes `A`'s output as an `ℓ n`-bit string (wrong length ↦ a fixed default that only lowers the probability — D5 Deviation). — Existing: `invProb` (exactly the per-`n` experiment, with `1^n` "implicit in the fixed types"). Difficulty 3 (definition + the two decoding lemmas + the lemma that the coin space of the experiment is the nuPPT's coin type). Asymptotic/OneWay.lean.

**Rem-28.1 ((t,s,ε)-one-wayness).** The concrete layer's `invProb f A ≤ ε` at one `n` for an adversary of a given size/time *is* this notion; no new declaration. Cite.

**Def-28.4 (Weak OWF).** (1) easy; (2) there is a polynomial `q` such that for every nuPPT `A` and all sufficiently large `n`, `Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y] ≤ 1 − 1/q(n)`. **Formal:** `∃ C c, 0 < C ∧ ∀ A, ∃ n₀, ∀ n ≥ n₀, invProb (f n) (A.inverter n) ≤ 1 − 1/(C·(n+1)^c)`. Difficulty 2.

### §2.3 Multiplication, primes, factoring

**Def-29.1 (f_mult).** `f_mult(x, y) = 1` if `x = 1 ∨ y = 1`, else `x·y`, on pairs of `n`-bit numbers (input length `2n`, output in binary). **Formal:** `fmult n : (Fin n → Bool) × (Fin n → Bool) → ℕ` (then `Nat.bits`), or on `Fin (2^n) × Fin (2^n)`. Deviation: the text's `ℕ² → ℕ` "picked uniformly from ℕ²" means `n`-bit numbers. Candidates/Factoring.lean. Difficulty 1. The "easy to compute" clause needs binary multiplication (Q1 hypothesis).

**Rem-29.2 (f_mult not strongly one-way).** The adversary `A(z) = (2, z/2)` for even `z` (else `(0,0)`) inverts with probability `≥ 3/4`. **Text issue:** `z/2` has up to `2n − 1` bits, so `(2, z/2)` is a preimage of a *different input length*; with inputs fixed to `n` bits (D5) this attack is invalid, and no typed attack is given. Deferred (difficulty 2 for the untyped reading, which is outside the campaign's model). Nothing depends on it.

**Def-29.3 (Π_n).** `Π_n = {q | q < 2^n ∧ q prime}`; the uniform distribution on it. **Formal:** `Primes n := {p : Fin (2^n) // (p : ℕ).Prime}` (a `Fintype`), `uprob` over it; cardinality `= Nat.primeCounting' (2^n) = #(Nat.primesBelow (2^n))` (`Nat.primesBelow_card_eq_primeCounting'`). Chebyshev.lean. Difficulty 1. Note `Π_n` contains `2` and small primes, and the text's later "`n`-bit primes" is loose; use `Π_n` consistently (Deviation noted at Thm-51.1).

**Asm-30.1 (Factoring).** For every nuPPT `A` there is a negligible `ε` with `Pr[p ← Π_n; q ← Π_n; N ← pq : A(N) ∈ {p, q}] < ε(n)` for all `n`. **Formal:** `FactoringAssumption := ∀ A : NUPPT, Negligible (fun n => uprob (fun (z : Primes n × Primes n × coins) => decodeℕ (A.run (pairEncode 1^n (bits (p·q))) r) ∈ {p, q}))`. Deviations: `A` receives `1^n` (the text passes only `N`, whose length is `≤ 2n`); `<` vs `≤` immaterial; `p = q` and `p = 2` are allowed by the text (probability `≤ 2n/2^n` by Claim-33.1). Difficulty 2.

**Thm-31.3 (Chebyshev).** For real `x > 1`, `π(x) > x/(2 log₂ x)`. Proof: `X = C(2x, x) = ∏_{p < 2x} p^{ν_p(X)} ≥ 2^x` and `p^{ν_p(X)} ≤ 2x`, so `2^x ≤ (2x)^{π(2x)}`, i.e. `π(2x) ≥ x/log₂(2x) = (1/2)·2x/log₂(2x)`; odd arguments via `π(2x) = π(2x−1)` (`2x` composite for `x ≥ 2`) and monotonicity of `t/log t`. — Existing Mathlib: `Nat.four_pow_lt_mul_centralBinom` (`4^n < n·centralBinom n`, `n ≥ 4`), `Nat.four_pow_le_two_mul_self_mul_centralBinom`, `Nat.prod_pow_factorization_centralBinom`, `Nat.pow_factorization_choose_le` (`p^{ν_p(C(n,k))} ≤ n`), `Nat.primesBelow_card_eq_primeCounting'`, `Nat.primeCounting`. No lower bound on `π` exists in Mathlib. **Formal statement recommendation:** prove the integer core `2^x ≤ (2x)^{π(2x)}` for `x ≥ 1` (hence `x ≤ π(2x)·⌈log₂(2x)⌉`), derive Claim-33.1 from it, and state the real-logarithm form of the theorem as a corollary (`Real.logb`). Difficulty 4 (3 for the integer core). Text issues: `log` means `log₂`; "each term is greater than 2" — the term `(x+x)/x` equals 2 (`X ≥ 2^x`, strict for `x ≥ 2`); the odd-case step uses `t/log t` increasing for `t ≥ 3`.

**Claim-32.4.** `log(2x)/log p > ν_p(X)`, i.e. `p^{ν_p(X)} < 2x`. **Text issue:** strictness fails (`x = 1, p = 2`); the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is `Nat.pow_factorization_choose_le` (with `Nat.factorization_choose_le_log`). Cite.

**Claim-33.1 (prime density).** For `n ≥ 1`, `|Π_n| ≥ 2^n/(2n)`, i.e. a uniform `x < 2^n` is prime with probability `≥ 1/(2n)`; consequently a uniform pair is a prime pair with probability `≥ 1/(4n²)` (independence: `uprob_prod`/`uprob_pi_forall`). From Thm-31.3's integer core at `x = 2^{n−1}`: `2^{n−1} ≤ π(2^n)·n`. Chebyshev.lean. Difficulty 3. **Text issue:** §2.6.6 (p. 50) claims the probability "exceeds `(2^n/n)/2^n = 1/n`", inconsistent with the `1/(2n)` of §2.3.2 and with Thm 31.3.

**Rem-33.2 (primality testing in P).** The text uses "primality testing can be done in polynomial time" (AKS, [aks04]) in Alg-33.6/37.4 and SamplePrime. **Formal:** hypothesis `PrimalityFP : PolyTimeComputable (fun w => [decide (Nat.ofBits w).Prime])` in the Q1 bundle (`Nat.decidablePrime` gives the mathematical test; its machine is not available). Deferred (difficulty 5 to discharge). Thms 33.5/36.3 are formalized without it.

**Thm-33.5.** Factoring assumption ⟹ `f_mult` is weakly one-way: with `q(2n) := 8n²`, for every nuPPT `A` and all large `n`, `Pr[x, y ← {0,1}^n : f_mult(A(1^{2n}, xy)) = xy] ≤ 1 − 1/(8n²)`. **Reduction (one-call variant `A″`):** `A″(1^n, N) := fst(A(1^{2n}, N))`. **Concrete lemma (C1):** if `S` is the success event of `A` on uniform `(x, y)` and `E` = "both prime" with `Pr[E] ≥ δ := 1/(4n²)`, then `Pr[S | E] ≥ 1 − (1 − Pr[S])/δ`; with `1 − Pr[S] ≤ 1/(8n²)` this gives `Pr[S | E] ≥ 1/2` (the text's `1/(8n²)` is weaker than what the argument yields). The conditional distribution of `(x, y)` given `E` is uniform on `Π_n × Π_n` (the factoring distribution), and on `E` a successful answer is a factor (Claim-34.1). Asymptotic: `A″` is `A` with a `PolyTimeComputable` projection (Claim-26.3(a)); `≥ 1/2` infinitely often contradicts negligibility (`not_negligible_iff`). "Easy to compute" needs Q1 (`mul`). — Existing: `uprob_and_le_mul`, `uprob_mono`, `uprob_fst`, `uprob_prod`, `uprob_pi_forall`, `not_negligible_iff`. Difficulty 3. Text issues: Alg 33.6 line 7 writes `A(1^n, z′)` (should be `1^{2n}`); the formal theorem uses `A″`, as the text itself suggests.

**Alg-33.6 (A′ / A″).** `A′(z)`: sample `x, y ← {0,1}^n`; if both prime set `z′ := z` else `z′ := xy`; `w ← A(1^{2n}, z′)`; return `w` if both prime. `A″`: always `z′ := z`, always output `w` (no primality test). Formalize `A″` only (plan). Difficulty 1.

**Claim-34.1 (unique factorization step).** If `p, q` are primes and `x′, y′ < 2^n` with `f_mult(x′, y′) = pq`, then `x′ ∈ {p, q}` (and `y′` is the other). Proof: `pq ≠ 1` so `x′, y′ ≠ 1` and `x′y′ = pq`; `x′ ≠ 0`; `Nat.Prime.dvd_mul`, `Nat.Prime.eq_one_or_self_of_dvd`. Factoring.lean. Difficulty 2.

### §2.4 Hardness amplification

**Thm-35.1 (weak → strong).** For any weak OWF `f` (with polynomial `q`) there is a polynomial `m` (the proof takes `m(n) = 2n·q(n)`) such that `f′(x₁, …, x_{m(n)}) = (f(x₁), …, f(x_{m(n)}))` on `({0,1}^n)^{m(n)}` is strongly one-way (security parameter `n`, input length `n·m(n)`). — **Existing (concrete, complete):** `OneWay.prodFun f q` (= `f′`), `yaoTry` (= Alg 38.5's `A₀`), `yaoInverter f B T` (= the `T`-fold repetition `A`), `yaoBad` (= complement of `G_n`), `invProb_prodFun_le` (Claim-39.2), `one_sub_invProb_yaoInverter_le` (Claim-39.1), `yao_amplification` (parametric in `a, θ, T`: `(1−a)^q + qθ < μ ⟹ 1 − a − (1−θ)^T ≤ invProb f (yaoInverter f B T)`). **Bridge:** (i) Claim-38.2 instantiates PS10's parameters; (ii) `yaoInverter f (A′ n) T` is a nuPPT: `T = 2n m² p(n)` fresh-coin calls of `A′` (Claim-26.3(e)), `m − 1` evaluations of `f` per call by `f`'s machine (loop with emitted chunks, `exists_emitLoopTM`), uniform `i : Fin m` from coins (Q7: take `m` a power of two), the test `f(z_i) = y` (equality machine), decoding of `A′`'s output tuple; (iii) from "`f′` not strong" obtain `c` and infinitely many `n` with `μ_n ≥ 1/n^c` (`not_negligible_iff`), conclude `invProb f (…) > 1 − 1/q(n)` infinitely often, contradicting Def-28.4; (iv) lengths: `A′` receives `1^{n·m(n)}`; the tuple `(Fin m → Fin n → Bool)` is encoded as the `nm`-bit concatenation (`Fin.appendEquiv`-style equivalence, cf. `owpBitsEquiv` in `Pseudorandom/GeneratorFromPermutation.lean`). Difficulty 4. Asymptotic/OneWay.lean. Text issues (proof): "For each `j ∈ [1, n]`" should be `[1, m]`; the displayed chain with the factor `m` is garbled — the concrete `invProb_prodFun_le` is the correct computation.

**Thm-35.2 (simple security reduction).** If `f` is a strong OWF then `g(x, y) = (f(x), f(y))` (input length `2n`) is a strong OWF. **Concrete lemma (C2, new):** `invProb (pairFun f) A′ ≤ invProb f (pairInverter f A′)` with `pairInverter f A′ u (y, r) := (A′ (u, f y) r).1` — proof exactly as `OneWay.invProb_pad_le` (`uprob_comp_equiv (Equiv.prodAssoc)`, `uprob_mono`); the text's test "`f(a) = u`" is unnecessary for the inequality. Asymptotic: the inverter samples `y`, evaluates `f`, calls `A′`, projects (Claim-26.3(a)–(c)); `1/p(2n)` infinitely often ⟹ non-negligible. Difficulty 3 (1 concrete + 2 bridge). Note `g = prodFun f 2` up to the equivalence `Fin 2 → α ≃ α × α`, so Thm-35.1's machinery also applies but is overkill.

**Thm-36.3 (f_mult amplified).** Factoring assumption and `m_n = 4n³` ⟹ `f′((x₁,y₁), …, (x_m, y_m)) = (f_mult(x₁,y₁), …)` on `({0,1}^{2n})^{m_n}` is strongly one-way. **Reduction (random-planting, one-call; the text's exercise):** `A″(1^n, N)`: sample `i ← [m]` and fresh pairs `(x_j, y_j)` for `j ≠ i`; put `z_i := N`, `z_j := x_j y_j`; call `A(1^{n′}, z⃗)`; output the first component of its `i`-th answer. **Concrete lemma (C3, new; mirror of `invProb_prodFun_le`'s proof with bad set = "pair not both prime"):** `Pr[A″ factors] ≥ (invProb (prodFun fmult m) A − (1 − δ)^m)/m` where `δ = Pr[pair both prime] ≥ 1/(4n²)`: by `uprob_update` planting at position `i` equals the uniform experiment conditioned on pair `i` prime; `sum_uprob_eq_card_mul` makes `i` uniform; `uprob_pi_forall` bounds `Pr[no pair prime] = (1 − δ)^m`; Claim-34.1 turns an inverse into a factor. Then Claim-36.2 and `μ ≥ 1/p(n′)` infinitely often give success `≥ 1/(2 m p(n′))` infinitely often. Deviation: no primality test, planting at a uniform position (instead of "the first prime pair"). Difficulty 3. Depends on Claim-36.2, Claim-34.1, Claim-33.1, Claim-26.3, Q1. Text issues: Alg 37.4 "Output `x′_i`" should output a factor and check it; `n′ = 2n·m(n) = 8n⁴`.

**Claim-36.2.** `(1 − 1/(4n²))^{4n³} = ((1 − 1/(4n²))^{4n²})^n ≤ e^{−n}` (and `e^{−n} ≤ 2^{−n}`, negligible by `negligible_two_pow_neg`). Pattern: `yao_amplification_exp` (`Real.one_sub_le_exp_neg`, `Real.exp_nat_mul`). Concrete.lean. Difficulty 1.

**Alg-37.4.** The random-planting `A′` (above). Difficulty 1.

**Alg-38.5 (A₀ and A).** `A₀(f, y)`: pick `i ← [m]`, fresh `x_j`, `y_j = f(x_j)` for `j ≠ i`, `y_i = y`, call `A′`, output `z_i` if `f(z_i) = y` else `⊥`; `A` runs `A₀` `2nm²p(n)` times and returns the first non-`⊥` answer. — Existing: `OneWay.yaoTry` (coins `(i, xs, r)`), `OneWay.yaoInverter f B T` (first success via `List.foldr`), `yaoInverter_spec`. Cite.

**Claim-38.2 (parameter instantiation).** With `m := 2n q(n)` (or the next power of two, Q7), `p(n) := p′(n·m)`, `a := 1/(2q(n))`, `θ := 1/(2m²p(n))`, `T := 2nm²p(n)`: for all large `n`, `(1 − a)^m + mθ ≤ e^{−n} + 1/(2mp(n)) < 1/p(n)` and `1 − a − (1 − θ)^T ≥ 1 − 1/(2q(n)) − e^{−n} > 1 − 1/q(n)`; hence `yao_amplification` (with `[NeZero m]`, `[Inhabited (Fin n → Bool)]`) yields `invProb f (yaoInverter …) > 1 − 1/q(n)`. Pure real arithmetic; Asymptotic/OneWay.lean. Difficulty 2.

**Claim-39.1.** `Pr[A fails | x ∈ G_n] ≤ (1 − 1/(2m²p(n)))^{2m²np(n)} ≈ e^{−n}`. — Existing: the `(1 − θ)^T` term of `OneWay.one_sub_invProb_yaoInverter_le`. Cite.

**Claim-39.2 (many good elements).** `|G_n| ≥ 2^n(1 − 1/(2q(n)))`, else `A′` would invert `f′` with probability `< 1/(2p(n)) + e^{−n} < 1/p(n)`. — Existing: `OneWay.invProb_prodFun_le` (`μ ≤ (1 − Pr[S])^q + qθ Pr[S]`), used contrapositively inside `yao_amplification`. Cite.

### §2.5 Collections

**Def-41.1 (Collection of OWFs).** `F = {f_i : D_i → R_i}_{i ∈ I}` with: (1) a PPT `Gen` with `Gen(1^n) ∈ I`; (2) a PPT that on input `i` returns a uniformly random element of `D_i`; (3) a PPT computing `f_i(x)` from `(i, x)`; (4) for every nuPPT `A` there is a negligible `ε` with `Pr[i ← Gen(1^n); x ← D_i; y ← f_i(x) : f_i(A(1^n, i, y)) = y] ≤ ε(n)`. **Formal design (Collections.lean):** a structure `OWCollection` with index strings `i : List Bool`, for each `i` a `Fintype` domain `D i` with an injective encoding `encD i : D i → List Bool` and a total decoder (wrong strings ↦ failure), `f i : D i → List Bool`; `Gen : PPT` (sampler of indices, coin length polynomial in `n`); `Sample : PPT` on input `i` with `PushesUniform (fun r => decode (Sample.run i r))` onto `D i` *or* (Q3) within statistical distance `2^{−n}` of uniform; `Eval : PolyTimeComputable (fun z => f (pairFstD z) (decode (pairSndD z)))`; hardness via a new per-`n` experiment `collInvProb F A n := uprob (fun (r₁, x, ρ) => let i := Gen.run 1^n r₁; f i (decode (A.run (pairEncode 1^n (pairEncode i (f i x))) ρ)) = f i x)` where `x` is uniform in `D i` (a dependent product: use `Σ`-type or the sampler's coins with `PushesUniform`). — Existing: `HardcoreBit.PushesUniform` and `.uprob_eq`, `invProb` (pattern). Difficulty 4 (design-heavy; the dependent-domain probability space is the subtle point — simplest is to define the experiment over `(r₁, r₂, ρ)` with `x := Sample i r₂` and require exact `PushesUniform`, matching the text's "uniformly random element"). Text issues: (4) says "p.p.t. `A`" against the standing nuPPT convention; "`f(A(1^n, i, y)) = y`" should read `f_i`; `R_i` is never constrained; "uniformly random element of `D_i`" presupposes `D_i` finite.

**Thm-42.2 (collection ⟺ strong OWF).** (⇐) a strong OWF `f` gives the collection with `Gen(1^n) = 1^n` (index = unary parameter), `D_{1^n} = {0,1}^n`, `f_{1^n} = f n`: difficulty 2 (the text's "`I = {0}`, `D_0 = ℕ`" is sloppy: the domain must depend on `n`; Deviation). (⇒, "left as an exercise") given a collection, `g_n(r₁, r₂) := (i, f_i(x))` with `i = Gen(1^n; r₁)`, `x = Sample(i; r₂)` is a strong OWF with input length `ℓ₁(n) + ℓ₂(n)` (Q2). Proof: `g` is `PolyTimeComputable` from `Gen`, `Sample`, `Eval` (`PolyTimeComputable.comp/.pairEncode`); an inverter `A_g` of `g` gives the collection inverter `A_F(1^n, i, y) := Sample(i; (A_g(1^{ℓ(n)}, pairEncode i y)).2)`: if `g(r₁′, r₂′) = (i, y)` then `Gen(r₁′) = i` and `f_i(Sample(i; r₂′)) = y`; the law of `(i, x)` under uniform `(r₁, r₂)` equals the law in Def-41.1(4) by `PushesUniform.uprob_eq` applied conditionally on `i` (`uprob_prod`). Difficulty 4. Depends on Def-41.1, Def-27.3, Claim-26.3.

### §2.6 Computational number theory

**Fact-42.1.** `(a mod N + b mod N) mod N = (a + b) mod N`, `((a mod N)(b mod N)) mod N = ab mod N`. — `Nat.add_mod`, `Nat.mul_mod`. Cite.

**Alg-43.2 (ExtendedEuclid).** `ExtendedEuclid(a, b)` for `a > b > 0`: if `a mod b = 0` return `(0, 1)`; else `(x, y) ← ExtendedEuclid(b, a mod b)`, return `(y, x − y⌊a/b⌋)`. **Formal:** `extEuclid : ℕ → ℕ → ℤ × ℤ` by well-founded recursion on `b`, plus `extEuclidCalls : ℕ → ℕ → ℕ` (recursive-call count). — Existing: Mathlib `Nat.xgcd`/`Nat.gcdA`/`Nat.gcdB`/`Nat.gcd_eq_gcd_ab` (Bézout, the standard extended Euclid), `ZMod.inv` (computable inverse through `Nat.gcdA`; used by `ZMod.mul_inv_eq_gcd`). The text's variant and its call count are new. Euclid.lean. Difficulty 2.

**Claim-43.3.** If `a > b ≥ 0` and `a < 2^n` then `ExtendedEuclid(a, b)` makes at most `2n` recursive calls. Induction on `n`: if `b < 2^n` the next call is in the hypothesis; if `b ≥ 2^n` then `a mod b < 2^{n+1} − b ≤ 2^n`, so two calls later the hypothesis applies. Difficulty 3. Text issues: case 2 writes `b > 2^n` (should be `≥`); the precondition `b ≥ 0` allows `b = 0`, where the recursion as written swaps arguments once more.

**Claim-44.4.** `gcd(a, b) = gcd(b, a mod b)`. — Lean core `Nat.gcd_rec` with `Nat.gcd_comm`. Cite.

**Claim-44.5 (correctness).** `ExtendedEuclid(a, b) = (x, y) ⟹ ax + by = gcd(a, b)` (strong induction on `b`; the text's regrouping). Difficulty 2. (Mathlib's `Nat.gcd_eq_gcd_ab` is the same statement for `Nat.xgcd`.)

**Rem-43.6.** "Polynomial time in `log a + log b`" at the machine level — deferred (Q1); mathematically Claim-43.3 is the step bound.

**Alg-45.5 (ModularExponentiation).** `r := 1; while x > 0: if x odd then r := r·a mod N; x := ⌊x/2⌋; a := a² mod N; return r`. **Formal:** `modExp a x N` by binary recursion on `x` (`Nat.binaryRec` or strong recursion), with `modExp_eq : N > 0 → modExp a x N = a^x % N` (`Nat.pow_mod`, `Nat.pow_succ`, `Nat.mul_mod`). ModExp.lean. Difficulty 2. No `powMod` exists in this Mathlib revision.

**Thm-45.6.** On `(a, x, N)` with `a ∈ [1, N]`, Alg 45.5 computes `a^x mod N` in time `O(log x · log² N)`. **Formal (optional):** the loop executes at most `⌊log₂ x⌋ + 1` iterations, each with at most two modular multiplications of numbers `< N` (so `≤ 2(⌊log₂ x⌋+1)` multiplications); optionally a `TimeM ℕ` version (`TCSlib/Cryptography/RSA.lean` cost monad) charging `log² N` per multiplication. Machine-level bound deferred (Q1). Difficulty 2. Text issues: the restriction `a ∈ [1, N]` is immaterial; the later remark that Euler's theorem "removes the restriction that `x < N`" refers to a restriction Alg 45.5 does not have.

**Def-46.7 (Group).** Mathlib `Group`/`CommGroup`. Cite. **Ex-46.1** `(Z_N, +)` = `ZMod N` as `AddCommGroup`. Cite.

**Thm-46.8.** `(Z_N^*, ×)` with `Z_N^* = {x ∈ [1, N−1] | gcd(x, N) = 1}` is a group (closure via Def-46.9/Claim-47.1; inverses via Euclid). — Existing: `(ZMod N)ˣ`, `ZMod.unitsEquivCoprime : (ZMod n)ˣ ≃ {x : ZMod n // Nat.Coprime x.val n}`, `ZMod.unitOfCoprime`, `ZMod.inv_coe_unit`, `ZMod.mul_inv_eq_gcd`. Optional one-line bridge to the text's set (`x.val ∈ [1, N−1]` for `N ≥ 2`). Units.lean. Difficulty 1.

**Def-46.9 (Prime).** `Nat.Prime`. Cite. **Claim-47.1** `p ∣ ab ⟹ p ∣ a ∨ p ∣ b`: `Nat.Prime.dvd_mul`. Cite.

**Claim-47.2 (totient values).** `Φ(p) = p − 1` for prime `p`; `Φ(pq) = (p−1)(q−1)` for distinct primes ("show this by counting"); `|Z_N^*| = Φ(N)`. — `Nat.totient_prime`, `Nat.totient_mul` + `Nat.coprime_primes`, `ZMod.card_units_eq_totient`. Units.lean (one lemma `totient_mul_prime_prime`). Difficulty 1. Text issue: the formula needs `p ≠ q` (`Φ(p²) = p(p−1)`).

**Thm-47.10 (Euler).** `∀ a ∈ Z_N^*, a^{Φ(N)} = 1 mod N`. — `ZMod.pow_totient` (units), `Nat.ModEq.pow_totient`. Cite. **Cor-48.11 (Fermat).** `ZMod.pow_card_sub_one_eq_one`. Cite.

**Cor-48.12.** For `a ∈ Z_N^*`, `a^x ≡ a^{x mod Φ(N)} (mod N)`: write `x = Φ(N)·(x / Φ(N)) + x mod Φ(N)` (`Nat.div_add_mod`) and apply Euler. Units.lean. Difficulty 1 (used by RSA decryption exponent arithmetic). **Rem-48.2** (efficiency "for any `x` given `Φ(N)`") is machine-level: deferred (Q1). **Ex-48.3** (paper-and-pencil example, garbled in the pdftotext): optional `decide`.

**Def-49.1 (L_N, corrected).** For odd `N > 2` write `N − 1 = u·2^j` with `u` odd; `L_N := {α ∈ Z_N | α^{N−1} = 1 ∧ ∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} ∈ {1, −1}}` ("no non-trivial square root of 1 among the intermediate powers"). Primality.lean. Difficulty 2. **Text error:** the text writes "`N = u2^j`" and a condition using `i = j` only, which is vacuous (`α^{u2^{j+1}} = (α^{N−1})² = 1` always and then requires `α^{N−1} = 1`, already assumed).

**Alg-49.13 (Miller–Rabin).** Handle `N = 2` (and even `N`); repeat `t` times: `α ← Z_N`, if `α ∉ L_N` output "composite"; output "prime". **Formal:** a sampler `millerRabin N t : (Fin t → Fin N) → Bool`. Difficulty 2. The membership test "`α ∈ L_N` by repeated squaring with internal checks" is Alg-45.5 instrumented (math: trivial; machine: Q1).

**Thm-49.14.** If `N` is prime the test outputs "prime" (probability 1); if `N` is (odd) composite it outputs "composite" with probability at least `1 − 2^{−t}`. Prime case from Lem-50.15a (core, difficulty 2); composite case from Lem-50.15b via `uprob_pi_forall` (`Pr[all t samples in L_N] = (|L_N|/N)^t ≤ 2^{−t}`) — deferred with the lemma. Text issue: "with probability `1 − 2^{−t}`" should be "at least".

**Lem-50.15a.** `N` odd prime ⟹ `L_N = Z_N^*` (`|L_N| = N − 1`): Fermat gives `α^{N−1} = 1` for `α ≠ 0`; in the field `ZMod N`, `β² = 1 → β = ±1` (`mul_self_eq_one_iff`/`sq_eq_sq_iff_eq_or_eq_neg`). Difficulty 3 (the index bookkeeping). **Lem-50.15b.** `N > 2` odd composite ⟹ `|L_N| ≤ (N−1)/2` (text: `<`): the liars lie in a proper subgroup of `Z_N^*` (with the "largest index" construction for Carmichael numbers) and Lagrange (`Subgroup.card_subgroup_dvd_card`). Deferred (plan), difficulty 5. Text issue: "`N > 2` composite" should say odd composite (even `N` is handled by the base case).

**Rem-49.3 / Rem-50.2.** Infinitely many Carmichael numbers; AKS. Out of scope / deferred. (Mathlib has `Nat.exists_infinite_pseudoprimes` for Fermat pseudoprimes to a fixed base — weaker.)

**Alg-50.16 (SamplePrime).** Repeat `x ← {0,1}^n` until `x` is prime. **Formal (strict PPT, truncated):** `T(n) := 2n²` independent uniform `x_t < 2^n`; output the first prime, else `⊥`. Primality.lean. Difficulty 3. Deviation: expected running time is not formalized; the primality test is `Nat.Prime` (exact) at the concrete layer and `PrimalityFP` (Q6) at the machine layer; with Miller–Rabin instead the output is only statistically close to uniform.

**Lem-51.17.** SamplePrime outputs a uniformly random element of `Π_n` in time `poly(n)`. **Formal:** (i) `Pr[⊥] ≤ (1 − 1/(2n))^{2n²} ≤ e^{−n}` (Claim-33.1, `uprob_pi_forall`, exp bound C8); (ii) conditioned on success the output is uniform on `Π_n` (C4: for i.i.d. uniform draws the first draw landing in `E` is uniform on `E`); (iii) the sampler is a PPT given `PrimalityFP` (loop `exists_loopFindTM` with fuel `2n²`). Difficulty 3 (+4 for (iii)). Text issue: "exceeds `1/n`" (should be `1/(2n)`).

**Thm-51.1 (factoring collection).** `I = ℕ`, `D_i = {(p, q) prime, |p| = |q| = i/2}`, `f_i(p, q) = pq`; factoring assumption ⟹ collection of OWFs. **Formal:** `Gen(1^n) = 1^n` (index `2n`), `D_n = Primes n × Primes n`, `Sample` = two SamplePrime calls (Q3: within `2e^{−n}` of uniform), `Eval` = multiplication (Q1), hardness: an inverter returning `(p′, q′)` with `p′q′ = N` gives a factor (Claim-34.1), so `A_fact(1^n, N) := fst(A(1^n, 1^n, N))`. Factoring.lean. Difficulty 3. Text issue: `D_i` uses exactly-`i/2`-bit primes while Asm-30.1 uses `Π_n`; the formalization uses `Π_n` throughout (Deviation).

### §2.8 Discrete logarithm

**Def-52.1 (Generator).** `g ∈ G` is a generator if `{g, g², …} = G`; `Gen_G` is the set of generators. — `Subgroup.zpowers g = ⊤`, `IsCyclic.exists_generator`, `orderOf_eq_card_of_forall_mem_zpowers`. Cite.

**Rem-52.2.** In a group of prime order every non-identity element is a generator; `Z_p^*` has order `p − 1` (not prime); for a safe prime `p = 2q + 1` the subgroup of squares has prime order `q`; sampling safe primes has no known guarantee. — `isCyclic_of_prime_card`, `ZMod.card_units`, `orderOf_dvd_card`; the squares subgroup is `MonoidHom.range (powMonoidHom 2)` of index 2 (Lem-57.1). Optional, difficulty 2. Units.lean.

**Asm-52.2 (DL).** "If `G_q` is a group of prime order `q`, then for every nuPPT `A` there is a negligible `ε` with `Pr[q ← Π_n; g ← Gen_{G_q}; x ← Z_q : A(g^x) = x] < ε(n)`." **Formal design:** a structure `DLGroupFamily` with, for each index `(q, desc)`, a finite group `G` of order `q` with injective string encoding of elements, `PolyTimeComputable` multiplication (hence exponentiation by repeated squaring, Alg-45.5 at the group level), and a PPT index sampler `GenDL(1^n)` returning `(q, g)` with `q ∈ Π_n` prime and `g ≠ 1` (a generator since `|G| = q` prime); the assumption: `∀ A, Negligible (fun n => Pr[(q,g) ← GenDL(1^n); x ← Z_q : A(1^n, q, g, g^x) = x])`. Deviations: `A` receives `q, g` (the text passes `g^x` only); the ideal "`q ← Π_n; g ← Gen_{G_q}`" is replaced by the family's own sampler (the text itself notes that sampling `(q, g)` efficiently is not known in general — Bach/Kalai); exact uniformity of `x ← Z_q` via Q3. Difficulty 3. DiscreteLog.lean. Text issues: `G_q` unspecified; `A(g^x)` lacks `q, g`.

**Thm-52.3 (DL collection).** `I = {(q, g) | q ∈ Π_k, g ∈ Gen_{G_q}}`, `D_i = Z_q`, `R_i = G_q`, `f_{q,g}(x) = g^x`; DL assumption ⟹ collection of OWFs. **Formal:** `Gen = GenDL`, `Sample` = uniform `Z_q` (Q3), `Eval` = exponentiation; hardness: the DL experiment *is* the collection's inversion experiment since `g^{x′} = g^x ⟺ x′ = x` in `Z_q` (`pow_eq_pow_iff_modEq`, `orderOf g = q`). Difficulty 3. Text issues: `R_i = G_p` and `f_{p,g}` typos (`q`); mixes `k` and `n`.

**Claim-53.1 (safe-prime generator test).** For `p = 2q + 1` with `p, q` prime, `g ∈ Z_p^*` is a generator iff `g ≠ ±1` and `g^q ≠ 1`: the order of `g` divides `2q`, so it is `1, 2, q` or `2q`. — `orderOf_dvd_of_pow_eq_one`, `orderOf_dvd_card`, `ZMod.card_units`. Optional, difficulty 2.

**Claim-53.2 (DL functions are permutations).** If `g` generates a group `G` of order `q` then `x ↦ g^x : ZMod q → G` is a bijection. — `zmodCyclicMulEquiv`, `orderOf_eq_card_of_forall_mem_zpowers`, `pow_eq_pow_iff_modEq`. Optional (the "DL is a collection of one-way permutations" remark after Thm 52.3), difficulty 2.

### §2.9 RSA

**Asm-53.1 (RSA).** For every nuPPT `A` there is a negligible `ε` with `Pr[p, q ← Π_n; N ← pq; e ← Z*_{Φ(N)}; y ← Z_N^*; x ← A(N, e, y) : x^e ≡ y (mod N)] < ε(n)`. **Formal:** `Φ(N) := (p−1)(q−1)` (valid for `p ≠ q`; the text's distribution allows `p = q`, where `Φ(p²) ≠ (p−1)²` — restrict to `p ≠ q` or define `Φ` as `Nat.totient N`), `e` uniform in `(ZMod (Φ N))ˣ`, `y` uniform in `(ZMod N)ˣ`, `A` receives `pairEncode 1^n (bits N, bits e, bits y)`, output decoded as a number `x` with `x^e % N = y`. RSA.lean. Difficulty 3.

**Thm-53.2 (RSA collection).** `I = {(N, e) | N = pq, p, q ∈ Π_n, e ∈ Z*_{Φ(N)}}`, `D_i = R_i = Z_N^*`, `f_{N,e}(x) = x^e mod N`; RSA assumption ⟹ collection of OWFs. **Formal:** `Gen`: two SamplePrime calls, `N`, `Φ`, then `e` by rejection sampling over `[0, Φ)` with `gcd(e, Φ) = 1` (needs C9 `φ(Φ)/Φ ≥ 1/(log₂ Φ + 1)` for a polynomial truncation, Q3); `Sample`: rejection sampling of `Z_N^*` (density `≥ 1/4` for `N = pq`); `Eval` = modexp (Q1). Hardness: by Thm-54.3 `x ↦ x^e` is a bijection of `Z_N^*`, so `(e, x^e)` with `x` uniform has the law of `(e, y)` with `y` uniform (`HardcoreBit.pushesUniform_equiv`, `PushesUniform.uprob_eq`); an inverter of `f_{N,e}` is an RSA breaker with the same probability. Difficulty 3. Text issue: the proof's "`{x, e ← Z_N^* : (e, x^e mod N)}`" samples `e` from the wrong group (should be `Z*_{Φ(N)}`).

**Thm-54.3 (RSA is a permutation).** For `e ∈ Z*_{Φ(N)}`, `x ↦ x^e mod N` is a permutation of `Z_N^*` with inverse `y ↦ y^d`, `ed ≡ 1 (mod Φ(N))`: `x^{ed} = x^{cΦ(N)+1} = x` by Euler. — Existing: `ZMod.pow_totient` (units; direct), and the legacy `RSA.rsa_crt_pow`/`RSA.rsa_correctness` (all of `ZMod (p*q)` for `p ≠ q` and `e·d = 1 + k(p−1)(q−1)`, via CRT). Units.lean (or RSA.lean). Difficulty 2.

### §2.10–§2.11 Permutations and trapdoors

**Def-55.1 (Collection of OWPs).** A collection of OWFs with every `f_i` a permutation (`D_i = R_i`, `f_i` bijective). Collections.lean. Difficulty 1.

**Thm-55.2 (RSA ⟹ Factoring).** If some nuPPT `A` factors `N = pq` (random `n`-bit primes) with probability `≥ 1/p(n)` (infinitely often), then `A′` (Alg-55.3) inverts `f_{N,e}` with probability `≥ 1/p(n)` (infinitely often); hence the RSA assumption implies the factoring assumption. **Formal:** `FactoringAssumption` is implied by `RSAAssumption`, proved contrapositively: `A′(1^n, N, e, y)`: `p′ ← A(1^n, N)`, `q′ := N / p′`; if `p′q′ ≠ N` abort; `Φ := (p′−1)(q′−1)`; `d := e^{−1} mod Φ` (`ZMod.inv`, computable by `Nat.gcdA`); output `y^d`. Whenever `A` returns a factor, `A′` succeeds (Thm-54.3), and the law of `N` is the factoring law regardless of `(e, y)` (`uprob_fst`-style marginalization), so `Pr[A′ wins] ≥ Pr[A factors]`. Difficulty 3. Machine-level: Q1 (`divMod`, `xgcd`, `modExp`). Text issue: the factoring assumption's `A` outputs one factor while Alg 55.3 expects the pair (compute the other by division); "running time of `A′` is `A` plus `O(log³ n)`" is a cost-model remark.

**Alg-55.3.** The adversary above. Difficulty 1.

**Def-56.1 (Trapdoor permutations).** `F = {f_i : D_i → R_i}` with (1) each `f_i` a permutation; (2) PPT `Gen(1^n) = (i, t)`; (3) PPT uniform sampler of `D_i`; (4) PPT evaluator; (5) for every nuPPT `A` there is negligible `ε` with `Pr[(i, t) ← Gen(1^n); x ← D_i; y ← f_i(x); z ← A(1^n, i, y) : f_i(z) = y] ≤ ε(n)`; (6) PPT `Inv((i, t), y) = f_i^{−1}(y)` for `y ∈ R_i`. Collections.lean. Difficulty 2. Text issue: "`≤ e(k)`" should be `e(n)`.

**Thm-57.2 (RSA is a TDP collection; "the proof is an exercise").** With `Gen(1^n) = ((N, e), d)`, `ed ≡ 1 (mod Φ(N))`, `f^{−1}_{N,d}(y) = y^d mod N`: under the RSA assumption, RSA is a collection of trapdoor permutations. Proof: (1) Thm-54.3; (2)–(4) as Thm-53.2 plus `d` from Alg-43.2; (5) Thm-53.2; (6) `(x^e)^d = x` (Thm-54.3). RSA.lean. Difficulty 3.

### §2.12 Rabin

**Def-57.0 (QR_p).** `QR_p := {x² mod p | x ∈ Z_p^*}`, as the subgroup `MonoidHom.range (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ)`. QuadraticResidues.lean. Difficulty 1.

**Lem-57.1.** For an odd prime `p`, `QR_p` is a subgroup of `Z_p^*` of order `(p−1)/2`; every `a ∈ QR_p` has exactly two square roots `±x` with `x ≠ −x`. Proof: the squaring homomorphism has kernel `{±1}` (`Units.sq_eq_sq_iff_eq_or_eq_neg`, `mul_self_eq_one_iff`), of order 2 since `p` is odd, so the image has order `(p−1)/2` (`Subgroup.card_eq_card_quotient_mul_card_subgroup`, `QuotientGroup.quotientKerEquivRange`); alternatively `legendreSym.card_sqrts` (`#{x | x² = a} = legendreSym p a + 1`) with `ZMod.euler_criterion`. Difficulty 3. **Claim-58.1** (`x² = y² → x = ±y` in `Z_p`): `sq_eq_sq_iff_eq_or_eq_neg`. Cite.

**Thm-58.2.** If `p = 4k + 3` is prime and `y ∈ QR_p`, then `(±y^{k+1})² = y`: with `y = a²`, `(y^{k+1})² = a^{4k+4} = a^{p+1} = a²` by Fermat (`ZMod.pow_card_sub_one_eq_one`, `a ≠ 0`). Difficulty 2.

**Ex-58.3 (exercise).** Square roots modulo `p ≡ 1 (mod 4)` (Tonelli–Shanks/Cipolla). Deferred (difficulty 4): not needed for the Blum-integer Rabin results; needed only for Thm-61.8 (⇐) in the text's generality.

**Thm-58.3 (CRT).** For pairwise coprime `p₁, …, p_k`, `N = ∏ p_i`, the map `y ↦ (y mod p_i)_i : Z_N → ∏ Z_{p_i}` is a bijection. — `ZMod.chineseRemainder` (`k = 2`, ring equivalence; all uses in the chapter have `k = 2`), `Nat.chineseRemainder`, `Nat.chineseRemainderOfList`/`…OfFinset` (general `k`, existence and uniqueness). Cite; an optional `k`-fold ring-equiv bridge by induction (difficulty 2). **Claim-59.1** (explicit inverse `y = Σ_i b_i n_i a_i`, `b_i n_i ≡ 1 (mod p_i)`, two Euclid calls): optional, difficulty 2 (math); machine-level deferred. **Ex-59.2** (`p = 7`, `q = 11`): optional `decide`.

**Def-59.3 (QR_N).** `QR_N := {x² mod N | x ∈ Z_N^*}`. Difficulty 1.

**Thm-59.4.** For `N = pq` (distinct primes) and `x ∈ Z_N^*`, `x ∈ QR_N ⟺ (x mod p ∈ QR_p ∧ x mod q ∈ QR_q)`. Proof: transport squares and units along `ZMod.chineseRemainder` (`Units.map`, `RingEquiv.map_pow`). Difficulty 2. Text issues: "`zinQRq`" typo; the two directions of the proof are labelled backwards.

**Thm-60.5.** For `N = pq` with `p ≠ q` odd primes, squaring on `Z_N^*` is 4-to-1: every `y ∈ QR_N` has exactly four square roots in `Z_N^*`. Proof: roots of `y` correspond under CRT to pairs (root mod `p`, root mod `q`), `2 × 2` by Lem-57.1. Difficulty 3. Text omits `p ≠ q` and oddness (fails for `N = p²` or `p = 2`).

**Cor-60.6.** `|QR_N| = |Z_N^*|/4 = Φ(N)/4`. Fiber counting (`Finset.card_eq_sum_card_fiberwise`). Difficulty 2.

**Claim-60.7 (roots from the factors).** If `a² ≡ y (mod p)` and `b² ≡ y (mod q)` then `s := CRT^{−1}(a, b)` satisfies `s² ≡ y (mod N)`; hence with `p, q` known, square roots modulo `N` reduce to square roots modulo `p` and `q`. Difficulty 2 (math; used by Thm-61.8 (⇐) and Thm-63.10(6)); machine-level deferred (Q1). **Ex-60.8** (`N = 77` example): optional `decide`; the pdftotext numbers are garbled (`71` vs `42`, `(1,5)`, `(0,3)`).

**Thm-61.7 (Rabin collection).** `I = {N = pq | p, q ∈ Π_n}`, `D_N = Z_N^*`, `R_N = QR_N`, `f_N(x) = x² mod N`; factoring ⟹ collection of OWFs. **Formal (Q4):** indices restricted to `p ≠ q` odd (or Blum), with the factoring assumption on the same index distribution; `Gen` as in Thm-51.1 with a `p ≠ q` re-sample; `Sample` = rejection sampling of `Z_N^*`; `Eval` = squaring mod `N` (Q1); hardness = Thm-61.8 (⇒). Rabin.lean. Difficulty 4. Text issue: "`Z_n^*`" for `Z_N^*`.

**Thm-61.8 (Rabin one-way ⟺ factoring).** (⇒ direction of the text, i.e. factoring hard ⟹ Rabin one-way, proved contrapositively) if a nuPPT `A` returns a square root of `y = x²` (`x ← Z_N^*`) with probability `≥ 1/p(n)` infinitely often, then `A′` (Alg-62.9) factors `N` with probability `≥ 1/(2p(n))` infinitely often. Concrete content: Claim-62.2 (the root differs from `±x` half the time) + Claim-62.1 (`gcd(x − z, N)` is then a prime factor). Asymptotic: `A′` samples `x`, squares, calls `A`, tests, takes a gcd (Q1). Difficulty 4. (⇐, "only if": Rabin one-way ⟹ factoring hard, contrapositively) if a nuPPT `A` factors with probability `≥ 1/r(n)` i.o., then `A′(N, y)`: factor, take roots mod `p` and mod `q` (Thm-58.2 — **only for `p ≡ q ≡ 3 (mod 4)`**), combine by Claim-60.7; success `≥ 1/r(n)` i.o. Difficulty 3 for Blum integers; the general case needs Ex-58.3 (text gap). Text issues: mixes `n` and `k`; the "1/2p(k)" bound; the heuristic "A outputs one of the four roots with equal probability" is replaced by the symmetry argument of Claim-62.2.

**Alg-62.9.** `A′(N)`: `x ← Z_N^*`; `y := x² mod N`; `z ← A(1^n, N, y)`; if `z² ≢ y` abort; else output `gcd(x − z, N)`. Difficulty 1.

**Claim-62.1.** For `N = pq` (distinct primes) and `x, z ∈ Z_N^*` with `x² ≡ z² (mod N)` and `z ≢ ±x (mod N)`, `gcd(x − z, N) ∈ {p, q}` (`x − z` taken in `ℤ`, or `(x − z) mod N` in `ℕ`): `N ∣ (x−z)(x+z)` but `N ∤ (x−z)`, `N ∤ (x+z)`, so exactly one of `p, q` divides `x − z` (`Nat.Prime.dvd_mul`, CRT). QuadraticResidues.lean. Difficulty 2.

**Claim-62.2 (symmetry lemma, concrete).** Let `Z : QR_N → ρ → Z_N^*` depend on `x` only through `y = x²` (and coins). Then `Pr_{x, r}[Z(x², r)² = x² ∧ Z(x², r) ∉ {x, −x}] ≥ (1/2)·Pr_{x, r}[Z(x², r)² = x²]`. Proof: let `u := CRT^{−1}(1, −1)` and `σ(x) := ux`; `σ` is a bijection of `Z_N^*` with `σ(x)² = x²` and `σ(x) ∉ {±x}` (for `p, q` odd distinct); the events `S ∧ B` and `S ∧ B∘σ` (`B(x) := Z(x², r) ∈ {±x}`) are disjoint subsets of `S` with equal probability (`uprob_comp_equiv`), so `2·Pr[S ∧ B] ≤ Pr[S]`. New concrete lemma in `Candidates/Concrete.lean`. Difficulty 3. Used by Thm-61.7/61.8 and (with `Z` = the QR root) by Thm-63.10.

**Thm-63.10 (Rabin TDP).** `I = {N = pq | p, q ∈ Π_n, p ≡ q ≡ 3 (mod 4)}`, `D_N = R_N = QR_N`, `Gen(1^n) = (N, (p, q))`, `f_N(x) = x² mod N`, `f^{−1}_{p,q}(y)` = the unique root of `y` in `QR_N`; factoring (on Blum integers) ⟹ collection of TDPs. Components: (1) Claim-63.1; (2) `Gen` samples Blum primes — density of primes `≡ 3 (mod 4)` below `2^n` is **not available** (no Dirichlet-type bound in Mathlib): take `BlumPrimeDensity : |{p ∈ Π_n | p ≡ 3 (mod 4)}| ≥ 2^n/(C(n+1)^c)` as an explicit hypothesis of the `Gen` clause (Q4); (3) `Sample`: square a uniform `r ∈ Z_N^*` — 4-to-1 maps push uniform to uniform (C5); (4) squaring (Q1); (5) hardness: Claim-62.2 with `Z := A`'s answer (the QR root): with `r` uniform in `Z_N^*`, `r ∉ {±x}` half the time, and `gcd(r − x, N)` factors `N` (Claim-62.1); (6) `Inv`: roots mod `p`, `q` by Thm-58.2, select the residues by Euler's criterion (`ZMod.euler_criterion`, exponent `(p−1)/2`), combine by Claim-60.7. Rabin.lean. Difficulty 4. Deviation: factoring assumption restricted to Blum moduli; density hypothesis.

**Claim-63.1 ("future homeworks").** For a Blum integer `N = pq` (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`), every `y ∈ QR_N` has exactly one square root in `QR_N`; hence squaring is a permutation of `QR_N`. Proof: `−1 ∉ QR_p` for `p ≡ 3 (mod 4)` (`ZMod.exists_sq_eq_neg_one_iff`), so of the roots `±a` mod `p` exactly one is a residue; likewise mod `q`; Thm-59.4 selects exactly one of the four roots. QuadraticResidues.lean. Difficulty 3.

### §2.13 Universal one-way function

**Thm-63.1 (universal OWF).** If some (strong) one-way function exists, then the polynomial-time computable `f_universal` of Alg-64.2 is one-way. The proof shows weak one-wayness (with `q(n) = n³`) and invokes Thm-35.1. **Formal (corrected, F2):** `f_univ c (y) := let k := ⌊log₂ |y|⌋; M := y.take k; x := y.drop k; pairEncode M (U(pairEncode (pairEncode (bits ((|y|+1)³)) M) x))` where `U` is the machine of `Turing.timed_universal_concrete c` (output `true :: M(x)` on halting within the budget, `[false]` otherwise), for a fixed `c : EffectiveMachineCode` (exists: `Turing.exists_effectiveMachineCode`) satisfying `∃ A B, ∀ k, c.canonizerTime k ≤ A·2^{B·k}` (so that the simulator's code-dependent coefficient `3|M| + canonizerTime |M| + |serialize| + 2|bits numStates| + 2q₀ + 16 + universalBlockBound + 14`, with `|serialize| ≤ canonizerTime |M|` by output-length ≤ time and `numStates ≤ |serialize|`, is `poly(n)` for `|M| = ⌊log₂ n⌋`). Statement: `(∃ g, StrongOWF g) → WeakOWF (f_univ c)` with `q(n) = n³`, and `StrongOWF (prodFun-amplification of f_univ c)` by Thm-35.1. Proof: Lem-64.3 gives a strong `g′` and a `CodeTM` `M_g` computing it within `c₀·(m+1)²` (≤ `(n+1)³` for large `n`); Claim-65.1: with probability `≥ 1/n` the code field of a uniform `y` is `encode M_g` padded with `true`s (`decode_encode_pad`); on that event `f_univ(y) = pairEncode M (true :: g′(x))` with `x` uniform of length `m = n − ⌊log₂ n⌋`, and an inverse `⟨M′, x′⟩` must have `M′ = M` (the code is part of the output; `pairEncode_injective`) and `g′(x′) = g′(x)`; Claim-65.2 turns "`A` inverts with probability `> 1 − 1/n³` infinitely often" into "the inverter `B(1^m, z) := x′` from `A(1^n, pairEncode M_g (true :: z))` inverts `g′` with probability `≥ 1/n²` at `m(n) = n − ⌊log₂ n⌋` infinitely often" — non-negligible in `m` (`m ↦ n` is recovered by advice or search), contradicting strong one-wayness. — Existing: `Turing.timed_universal`, `timed_universal_concrete`, `universalBlockBound`, `EffectiveMachineCode`, `exists_effectiveMachineCode`, `MachineCode.decode_encode_pad`, `exists_codeTM`, `FinTM.one_work_tape_binary`, `pairEncode_injective`, `OneWay.card_log_bits_le`, `uprob_eq_one_div_card`, `not_negligible_iff`. Universal.lean. Difficulty 5. Text issues: output must include `M` (F2); "hardness amplification construction from §2.3" should be §2.4; `|y|³` budget becomes `(|y|+1)³`.

**Alg-64.2 (f_universal).** Interpret `y` as `⟨M, x⟩` with `|M| = log|y|`; run `M` on `x` for `|y|³` steps; output `M(x)` if it halts, else `⊥`. **Formal:** as above (corrected). Poly-time computability: `y ↦ (y.take ⌊log₂|y|⌋, y.drop ⌊log₂|y|⌋)` needs a new primitive "split at `⌊log₂ |y|⌋`" (`computesFunInTime_lengthBits` gives `bits |y|`, whose length is `⌊log₂|y|⌋ + 1`; difficulty 3), `computesFunInTime_polyBits 1 3` gives `bits ((|y|+1)³)`, `PolyTimeComputable.pairEncode` assembles `U`'s input, `computesFunInTime_comp` runs `U` (its bound is quadratic in the budget times the code-dependent coefficient), and `PolyTimeComputable.pairEncode` prepends `M`. Difficulty 4.

**Lem-64.3.** If `g` is a strong OWF then there is a strong OWF `g′` computable in time `O(n²)`: `g′(⟨a, b⟩) = ⟨a, g(b)⟩` with `|a| = n^c − n`, `|b| = n`. **Formal:** `g′ n (a, b) := (a, g k(n) b)` with `|b| = k(n)` and `|a| = n − k(n)` where `k` is chosen so that the coded machine for `g` runs within the quadratic budget on `b` (if `M_g` runs in `C(k+1)^c` multi-tape, `one_work_tape_binary` gives a one-tape binary machine in `c′(C(k+1)^c+1)²`, so take `n := ` that bound plus `k`, i.e. `k(n) ≈ n^{1/(2c)}`), and a `CodeTM` (`exists_codeTM`) computing `g′` within `c₀(n+1)²`: copy `a` (linear), parse the split (lengths known from `n`), run `M_g` on `b`. Hardness: `OneWay.invProb_pad_le` (`pad`, `padInverter`) + nuPPT closure (sample `a`, call `A`, project). Difficulty 3 (+3 for the machine time analysis). Universal.lean. Note the text's `⟨a, b⟩` pairing is immaterial when the split lengths are fixed by `n`; plain concatenation avoids `pairEncode`'s doubling.

**Claim-65.1 (PickG).** For `n` with `⌊log₂ n⌋ ≥ |encode M_g|`, `Pr_{y ← {0,1}^n}[y.take ⌊log₂ n⌋ = encode M_g ++ 1^{⌊log₂ n⌋ − |encode M_g|}] = 2^{−⌊log₂ n⌋} ≥ 1/n` (`uprob_fst`, `uprob_eq_one_div_card`, `card_log_bits_le`), and on this event `decode (y.take …) = M_g` (`decode_encode_pad`). Difficulty 2.

**Claim-65.2 (union bound).** If `Pr[Invert] > 1 − 1/n³` and `Pr[PickG] ≥ 1/n` then `Pr[¬Invert ∨ ¬PickG] ≤ 1/n³ + 1 − 1/n`, so for `n ≥ 2` `Pr[Invert ∧ PickG] ≥ 1/n − 1/n³ ≥ 1/n³` (text) — and in fact `Pr[Invert | PickG] ≥ 1 − 1/n²`; the `g′`-inverter's success at length `m(n)` is at least this, infinitely often, so not negligible (`not_negligible_iff`; the map `n ↦ n − ⌊log₂ n⌋` is unbounded and non-decreasing with steps `≤ 1`, so infinitely many `n` give infinitely many `m`). Difficulty 2.

### Appendix items Chapter 2 relies on

**App-A.1 (union bound).** `uprob_or_le`, `uprob_exists_le`. Cite. **App-A.2 (Markov, Chebyshev).** `HardcoreBit.uprob_mul_le_uexp` (Markov form), `HardcoreBit.uprob_le_abs_le`. Cite. **App-A.3 (pairwise-independent sampling).** `HardcoreBit.chebyshev_pairwise`, `chebyshev_pairwise_ident` (bits; the appendix states it for `|X_i| ≤ 1`). Cite.

**Thm-188.7 (Chernoff).** For independent `X_1, …, X_n` with `E X_i = μ` and `|X_i| ≤ 1`, `Pr[|Σ X_i − μn| ≥ εn] ≤ 2^{−ε²n}` (the text writes `≥ ε`, dimensionally wrong; constants "chosen for simplicity"). Deferred (difficulty 4): Mathlib's Hoeffding `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` is measure-theoretic (sub-Gaussian MGFs) and would need a `uprob`-bridge; only Rem-24.2/Lem-189.8 use it.

**Lem-189.8 (Majority vote).** `Pr[X_i = b] ≥ 1/2 + 1/p(n)`, `ℓ > p(n)²` ⟹ `Pr[majority = b] > 1 − 2^{??}` (garbled; proof unfinished "…"). Deferred (difficulty 4 via Chernoff; Chebyshev alone gives only `1 − O(1/n)` error with `ℓ = n p(n)²`).

**Thm-189.9 (Cauchy–Schwarz).** `Finset.sum_mul_sq_le_sq_mul_sq`. Cite.

**Def-191.10 (DP).** `Complexity.P`. Cite. **Def-191.11 (NP).** Witness relation `R_L ∈ P`, `|y| ≤ p(|x|)` — `Complexity.NP` (exact length `C(|x|+1)^c`, concatenation) with `Complexity.mem_NP_iff_exists_length_le` (bounded-length paired form). Cite. **Def-192.12 (BPP).** `L ∈ BPP` iff some PPT `M` has `Pr[M(x) = 1] ≥ 2/3` for `x ∈ L` and `Pr[M(x) = 0] ≥ 2/3` for `x ∉ L`. Deferred (difficulty 2 once Def-23.4 exists); only Rem-27.1 uses it.

---

## 3. Text errors and issues (consolidated)

Outright errors (also returned as `text_errors`):

1. **Algorithm 64.2 / Theorem 63.1:** `f_universal(⟨M, x⟩) = M(x)` omits the machine description from the output; the proof ("`A` must invert a hard instance of `g`") is invalid because the inverse may be `⟨M′, x′⟩` with `M′ ≠ M_g`. Correct definition: output `⟨M, M(x)⟩`.
2. **§2.6.5, definition of `L_N`:** "`N = u2^j`" should be `N − 1 = u·2^j`; the second condition is stated with `i = j` only and is vacuous; intended: for all `i < j`, `α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. **Claim 32.4** is false as a strict inequality (`x = 1`, `p = 2`); correct: `p^{ν_p(C(2x,x))} ≤ 2x`.
4. **§2.6.6 (p. 50):** "the probability that a uniformly sampled `n`-bit integer is prime exceeds `1/n`" — Theorem 31.3 (and §2.3.2's own corollary) gives `1/(2n)`.
5. **Theorem 60.5, Corollary 60.6, Theorems 61.7, 61.8, 63.10:** require `p ≠ q` odd primes; `Π_n` contains 2 and the sampling allows `p = q`. Likewise `Φ(pq) = (p−1)(q−1)` (p. 47) and `Φ(N)` in Assumption 53.1 need `p ≠ q`.
6. **Theorem 61.8 (⇐):** needs square roots modulo arbitrary primes, but only `p ≡ 3 (mod 4)` is proved (Theorem 58.2; the rest is "left as an exercise").
7. **Theorem 59.4:** "`zinQRq`" typo; the proof's `⇒`/`⇐` labels are swapped.
8. **Theorem 52.3:** `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; **Assumption 52.2:** `A` receives only `g^x` (needs `q, g`); `G_q` is unspecified.
9. **Theorem 53.2 proof:** "`x, e ← Z_N^*`" samples `e` from the wrong group (`Z*_{Φ(N)}`).
10. **Definition 56.1(5):** "`≤ e(k)`" should be `e(n)`.
11. **Definition 41.1(4):** "p.p.t. `A`" contradicts the standing nuPPT convention; "`f(A(1^n, i, y)) = y`" should be `f_i`.
12. **Theorem 42.2 proof idea:** "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n` (`{0,1}^n`).
13. **§2.4.3 proof:** "For each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra factor `m` is garbled.
14. **Algorithm 33.6, line 7:** `A(1^n, z′)` should be `A(1^{2n}, z′)`; **Algorithm 37.4:** "Output `x′_i`" should output a verified factor.
15. **Lemma 189.8:** statement garbled ("`1 − 2??`"), proof unfinished; **Theorem 188.7:** threshold `ε` should be `εn`.
16. **§2.3 attack on `f_mult`:** `A(z) = (2, z/2)` returns a preimage of a different input length; with `n`-bit inputs it does not show `f_mult` is not strongly one-way.
17. **Claim 43.3 case 2:** "`b > 2^n`" should be `b ≥ 2^n`.
18. **Example p. 61 (`N = 77`):** numbers garbled (`71`/`42`, `(1,5)`, `(0,3)`).
19. **Theorem 63.1 proof:** "hardness amplification construction from §2.3" should be §2.4.
20. **Theorem 49.14:** "with probability `1 − 2^{−t}`" should be "at least"; **Lemma 50.15:** "`N > 2` composite" should be odd composite.
21. **p. 27:** "NP ⊄ BPP ⟺ worst-case one-way functions exist (show this!)" mixes the uniform class BPP with the non-uniform adversaries of §2.1.3.
22. **Theorem 45.6 / p. 46:** the remark that Euler's theorem "removes the restriction that `x < N`" refers to a restriction Algorithm 45.5 does not have.
23. **Theorem 31.3 proof:** "each term is greater than 2" — the term `(x+x)/x` equals 2 (`X ≥ 2^x`).
24. **Theorem 61.8 / 55.2:** mix `n` and `k`; **Theorem 61.7:** `Z_n^*` for `Z_N^*`; **Theorem 51.1:** `D_i` uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.

Non-error sloppiness handled by Deviations: adversaries receive `1^n` everywhere (Assumptions 30.1/52.2/53.1 omit it); dyadic samplers approximate the ideal uniform distributions (Q3); expected polynomial time (SamplePrime) replaced by strict PPT with `2^{−n}` failure; polynomial normal form `C(n+1)^c`.

---

## 4. New concrete-layer lemmas (Garg files are frozen; put these in `TCSlib/Cryptography/Candidates/Concrete.lean` unless noted)

* **C1** `uprob_cond_ge`: for `E, S : α → Prop` with `Pr[E] ≥ δ > 0`, the probability of `S` on the uniform subtype `{a // E a}` equals `Pr[S ∧ E]/Pr[E]` and is `≥ 1 − (1 − Pr[S])/δ` (Thm-33.5). Also the identification of `uprob` on `Primes n × Primes n` with the conditional law on `Fin (2^n) × Fin (2^n)`.
* **C2** `invProb_pairFun_le` (Thm-35.2) — in `Asymptotic/OneWay.lean`.
* **C3** `invProb_prodFun_plant_le`: random-position planting with a bad set (Thm-36.3); may be stated generally enough to re-derive `invProb_prodFun_le`.
* **C4** `first_hit_uniform`: for i.i.d. uniform draws `x_1, …, x_T`, the first `x_t ∈ E` is uniform on `E` conditioned on existence, and `Pr[no hit] = (1 − Pr[E])^T` (Lem-51.17; also the rejection samplers of Q3).
* **C5** `pushesUniform_of_card_fiber`: a map all of whose fibers have the same size pushes uniform to uniform (`QR_N` sampling, Thm-63.10(3)); converse-type lemma for 4-to-1 (Cor-60.6).
* **C6** Claim-62.2 (Rabin symmetry lemma; `Rabin.lean` · `rabin_symmetry`, gate 03f1, finding 2).
* **C7** `uprob_eq_one_iff_forall` (Def-24.6).
* **C8** `one_sub_inv_pow_le_exp_neg`: `(1 − 1/a)^{a·n} ≤ e^{−n}` for `a ≥ 1`, and `e^{−n} ≤ 2^{−n}` (Claim-36.2, Lem-51.17, Claim-38.2).
* **C9** `totient_div_self_ge`: `φ(m)/m ≥ 1/(log₂ m + 1)` for `m ≥ 1` (the `i`-th smallest prime factor is `≥ i + 1`, `∏_{k=2}^{K}(1 − 1/k) = 1/K`) — in `NumberTheory/Units.lean`; needed for sampling `Z*_{Φ(N)}` (Thm-53.2) by truncated rejection.
* **C10** statistical-switch lemma: replacing a sampler by one within statistical distance `δ` changes any success probability by `≤ δ` (Q3; `distAdv_le_statDist` is the model) — in `Asymptotic/Collections.lean`.

## 5. Machine-layer requirements consumed by Chapter 2 (for `Randomized/{Closure,Repetition}.lean`)

* R1 post-processing by `PolyTimeComputable` (decode `n`-bit strings, projections `pairFstD/pairSndD`, numeral decoding) — all theorems.
* R2 pre-processing: `x ↦ pairEncode 1^n (h x)` for `PolyTimeComputable h`; planting a given string into a computed tuple at a coin-chosen position (Thms 35.1, 36.3).
* R3 coin splitting: using disjoint segments of the coin string as independent uniform strings / `Fin 2^k` elements (every reduction).
* R4 advice pass-through (every reduction uses the given nuPPT's advice).
* R5 `T(n)` fresh-coin calls returning the first success (`exists_loopFindTM`): Thm-35.1, SamplePrime, rejection samplers.
* R6 `m(n)` evaluations of a `PolyTimeComputable` function with concatenated outputs (`exists_emitLoopTM`): `prodFun` evaluation in Thms 35.1/36.3/63.1 amplification.
* R7 calling the clocked universal machine with a hard-wired code (`computesFunInTime_pairEncodeFixed`, `computesFunInTime_comp`): Thm-63.1.
* R8 equality test of two computed strings and `ite` (`polyTimeComputable_ite`, `lenEq`): Thm-35.1's `f(z_i) = y`, Alg-62.9's `z² = y`.
* R9 (Q1 bundle) binary arithmetic: `mul`, `divMod`, `xgcd`, `modExp`, comparison, numeral/string decoding; (Q6) primality test. Taken as hypotheses in `Candidates/Arithmetic.lean`.

## 6. Proposed file split (changes to the plan's layout)

* Add `TCSlib/Cryptography/Candidates/Arithmetic.lean` (the Q1/Q6 hypothesis bundle, docstring explaining why it is a hypothesis) and `TCSlib/Cryptography/Candidates/Concrete.lean` (C1, C3–C6, C8). Both under the `Candidates.lean` facade.
* `Candidates/Factoring.lean` (Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Alg-37.4, Thm-51.1) is at risk of exceeding 600 lines: split `Candidates/FactoringAmplified.lean` for Thm-36.3 if needed.
* `NumberTheory/Chebyshev.lean` holds Def-29.3, Thm-31.3, Claim-33.1; `NumberTheory/Primality.lean` holds Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a/b (both proved; b for odd composites with `≤`, gate 03f2, F02), Alg-50.16, Lem-51.17.
* `Asymptotic/Universal.lean` holds Thm-63.1, Alg-64.2, Lem-64.3, Claims 65.1–65.2, plus the new log-split primitive if it is not placed in a `Complexity/Randomized` helper (it is a deterministic machine; placing it in `Complexity/TuringMachine/Build/` would touch frozen files — put it in `Asymptotic/Universal.lean` as a private construction or in a new `Complexity/Randomized/Primitives.lean`).
* Definitions 24.7 (Encryption.lean) and 192.12 (PPT.lean, deferred) sit outside the Chapter-2 files as the plan prescribes.

## 7. Build order (dependencies)

PPT.lean → NonUniform.lean → Closure.lean/Repetition.lean → Asymptotic/OneWay.lean (Defs 26.1, 27.3, 28.4; Thms 35.2, 35.1 with Claim-38.2) → Asymptotic/Collections.lean (Defs 41.1, 55.1, 56.1; Thm 42.2) → NumberTheory/{Chebyshev, Euclid, ModExp, Units, Primality, QuadraticResidues}.lean (independent of the machine layer except Lem-51.17(iii)) → Candidates/{Arithmetic, Concrete, Factoring, DiscreteLog, RSA, Rabin}.lean → Asymptotic/Universal.lean (needs OneWay.lean, Thm-35.1, and the universal machine).

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03f1-pack.md =====

# Gate 03f1 ([PS10] ch. 2–4, discrete log, its hard-core bit, ElGamal): external statement audit pack

**Status: ready to dispatch once [Shilun-Allan-Li/tcslib#201](https://github.com/Shilun-Allan-Li/tcslib/pull/201) merges** (re-staged 2026-11-05 at that PR's head, the gate 03a + 03c repairs; first staged at `a3c5fa8b`; the evidence is under `evidence/f1/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`0c348ff94cacf24d96d99078c9dd9e328530c8d2` (the head of #201; its Lean files are what the branch holds once #201 merges). This pack covers the discrete-log candidate (the assumption
and the collection), its hard-core bit, ElGamal, and the concrete samplers they use.
- **This pack gates fills.** Its files hold **21 `sorry`s**. By the user's ruling of 2026-11-05 they
  will be filled after this pack closes, discrete log first, because ch. 5–8 cites the DL candidate
  (Thm 142.3). A statement that cannot be proved as stated, or that is weaker than the source,
  must be found **now**, before anyone tries to fill it.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03f1-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs:
- §2.8 (book pp. 52–53);
- §3.4.1 (pp. 82–86);
- §3.11 (pp. 105–107);
- Claim 36.2 (p. 36);
- Claim 62.2 (p. 62).

## Changes since the first staging (repairs of the interface packs; check them, do not re-find them)

The pin moved from `a3c5fa8b` to the head of the gate 03a + 03c repair PR. Changes in or near this pack's files:
- **G3-1** (gate 03b major, merged in #198): `Collection` gained the field `encD_decD`, which makes decoding canonical. `expCollection` proves it by `expEnc_of_expDec` (`DiscreteLog.lean`). The numeral lemmas `natToList_length_listToNat` and `natToList_val_natCast` are in `Arithmetic.lean` (context). `encodeDistinctPrimes_of_decode` is in `Concrete.lean`.
- **Gate 03a #12:** `DiscreteLog.lean` imports `Randomized.{Closure, NonUniform, Repetition}` instead of the facade `TCSlib.Complexity.Randomized`. No statement changes.
- **Gate 03l, major 1:** the axiom attestation below prints every public theorem and lemma of this pack's files, not only `Checks.lean`'s headlines.

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also:
- For **every sorried declaration**, say whether it is (a) true as stated and provable from the
  hypotheses it carries, (b) true but stated more weakly than the source, or (c) false or
  unprovable as stated. For (c), give a counterexample or the missing hypothesis.
- The candidates are stated under an explicit hypothesis bundle for polynomial-time arithmetic
  (`Candidates/Arithmetic.lean`, decision D11; pack 03b audits the bundle itself). Say where a
  statement needs a field the bundle lacks.

Attempt at least **three adversarial instantiations**, for example:
- a group generator whose "generator" is the identity with non-negligible probability;
- a DDH instance whose exponents are not uniform;
- a hard-core-bit predictor that uses its advice to know the group.

Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Candidates/{DiscreteLog, DiscreteLogHardcore, ElGamal, Concrete}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | `Candidates/Arithmetic.lean` (pack 03b); the files of packs 03a–03d, which these statements use |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D11; §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Asm-52.2, Thm-52.3, Claim-53.2, Claim-36.2, Claim-62.2; `inventory-ch3.md`: Constr-82.b, Lem-84.1 (with .0, .1, .3, .4, .5), Alg-84.2, Alg-85.a, Asm-105.1, NT-105.a, Claim-106.a, Claim-106.b, Alg-106.2, Claim-107.a, Thm-107.3, Def-107.b |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` (P8-1, the DDH ensembles, was a run-3a blocker: check its repair) |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the factoring-based candidates (pack 03f2) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (evidence under `evidence/f1/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 89 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   39 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 150 prints of every public theorem and lemma in this pack's files:
   116 use only the standard axioms, and 34 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 21 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes at its head (`evidence-repairs/03ac/replay.log`); each line of
`replay.log` is the newest check of its module. The closure is smaller than at the first staging
because 03a's repair narrowed facade imports (`Randomized` → its three files).

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints of every public theorem and lemma of this pack's files;
- **admissions:** the 21 `sorry`s, listed by declaration:
  - `DiscreteLog`: 6;
  - `DiscreteLogHardcore`: 7;
  - `ElGamal`: 7;
  - `Concrete`: 1;
- lint;
- interface use. The declarations cited by ch. 5–8 are `Candidates.ExpGroupGen` and
  `Candidates.DLAssumption`.

## Specific questions

1. **The DL assumption and collection (Asm 52.2, Thm 52.3).**
   - Is `DLAssumption` the source's assumption: the group (a safe-prime subgroup), the generator
     and the exponent sampled as stated, and inversion negligible for every n.u.p.p.t. adversary?
   - Is the validity bridge of `expCollection` (the generator output `dlDefaultIndex` below `n₀`, a
     run-3a repair) benign?
2. **The samplers** (`expSampler_spec`, `statClose_sampleBelowL`, `Concrete.lean`'s rejection
   sampler). Are the claimed closeness bounds negligible at the stated parameters, and are the
   specifications what the collection needs?
3. **The hard-core bit of DL (§3.4.1, Lem 84.1).**
   - Is the "half" predicate, with its inverter reduction (Algs 84.2 and 85.a), stated with the
     right advantage loss?
   - Lemma 84.1's generator is restricted to `p ≡ 3 (mod 4)` (open question 3 of Frederick's
     plan). Is that restriction declared, and is it benign?
4. **ElGamal (Asm 105.1, Alg 106.2, Thm 107.3).**
   - Is DDH stated on the right group with uniform exponents, and is P8-1's repair right?
   - Is the message space `G_q` handled as the source requires?
   - Is the encryption correct (`elGamal_correct`) for every message?
   - Is the security statement `elGamal_secure` the source's CPA security?
5. **Claim 107.a** (squaring a uniform unit is uniform on `G_q`, a generator unless it is `1`). Is
   `statClose_sq_generator` the claim, at the right distance?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. Add the column **Sorry verdict** (a / b / c, see the
brief) for sorried declarations. The pack closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).
