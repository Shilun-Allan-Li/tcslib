<!-- Filed by the maintainer on 2026-11-17 from the auditor's chat reply, pasted by Seyoon. The text below is verbatim.
The evidence ZIP it mentions (gate44-pairing-fills-evidence.zip) was not uploaded; only this Markdown was received. -->

# Gate 44 pairing fills — round 1 findings

**Verdict: HOLD. Open findings: 0 blockers, 1 major, 1 minor, 1 note.**

The delivered proofs establish the frozen T1 and T4 statements. The hold concerns the required acceptance of disclosed duplication.

| Audited item | Pin |
|---|---|
| Exchange | `30ef1257a56873489b599007782046b7dedeb7fc` |
| Campaign records | `8f888790b7e40f9e0529967e29a05a72c5ee8ba3` |
| #340 / merge base | `916afc25c21f5e52b4b01958186ad55d2f615fd1` / `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| #346 / merge base | `89a18a8225be1b76166af12a15179da291747783` / `7291f6b237fec75add1549c0992c174442180488` |
| Joint tree T44 | `33681cb8ed893a897ca2028d5ada70ca29237978` |

## Findings

Lean paths below are under `TCSlib/Cryptography/`.

| ID | Severity | PR · location | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G44-01 | **Major** | #340, `Pairing/Assumptions.lean:199`; #346, `IdentityBased/BonehBoyenMachine/Words.lean:261` and neighboring reader proofs | Disclosed exact re-derivations are classified as “no duplicated proved material; nothing for the duplication ledger.” T1’s inline verdict identity is precisely public `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), specialized to the solver-success decision bit. The checkpoint’s `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` also re-prove the polynomial-time facts for identical public `InteractiveHandler` projection functions (`Games/Efficiency.lean:538`, `:542`, `:546`, `:550`). Both families are disclosed, but no explicit human acceptance and scheduled repayment is recorded in the audited material or pinned duplication ledger. Policy §1 requires that acceptance, including for mechanically forced copies. | Reuse shared facts, promoting missing generic readers where necessary; or record Seyoon’s explicit acceptance, the shared home and repayment point. Correct both reports’ “nothing for the ledger” dispositions. |
| G44-02 | **Minor** | #346, `BonehBoyenMachine/Draws.lean:58`, `:130`; References entries in `Words.lean:60` and `Handler.lean:62` | `[PS10, Theorem 52.3]` is an inaccurate locator for bounded rejection sampling. That theorem concerns the discrete-log collection of one-way functions; its proof merely remarks that the domain is easy to sample. It does not specify this sampler, fixed coin budget, fallback or statistical bound. The actual formal justification is `Candidates.statClose_sampleBelowL`. This is a genuine source with an inaccurate citation, rather than a fabricated-tag major. | Attribute the bounded sampler to the existing library construction and bound. Retain PS10 §2.8/Theorem 52.3 only as context, and correct the three References entries consistently. |
| G44-03 | **Note** | `pack-r1.md:339`, Assumptions paired-control figures | The prose doubles the totals. Each variant has **2 sealed and 2 unsealed probes**, with **25** expected negative errors: 12 in A and 13 in B. Across strict and coe together: 4 sealed, 4 unsealed and 50 negative errors. The raw logs and plans verify these actual counts, with every reader passing. | Correct “per variant” and “50 … in each.” No replay or control repair is needed. |

The PS10 source supports G44-02’s distinction between its discrete-log theorem and the bounded sampler. [cs.cornell.edu](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf?utm_source=chatgpt.com)

G44-01 is an acceptance/ledger requirement. The overlaps were disclosed; it is **not** an undisclosed-copy accusation.

## Proof and scope checks

| Question | Result |
|---|---|
| **1 — T1 correctness** | **Pass.** `exists_bdhDistinguisher` constructs a total polynomial-time raw function through `NUPPT.ofPolyTime`, retaining the solver’s coins and advice. On the real tuple law, `coinsCongr` and `expect_sample_equiv` preserve success probability and the unused target sample disappears. On the random law, exchanging independent target/coin samples and encoding injectivity give the inverse-order bound, including outputs outside the encoding range. `accept_bdhGame_le` is pointwise in the security parameter; the bad-order charge is exactly the stated hypothesis. The final negligibility argument adds no assumption. |
| **1 — T4 correctness** | **Pass.** The handler uses total polynomial-time string operations. Negation reduces before subtracting from the modulus; differences and inverses agree with `ZMod`, including inverse zero. Membership precedes message decoding. The per-call identity covers all three oracles and every simulator state. At most one tape entry is consumed per oracle call, so the budget suffices. The sampler is exactly G40-03’s; encoding injectivity supplies its strict modulus bound on every generated group. Machines and error function are chosen before the universally quantified bits and security parameter. |
| **1 — edge cases and sufficiency** | **Pass.** Parameter zero, zero budget, empty coins/advice, absent initialization/challenge, refused target-key queries, repetitions, invalid messages and identity collisions are covered. T4 requires no identity-injectivity/order-growth hypothesis: both simulations use the same zero-inverse convention. Orders zero and one and invalid mathematical group objects are excluded by `BilinearGroup`’s fields; malformed machine strings still receive total polynomial-time behavior. `bb1_sidSecure` is unchanged and reaches `sorryAx` exactly through T2 and T3. T1 is not used by that consumer. |
| **2 — frozen declarations** | **Pass.** Independently reconstructed T44 from the pinned trees; both PR diffs match the pack. T1/T4 headers and statement prose are unchanged. Restoring permitted regions restores the base files. All six T1 and ten T4 mutation controls reject their mutations. The checkpoint inserts only its four imports and Contents section. Public declarations: 101 → 275, exactly 174 additions, with no other frozen declaration changed or removed. |
| **3 — seven readers** | **Pass.** Independent reconstruction is byte-exact: `Defs` +43/−0, `BonehBoyen` +37/−0 at the approved positions. All nine controls reject their mutations. These are precisely the three `oracleImpl_*_onSpec` readers and four approved BB1 encoding/message-space readers, with approved proofs and no added attribute. The casts’ `rfl` witnesses read `Defs`’ own `sidSpec`; consumers use published theorems. |
| **4 — LE-bb1m** | **Pass.** Direct parent/head comparison confirms only deletion of unused `hpp` and reordering of the formula docstring. No statement changes. |
| **5 — duplication** | G44-01 and the grading tables below. No additional undisclosed duplicate was identified. The checkpoint overlaps were reviewed beyond the full-name clash check. |
| **6 — Rule 10** | **Pass.** Recounted **24/24** joint-owner and **16/16** supplement seals: source/probe hashes, conservative request sets reconstructed from collector catalogs, exact source recovery after removing harness insertions, install/EOF coverage, rc 0 and no errors. Strict/coe A/B exclusions match the rulings. Assumptions controls pass at the corrected counts; supplement controls give 24 expected negatives per variant, with all readers/unsealed controls passing. The three skipped owners have **12** row-, source- and probe-identical records against phase 2; its **32/32** earlier seals also recount cleanly. Those owners do not import changed Assumptions, so unchanged inputs justify reuse. The explicit scan has 1,016 items and zero foreign reads; source inspection agrees. |
| **7 — sources** | **Pass apart from G44-02.** BB04 §4.2/Theorem 4.1 and algorithm B are correct sources. The theorem is on printed p. 6 and its proof on pp. 7–8, so the locators are compatible. T1’s independent folklore attribution is accurate under Q10. PS10 Algorithm 43.2 and Definition 181.1 are apt for Euclid and statistical closeness. Inherited missing SOK00/BF01 entries remain outside these fills. |
| **8 — documentation** | **Pass apart from G44-02.** New public docstrings state their formulas; sketches describe the delivered proofs. The sole 15-line sketch omission is pre-existing frozen `bb1SimChal_fresh`. “Handler theorem T1” explicitly names `Games.exists_handlerMachine`, distinguishing it from pairing T1; consistently spelling out “Games” would improve readability. |
| **9 — replay and axioms** | **Pass on supplied evidence.** Independently reconstructed the 16-module downstream set and 1,427-module root/audit closure. All 16 build logs and source bindings recount cleanly: rc 0, no errors, exactly the two T2/T3 admission warnings. Census: **198 → 196**, exactly T1 and T4 removed. Both targets have the standard three axioms and no sorried dependency; the owner census has 604 constants and no nonstandard axioms. State, output-map and snapshot-preservation records are consistent. |
| **10 — disclosures** | G44-03 is an additional pack discrepancy. Other recorded staging/provenance slips do not alter the audited code or conclusions. The shared signing key establishes account-session provenance, not individual authorship. |

The BB04 page locators and the PS10 Euclid/statistical-closeness locators were checked against the primary texts. [crypto.stanford.edu](https://crypto.stanford.edu/~xb/eurocrypt04b/bbibe.pdf?utm_source=chatgpt.com)

The principal bounds checked are

\[
\operatorname{accept}(G.\mathrm{bdhGame}\ A\ \kappa)
\le G.\mathrm{dbdhAdv}\ D\ \kappa+2^{-\kappa}+\delta(\kappa),
\]

\[
q(\kappa)2^{-n}\le(q(\kappa)+1)2^{-\kappa}=\sigma(\kappa),
\qquad n=\kappa+w_G(\kappa)+1.
\]

## Grades: BM-F01–BM-F09

These dispositions do not add to the open-finding counts.

| Finding | Grade / disposition |
|---|---|
| BM-F01 | Agree: note, **closed** by removal of the unused proof. |
| BM-F02 | Agree: minor, **closed** by corrected argument order and explicit security parameter. |
| BM-F03 | Agree: evidence note, **closed**. Independently recounted Oracles controls: 14 negative and 14 reader rows per variant, all as expected. |
| BM-F04 | Agree: note, superseded by landing-head seals and unchanged-input comparisons. |
| BM-F05 | Agree: evidence nits; source/log/hash checks resolve the substantive questions. G44-03 is separate. |
| BM-F06 | Agree: inherited documentation note, outside permitted edits. |
| BM-F07 | Agree: size note; the files exceed the target but remain below the cap. |
| BM-F08 | Agree: disclosed promotion request. The private range-type lemmas derive from published readers without re-proving an existing public IBE theorem. |
| BM-F09 | Agree: suitable machine-specific public glue, with its formula and sketch. |

## Grades: #340’s seven overlap disclosures

| Item | Grade / disposition |
|---|---|
| 1 — raw machine versus `NUPPT.wrap` | Agree. Composition of verified construction layers; the alternative’s bookkeeping does not make this an additional copied theorem. |
| 2 — equality test | Agree. `polyTimeComputable_pairEq` is reused. |
| 3 — projections | Agree. Fixed compositions of published projections; the iterated-first-projection theorem does not supply the required second-projection contract. |
| 4 — target probability | Agree. Tuple-specific application of published probability/injectivity facts; the list-membership bound is a near-alternative. |
| 5 — verdict identity | **Reject “no duplicated proved material / no ledger”: G44-01.** The exact public identity is re-derived inline. Disclosure does not establish acceptance of retained debt. |
| 6 — bad-order bound | Agree as disclosed pattern overlap. The ElGamal safe-prime/index proof is not copied as an interchangeable theorem. |
| 7 — advantage inequality | Agree. Direct absolute-value API use; no matching public Games lemma was identified. |

The checkpoint’s identical round-input projections and polynomial-time facts have the same acceptance gap. Its API obstruction is real, but the required acceptance/repayment record is absent. Other disclosed specializations, casts, encoding-contract applications and simulator comparisons have different contracts or apply existing facts.

## Verification and limits

All **14/14** outer and **549/549** verification-archive checksums pass, with an exact file set. All **186** source-manifest entries pass; **181** Lean source copies bind to pinned git blobs. All **43** bundle sections match their separate copies. The two additionally consulted review archives verify **962/962** and **255/255** inner files and their pinned outer hashes.

The ZIP contains the independent checks, results, mutation-control reruns and pinned duplication ledger. **I did not run a fresh Lean compilation**; compilation/axiom conclusions use the hash-bound supplied replay and probes, independently recounted and checked against the inspected sources.

Gate 40, the T2/T3 fill and #351/#352 are not re-audited. Merge order and snapshot adoption remain maintainer conditions.

**Notation:** `A`: adversary/solver; `D`: reduction distinguisher; `G`: bilinear generator; `κ`: security parameter; `q(κ)`: query budget; `w_G(κ)`: source-group encoding width; `n`: sampler width defined above; `δ(κ)`: bad-order bound; `σ(κ)`: simulation-error bound. T1/T4 and BM-F01–BM-F09 retain the campaign’s labels.
