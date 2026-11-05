# Gate 03e (interaction, proof systems, ZK definitions, commitments, NP layer): round 1 resolutions

- **Round 1:** findings `findings/gate03e-findings.md`, verbatim, SHA-256
  `8af18f12965eb01b594de42d60e567b4ad5cb2810652a94f70f7daf0aef0a7e3`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 2 majors (#1, #2), 4 minors,
  11 notes.**
- **Review:** `review/gate03e-review.md`: no finding false; by its tables 15 true (#6 (c) left
  unverified) and 2 partly true (#5, #16). No severity change (2 majors, 4 minors, 11 notes).
  Corrections to the auditor's proposed fixes for #1, #5 (c), #12, #13 and the pack labels. Ten
  items missed by the auditor (M1–M10 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`; decision log rows "Gate 03 rulings G3-1 to
  G3-4" and "G3-5 to G3-8"**):** G3-3 (A) = R-03e-1 option 1, `Efficient` plus bounded honest
  messages in the definitions (#1); G3-4 (A) = R-03e-2 option 1, keep the perfect forms, state the
  cost, prove `PerfectZKAbort.statZK` (#2); G3-6 (A) = R-03e-3, approve the 15 `@[simp]` (#17);
  G3-7 (d) = R-03e-4, `InteractiveProofErr.seqRep` in prong C (#3); G3-5 (A) for the copy
  `negligible_const_zero` (DL-13). Q-1 (no cap on `V*`) stands (#7).
- **Repair:** worker commit `30f90d36ab23d8f6b9ac99e4608c38174f3bfcb1` (on `a3c5fa8b…`), merged
  with #198's head as `b925421ece04d3189f5fc8c6ed4c6884e5caae49` = PR #199's head, merged into
  `cryptography/pass-shelat-ch2-4` by `af91d53a414cdad6bbb61cecdc13f5e0e956d0b1`. Evidence
  `evidence-repairs/03e/` (31 downstream modules on the stacked state; `Checks` 328 prints, 57
  `sorryAx`); the prints below are also in `evidence-repairs/03ac/checks-axioms.log` at #201's head
  (`0c348ff94cacf24d96d99078c9dd9e328530c8d2`, which contains #199). Line numbers are at #201's head;
  Lean paths are under `TCSlib/Cryptography/ZeroKnowledge/`.
- **Outside ch. 2–4:** G3-7 (d) is prong C commit `9e6f08bb28b2fcebfa845d47a9fd6e1ed281f951`; prong
  C's re-sync to G3-3 and G3-4 is in gate 06's integration to-do
  (`gates/06-ch5-8-statements/PLAN.md:55–57`).

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major | **Fixed** (G3-3). `Protocol.ProverBounded` is in `Interaction.lean:331–337`; `InteractiveProof(Err).complete` bounds the honest messages (`InteractiveProofs.lean:126–128, 149–151`), `EfficientProverProof(Err)` has `boundedP` (:346, :361), with bound lemmas (`InteractiveProofs.lean:466`, `NP.lean:273`, `GraphIsomorphism.lean:926, 930, 935`, `ThreeColoring/Protocol.lean:562, 580, 605`), the "PPT" docstrings replaced, statements re-proved unchanged, prints standard. **Fixed (records, after #201 merged):** DESIGN §5 item 8 (`briefs/pass-shelat/DESIGN.md:1009–1014`) now states the bounded-message convention; the 03e repair had not amended (review §1.1); prong C's local `ProverBounded` is **Scheduled** for gate 06 integration. |
| 2 | major | **Fixed** in ch. 2–4 (G3-4); prong C scheduled. The cost is stated on `PerfectZK` and `PerfectZKAbort` (`Defs.lean:173–180, 189–196`) and in the module docstring (:50–57); `PerfectZKAbort.statZK` (error `2^{-\|x\|}`), `.zk` and `perfectZK_zeroRounds` are proved (:535, :596, :269), and `GraphIsomorphismZK.lean:43–48` cross-references. **Fixed (records, after #201 merged):** DESIGN §5 item 11 (`DESIGN.md:1019–1023`) no longer says "`PerfectZKAbort` stated as the perfect form": no source protocol attains the perfect forms; GI is `StatZK`. **Fixed (records):** the Thm-175.1 row of `inventory-ch5-8.md`. **Scheduled:** prong C's `SequentialZK.lean` (:41–45, `PerfectZKAbort.seqRep` through `statZK`) at gate 06 integration; the `inventory-ch5-8.md:130` row is not named there. |
| 3 | minor | **Fixed.** Titles retitled to "a zero-knowledge protocol with soundness error …" (`NP.lean:563–581, 595–607`); tied forms `exists_commitment_zk_proof_of_owp_levinReduction`, `zk_proof_of_witnessRelation(_of_owp)` (:625–634, :679, :698); the text's Thm 124.1 recorded as debt for ch. 7 (:575–576). The debt's discharge (G3-7 (d)): `InteractiveProofErr.seqRep` is in prong C (`9e6f08bb…`); the 3-colouring corollary is **Scheduled** for gate 06 integration (decision log, G3-7d row). |
| 4 | minor | **Fixed.** `zk_proof_of_witnessRelation` holds for every witness relation (`NP.lean:679`); `zk_proof_of_mem_NP` (:729) is its corollary, statement unchanged. |
| 5 | minor (partly true) | **Fixed.** (a) The `sorryAx` prints are annotated with the stubs they reach, `colRep_efficientProverProof` and `col_zk` (`audits/pass-shelat/Checks.lean:321–324`); (b) the five prints (:418–423), standard at #201's head. **Fixed (records):** (c)'s record fixes, an erratum on `audits/pass-shelat/run3-audit-summary.md:17` (it meant `Complexity/Randomized/Build/*`; of the 22 non-ZK `sorry` warnings in 03e's closure, 21 are `main`'s and one is `NonUniform`'s optional admission). The drafter found them missing: `audits/pass-shelat/run3-audit-summary.md:17` still names `TuringMachine/Build/*` (it means `Complexity/Randomized/Build/*`), and no attestation says the 22 core-module sorries are `main`'s (MIG-1 stage S), as the review found. |
| 6 | minor | **Fixed** in ch. 2–4; prong C scheduled. (a) `[Gol01]` in `Defs.lean:68, 102, 184` and `GraphIsomorphismZK.lean:87, 289`; (b) the p. 116 misquotes paraphrased (`Interaction.lean:46–48, 160–162`); (c) `[AB09, §2.3]` (`NP.lean:114–115`). **Scheduled:** the tag in prong C's `Composability/SequentialZK.lean:85`, now in gate 06's integration to-do (`gates/06-ch5-8-statements/PLAN.md`). |
| 7 | note | **Fixed.** `ZK`'s deviation records Q-1 (no cap on `V*`) and why the view is still bounded (`Defs.lean:146–152`). |
| 8 | note | **Fixed.** The dummy-move repetition convention, with its users, in `Interaction.lean:39–43`. |
| 9 | note | **Fixed.** The necessity argument for `Lz` and for advice indexed by `\|x\|` is in `Defs.lean:42–47`. **Fixed (records, after #201 merged):** the source issue is DESIGN §7 item 51, beside item 50. |
| 10 | note | **Fixed.** `perfectZK_zeroRounds` (`Defs.lean:269`); `gi_statZK` named as the substantive instance in the module docstring (:53–56). |
| 11 | note | **Fixed.** `WitnessRelation`'s docstring states the daylight with Def 191.11 (`InteractiveProofs.lean:239–249`). |
| 12 | note | **No change** needed (already met: `colVerify` checks the lengths); the optional sentence is added to `Commitment` (`Commitment.lean:107–110`). |
| 13 | note | **Fixed.** `exists_commitment_of_owp`, the text's Thm 126.4 (`Commitment.lean:905–911`); its print is standard. |
| 14 | note | **Fixed.** The padding remark now says "assumed" (`NP.lean:35, 131`); the pointer belongs to 03g. |
| 15 | note | **Fixed (records).** Both limits (Barak–Lindell on black-box strict-PPT simulation; everything indexed by `\|x\|`) are recorded in `SPINE-DESIGN.md` §S1, "Two limits of the interaction model D8 for ch. 5–8". |
| 16 | note (partly true) | **Fixed in the closing-round pack** (pack text): Thm-124.1 and Claim-124.d are owned by 03g and listed in 03e's pack as "(also 03g)". |
| 17 | note | **Recorded** (G3-6, `QUEUE.md:125`): the 15 are approved and unchanged: `encodeMsgs_nil/cons`, `moverIsV_true/false`, `exec_zero`, `withV_V/P/rounds/verifierFirst/self` (`Interaction.lean`), `mem_witnessLanguage`, `mem_witnessSet` (`InteractiveProofs.lean`), `bitCom_castSucc/last`, `owpComLen_eval` (`Commitment.lean`). |
| M1 | (review) a prefix cap does not give `ProverBounded` | **No change:** informed G3-3's option 1, which bounds the honest messages directly. |
| M2 | (review) the 3-colouring parties are not prefix-reading | **No change:** option 1 needs no redefinition; `colProtocol_proverBounded` (`ThreeColoring/Protocol.lean:605`) comes from `Com`'s polynomial time. |
| M3 | (review) the bound must sit in the completeness clause | **Fixed** (`InteractiveProofs.lean:126–128, 149–151`). |
| M4 | (review) the perfect-ZK obstruction is inherent | **Fixed:** both arguments (`n! ∤ 2^c`; dyadic simulator laws) are in `Defs.lean:173–180, 189–196` and `GraphIsomorphismZK.lean:43–48`. |
| M5 | (review) misleading text in DESIGN §5 item 11 and `SequentialZK.lean` | **Fixed** for DESIGN (§5 item 11, records); **Scheduled** for `SequentialZK.lean:41–45, 397–399` at gate 06 integration (`PLAN.md`). See #2. |
| M6 | (review) no soundness amplification for `seqRep` | **Fixed** in prong C (G3-7 (d), `9e6f08bb…`: `InteractiveProofErr.seqRep`, `EfficientProverProofErr.seqRep`); the 3-colouring corollary is **Scheduled** (gate 06 integration). |
| M7 | (review) pack labels; 03e's scope line | **Fixed in the closing-round pack:** 03g is 3-colouring and 03k graph isomorphism (`03e-pack.md:39` had them swapped). 03g's re-staged pack (`b13af7af`) points at the rulings. |
| M8 | (review) #12 met, #13's premise outdated, #5 (c) reconciled | **No change**, except #5 (c)'s record correction, which is not done (see #5). |
| M9 | (review) "PPT strategy" field docstrings; second misquote | **Fixed:** no "PPT strategy" remains in `InteractiveProofs.lean`; `Interaction.lean:46–48` paraphrases. |
| M10 | (review) removing the 15 `@[simp]` breaks proofs | **No change** (G3-6 approves them). |
