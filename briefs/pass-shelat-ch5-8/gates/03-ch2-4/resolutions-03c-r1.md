# Gate 03c (hard-core bits and PRGs): round 1 resolutions

- **Round 1:** findings `findings/gate03c-findings.md`, verbatim, SHA-256
  `0547776d90b620023b825684a873ebb11f4ec0c3fbf9baa54f02a4da80376a3a`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 1 major (#1), 5 minors,
  5 notes.**
- **Review:** `review/gate03c-review.md`: 9 true, 2 partly true (#1, #4), none false. #1 stays a
  major, not a blocker (no statement of ch. 2–8 is about a stretch-`2n` `PRG`). One severity
  change, proposed by the review: #3 from minor to **major** (the library's own trapdoor
  collections fail `henc`). New tally **0 blockers, 2 majors, 4 minors, 5 notes**. Eight items
  missed by the auditor (M1–M8 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`; decision log rows "Gate 03 rulings G3-1 to
  G3-4" and "G3-5 to G3-8"**):** G3-2 (A), keep `∀ n, n < ℓ(n)` and declare the cost (#1); G3-7 (b),
  drop Thm 75.4's extra hypothesis (#2); G3-7 (c), state `henc`'s cost now (#3); G3-6 (A), approve
  the listed `@[simp]` (#11).
- **Repair:** commit `bc2aab59333e27729c9fbac3052cd650bf62c3aa` (on #198's head
  `c10ed6ace0b991146c0be769313fbbe52d36e25a`), in PR #201 with 03a's
  `e8f45ca3ca7246d1379c4b66ce5a7a72d0b2d820`; #201's head
  `0c348ff94cacf24d96d99078c9dd9e328530c8d2` is **not yet merged**, so every "Fixed" below except
  #3 is on #201's branch only. #3 (G3-7 (c)) was done in #198 (`c10ed6ac…`, merged by
  `cdff8890ee4af8eec7d6682963c02041390f52f2`). Evidence `evidence-repairs/03ac/` (replay of the
  97 downstream modules plus `Checks`, the `Checks` axiom print at #201's head, lint 0). Line numbers
  are at #201's head; Lean paths are under `TCSlib/Cryptography/Asymptotic/`.
- **Moved file:** `HardCore.lean`'s collection section (17 declarations, statements unchanged) is
  now `HardCoreCollection.lean`, which `HardCore.lean` imports (#11).

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major (not blocker) | **Fixed** (G3-2; docstrings and DESIGN, no statement change). A second Deviation on `PRG` (`Pseudorandom.lean:120–131`, with the module docstring :38–41 and the `expands` field :137–139) states the cost and the routes (`prg_expand` from `PRG.truncate`, `truncateTo_*`, `DoublingPRG`); "`ℓ(n) > n` at every `n`, see `PRG`" in `HardCore.lean:64, 372–377, 441, 452`; DESIGN §2.12 line comment and §5 item 25 (`briefs/pass-shelat/DESIGN.md:714, 1068–1078`). |
| 2 | minor | **Fixed** (G3-7 (b); a strengthening). `Ensemble.NextBitUnpredictable.pseudorandom` no longer takes `hℓ` (`NextBit.lean:682–683`; repair note :657–659), via the machine lemma for every position (:573–577) and the new `prgAdv_eq_zero_of_length_eq_zero` (:453); `stretch_pos`'s attribution fixed (`Pseudorandom.lean:178–180`); DESIGN §2.12 (`DESIGN.md:723`). Both print standard (`evidence-repairs/03ac/checks-axioms.log:241–243, 484`); no Lean consumer. |
| 3 | major (review; was minor) | **Fixed** (G3-7 (c), in #198). `Collection.glPad`'s deviation states the cost (no library candidate satisfies `henc`; `HardCoreCollection.lean:84–91`), as does DESIGN §5 item 18 (`DESIGN.md:1036–1045`); "satisfiable from trapdoor permutations alone" is replaced in `HardCoreCollection.lean:344–347` and `PublicKey.lean:809–812, 952–958`. `henc` itself is unchanged (the per-index form is not formalized, as ruled). |
| 4 | minor (partly true) | **Fixed** (record). DESIGN §2.12 records the shipped one-bit signature and the route through `PRG.truncate`/`PRG.Secure.truncate` (`DESIGN.md:732–737`), as does `prg_expand`'s docstring (`HardCore.lean:445`). The optional `PRG.Secure.expand` corollary is left to 03d (commit message only). |
| 5 | minor | **Fixed.** The sketches of `nextBitProb_nextBitPred_false` (`NextBit.lean:369–379`) and `acceptProb_nextBitHybrid_mix` (:320–325) now go through `uprob_split_bit`'s involution; inventory-ch3 Thm-75.4.2 is annotated (`briefs/pass-shelat/inventory-ch3.md:319–321`). **Recorded here**, as the review asks (the run-3 summary is closed): *P2-3* is the run-3 repair that replaced the 2-to-1 planting map by `uprob_split_bit` (`NextBit.lean:236–243`). |
| 6 | minor | **Fixed.** The eleven prints (`fact_88_4`, `thm_87_3_1/2/3/6/7/8/9`, `not_hardCore_const`, `Ensemble.uniform_nextBitUnpredictable`, `PermCollection.OneWay.glPad_hardCore`) are in `audits/pass-shelat/Checks.lean:559–571`; all standard at #201's head (`checks-axioms.log:485–495`). |
| 7 | note | **Fixed** (docstrings). `HardCoreClaims.lean:14–27` separates the family-level claims (`thm_87_3_1/2/3/9`) from the concrete ones (`fact_88_4`, `thm_87_3_6/7/8`); `thm_87_3_6` (:109–117) places the formal `1/(4mε'²)` between the text's `(1 − 4ε'²)/(4mε'²)` and `1/(mε'²)`, `m` being the `2^k − 1` samples; `thm_87_3_8` (:134–139) notes `m = 2^k`. |
| 8 | note | **No change** in 03c (scope note, answered by 03b's audit of `Collection.HardCore`, #1, #3, #7). After G3-1, `Collection.glPad` proves `encD_decD` (`HardCoreCollection.lean:103–107`); the collection section is re-verified in this closing round. |
| 9 | note | **No change:** answered by 03i's evidence (`evidence/i/axioms.log:13–15`: `glHalf`, `exists_owp_hardCore`, `exists_securePRG_of_owp` standard; replay `sorry=0`). |
| 10 | note | **Fixed.** Remarks for Constr-77.a (Shamir), Claim-78.a and Claim-78.b in `HardCore.lean`'s module docstring (:73–82). Claim-107.c is not formalized (optional, DESIGN §6.2). |
| 11 | note | **Fixed**, with G3-6. New `PRG.easy_iff` (`Pseudorandom.lean:156`), `hardCore_iff`, `PRG.oneBit_stretch`, `PRG.oneBit_G`, `owpPredictorSnoc_eq`, `oneBitStep_eq`, `expandRed_eq` (`HardCore.lean:161, 221, 225, 253, 366, 405`) and `Collection.glBit_eq` (`HardCoreCollection.lean:146`), printed (`Checks.lean:572–580`); `HardCore.lean` split (775 and 353 lines). **Recorded** (G3-6): `PRG.ensemble_X` keeps `@[simp]` (`Pseudorandom.lean:173`), against the review's per-pack advice to drop it. `NextBit.lean` is not split (972 lines; the review did not ask). |
| M1 | (review) the cost was declared in `PRF.lean` | **No change** (observation). The new `PRG` deviation cites `DoublingPRG`, `PRG.truncate` and `PRG.doubling`. |
| M2 | (review) no downstream statement is vacuous | **No change:** #1's escalation test fails, so #1 is not a blocker. |
| M3 | (review) `henc` fails for the library's trapdoors | **Fixed** with #3 (G3-7 (c)). |
| M4 | (review) #1 and #2 interact | **No change:** G3-2 keeps `∀ n`, so the interaction is not triggered; G3-7 (b) removed `hℓ` anyway. |
| M5 | (review) the PDF checks are settled | **No change.** #7's docstring quotes the per-bit bound from the raw extract (`blueprint/src/references/pass-shelat-2010-ch3.raw.md`, about l. 995–997). |
| M6 | (review) "eventually" equals "from 2 on"; "PRGs exist" is unchanged | **No change**; the second remark is in the `PRG` deviation (`Pseudorandom.lean:127–130`, not formalized). |
| M7 | (review) note #8 is answered by 03b | **Recorded** with #8. |
| M8 | (review) note #9 is answered by 03i's evidence | **No change** (see #9). |
