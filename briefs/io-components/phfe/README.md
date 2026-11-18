# io-phfe: dispatch pack (degree-2 PHFE from DLIN, [Wee20] in the JLS26 pipeline)

The second iO-components job (IOComponentsPlan.md): one end-to-end Codex job in a local checkout,
with a statements gate on its checkpoint 0 and a proofs gate on its final. Prepared 2026-11-18
at records `0fec2589`. Static only; nothing is committed or dispatched.

## Contents

| File | What |
|---|---|
| `sources.md` | What was obtained (JLS26) and what was refused (both ePrint PDFs: Cloudflare 403); the citation chain (a)–(c) with its verification status |
| `design-r1.md` | The design note: settled conventions (§ 0), the chain and bridge rule (§ 1), layout (§ 3), statement shapes (§ 4: DLIN, exponent vectors, generic FE, the bidegree-(d, 2) class, PHFE, `wee20PHFE`, headlines), machines (§ 5), milestones with sizes (§ 6), **questions Q1–Q14** (§ 7), risks, extensions |
| `duplication-sweep.md` | TCSlib and Mathlib items with `file:line`, must-reuse or not; gaps; overlap with the parallel sPRG job and Stage 2 |
| `dispatch-prompt.md` | The prompt Seyoon pastes into Codex, with placeholders `<BASE>`, `<RECORDS>`, `<EXCHANGE>`, `<GJLS21-PHFE-DEF>`, `<WEE20-THM>` |

## Open questions (design-r1 § 7)

Seyoon's input matters most on:
- **Q1**, the PHFE security notion GJLS21 Theorems 10.3/10.4 consume, and its definition number;
- **Q2**, the function class: bidegree (d, 2) recommended, against NC¹;
- **Q3**, correctness in the exponent;
- **Q6**, the proof architecture and hybrid sequence.

Q4 (compactness) and Q5 (generality of the FE syntax) follow from these.

Engineering questions with recommended defaults:
- Q7: where DLIN lives; two facades touched;
- Q8: g uniform in G*;
- Q9: the drawn group order as the modulus;
- Q10: independence from the sPRG representation;
- Q11: the oracle game shape;
- Q12: a typed universal simulator;
- Q13: partial-delivery rule;
- Q14: k = 2 only.

Sampling is settled, not asked: the pairing convention is reused, and the sampler bridge is
deferred.

## Before dispatch (maintainer and Seyoon)

1. **Rulings** on Q1–Q14. Record them in `briefs/io-components/phfe/rulings.md`, with a
   decision-log row in `IOComponentsPlan.md`. Q1 needs GJLS21's PHFE definition number at the
   ePrint revision being staged.
2. **Sources.** Automated fetches from eprint.iacr.org are refused, so Seyoon downloads them by
   hand:
   - ePrint **2020/1420** ([Wee20]);
   - ePrint **2020/764** ([GJLS21]), the revision whose Theorems 10.3/10.4 match JLS26 Theorem 5.1;
     check the latest, 2025-01-03, first;
   - the JLS26 PDF (SHA-256 `bb357e8d…2f3d`).

   Stage them on the exchange at `outbox/io-components/sources/` with a `SHA256SUMS`, and record
   the hashes in `sources.md`.
3. **Re-read the chain** against the staged PDFs, before or with the rulings: links (b) and (c) of
   `sources.md` § 3. If Wee20's notion differs from GJLS21's, name the bridge's literature place
   (design § 1.3).
4. **Fill the placeholders** in `dispatch-prompt.md`:
   - `<GJLS21-PHFE-DEF>` and `<WEE20-THM>` from step 3;
   - `<BASE>`, the records tip at dispatch;
   - `<RECORDS>`, the commit carrying this folder with `rulings.md`;
   - `<EXCHANGE>`, the staging commit.

   All are full hashes from `git rev-parse`. Adjust the *Scope* item if Q7 is not (A).
5. **Check the host plan** with the sPRG job's dispatch: 3 Lean processes on the Mac in all. This
   job holds 1, so the sPRG job may hold at most 2. Both use `lean-slot.sh` with distinct tags.
6. Commit and push the records, push the exchange staging, and then the prompt is **Ready to
   dispatch**.
