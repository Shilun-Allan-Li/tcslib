# Gate 03h ([PS10] ch. 2–4, ch. 2 results and the universal one-way function): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/h/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the statements of ch. 2's main results proved in their own files: Yao's amplification (Thm 35.1's proof) and its lemmas, the collections theorem's proof (Thm 42.2), and the universal one-way function of §2.13.
- **This pack gates fills.** Its files hold **2 `sorry`s**, to be filled after this pack
  closes (user's ruling of 2026-11-05). A statement that cannot be proved as stated, or that is
  weaker than the source, must be found **now**.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03h-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §2.4.3 (book pp. 36–40), §2.5 (pp. 41–42) and §2.13 (pp. 63–65).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also, for **every sorried
declaration**, say whether it is (a) true as stated and provable from the hypotheses it carries,
(b) true but weaker than the source, or (c) false or unprovable as stated. For (c), give a
counterexample or the missing hypothesis. Attempt at least **three adversarial instantiations**,
for example:
- a universal function whose enumeration misses machines of some code length;
- an amplification whose repetition count is not polynomial;
- a padding that changes the input distribution.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Asymptotic/{OneWayLemmas, OneWayYao, CollectionsLemmas, Universal, UniversalLemmas, UniversalPadding}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | pack 03b's files (one-wayness, collections); the machine layer (`Complexity/Randomized/`, and `Complexity/TuringMachine/` from `main`) |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D11 (`CanonizerExp`, ratified as an explicit hypothesis, with its open problem); §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Thm-35.1 (proof), Claim-38.2, Thm-42.2 (proof), Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the definitions of pack 03b |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/h/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 69 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   19 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 9 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 6 use only the standard axioms, and
   3 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 2 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 6 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints of this pack's headlines (`audits/pass-shelat/Checks.lean`);
- admissions: the 2 `sorry`s, listed by declaration;
- lint.

## Specific questions

1. **Yao's amplification.** Are the lemmas of `OneWayYao` stated at the parameters the proof
   of Thm 35.1 needs (the number of rounds, and `statClose_roundSample` and `statClose_sampleAll`)?
2. **Thm 42.2's proof** (`CollectionsLemmas`). Are both directions' auxiliary statements right?
3. **The universal OWF (Thm 63.1, Lem 64.3).**
   - Is `theorem_63_1` stated under `CanonizerExp` as an explicit hypothesis?
   - Is the open-problem stub `exists_canonizerExp` (sorried) correctly labelled? Is it true?
   - Is `exists_linearTime_gStr` (sorried, a machine construction) true as stated, with the right
     linear-time bound?
4. **Sorried statements.** Give both a sorry verdict (a / b / c).

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. Add the column **Sorry verdict** (a / b / c, see the
brief) for sorried declarations. The pack closes at **0 blockers and 0 majors**.
