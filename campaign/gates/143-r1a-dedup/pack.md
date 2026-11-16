# Gate 143 · Closeout R1a: BW-1 and the CH34-D4 leftovers (PR #329)

**Not yet clear to merge** · PR #329 is a draft. Seyoon dispatches and merges.
The Lean head is `45d0ce546318188d7991ef65429138071b5c152a` (two commits), against the campaign at
`ba0a67e40a13385df82a8cf43ef57be18d006139` (Lean as after #325). This is the first audit.

## Scope

Chapters 3–4 closeout, refactor wave R1 (`campaign/closeout/REFACTOR-PLAN.md`, agreed by
Seyoon 2026-11-16, bundled). This gate retires two acknowledged duplication families by
replacing re-proved facts with citations of the existing public lemmas:

- **BW-1** (ledger, 2026-10-18 ruling: "`StepBlock` imports the module and its four privates
  are deleted, their uses re-pointed"). `Build/StepBlock.lean` now imports
  `TuringMachine/BufferWords`. Its four private lemmas `bufferTape_unary`, `bufferTape_outside`,
  `bufferTape_reads` and `bufferTape_suffix` keep their names and statements, and each proof is
  a one-line citation of `Turing.FinTM.bufferTape_unary`, `bufferTape_eq_none_of_not_mem`,
  `bufferTape_append_mid` and `bufferTape_append_shift`.
- **CH34-D4 leftovers** (backlog). `TimeHierarchy/Separation.lean`'s private `bits_two_pow` cites
  `Turing.bits_two_pow_eq_replicate`. `CircuitComplexity/MeyerTableau.lean`'s public
  `Complexity.Meyer.incFixed_eq_none_iff` keeps its name and statement, and cites
  `Turing.incFixed_eq_none_iff_replicate`. MeyerTableau is a colleague file, edited
  mechanically under the 2026-11-06 ruling (HANDOFF §3 item 4), with an FYI in the PR.

**Deviation from the BW-1 wording, to rule on.** The first commit (`293e4963`) deleted the
privates and re-pointed their five use sites. The sealed check then failed on those use sites
(`StepBlock`'s round proofs, 11 errors; `timeConstructible_two_pow`, 2 errors). The failures
came from their unchanged text, which reads other files' definitions (`simp [Cfg.mapState]`;
the `TimeConstructible` anonymous constructor): debt that predates rule 10 and that the edit
exposed. The second commit keeps the private names as citations, so every use site is
byte-identical to the base and the copied proofs are still retired. The first attempt's sealed
logs and check summary are in the carrier under `first-attempt/` (its replay passed and is not
included; the second commit's replay is).

## Brief for the auditor

1. **Statements and names.** `evidence/SOURCE.json`: 3 owners, 6 changed declarations
   (the five citations and Meyer's theorem), none added, removed or restated. Check that each
   changed declaration's statement is unchanged and that its new proof is exactly a citation of
   the named public lemma, with matching statements.
2. **The import.** Check that `StepBlock` importing `BufferWords` creates no cycle and is the
   import the BW-1 ruling prescribed.
3. **Rule 10.** Seals (`seals/`): the six changed proofs pass with every other-file definition
   they reach irreducible (2 heads); the 13 paired controls each close natively and fail sealed.
   The proof-syntax sweep finds 0 explicit foreign-definition reads in them.
4. **Use sites.** Check that no use site changed (`patch/campaign-to-head.patch`).
5. **Copy screen** (population: the three owners and the three cited homes, `BufferWords`,
   `Encoding`, `Convention`): BASE 165 declarations and 17 pairs, HEAD 159 and 15. No new pair; the
   two gone are the `incFixed_eq_none_iff` copy. BW-1 and `bits_two_pow` were restated facts with
   different proofs, which the copy-text screen does not pair.
6. **Records.** Rule on, or flag, the deviation above (the four privates kept as citations
   rather than deleted), and check that the refactor plan's R1 row and the ledger's R0
   reconciliation describe this PR accurately.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure of the three changed
  modules (41 modules) on the campaign snapshot after #325 (876 objects; prospective tree
  `19945718d537ea31faa33b0498b35e68ef14a099`). 41 passed, 0 failed. The 21 inherited admissions are
  `ClassPSPACE/TQBF.lean`'s `ConfigCodec` ones, downstream of `StepBlock`, which gate 142 (PR #328)
  removes.
- Metadata: the changed proofs use standard axioms only. Lint: no change.
- `evidence/DATA-CARRIER.json` and its recovery map. Decode each gzip+base64 blob and check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate143-r1a-dedup-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
