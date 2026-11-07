# Gate 114: one home for binary-length bounds, PR #222

Audit [PR #222](https://github.com/Shilun-Allan-Li/tcslib/pull/222),
`lean/dedup-natbits`, against the campaign. The immutable commits are in the bundle header and
`evidence/current/landing/refs.json`. The user selected Codex for this audit and dispatches it.

## Scope and approved decisions

The PR implements BL-1 and NB-1, pays LS-3, and moves BL-2's published lemma to the shared home.
The user's D1–D6 defaults, one-PR decision, D7 authorization of the two mechanical Meyer edits,
D8 blueprint decision and D9 record-only ruling are recorded in
`campaign/items/dedup/natbits-PLAN.md` and `natbits-SCOPE.md`. Those historical site tables have
older line numbers; use the current diff and census for the audited tree.

The new `TCSlib/Complexity/TuringMachine/NatBits.lean` has 144 lines, ten public theorems, no
private source declarations and Mathlib imports only. The compiled module has **16 constants**:
the ten source theorems plus six moved internal proof auxiliaries. All 16 receive axiom checks.
Keeping the two namespace roots was explicitly
approved to preserve names. Encoding and Bin import it; no consumer site gets an additional
import. The TuringMachine facade imports and lists it.

| Public surface | Disposition |
|---|---|
| `Turing.length_bits_le_self`; `Complexity.LogProg.length_bits_le`, `length_bits_succ_le`, `two_pow_bits_le`, `length_bits_mono`, `length_bits_le_log` | Six declarations move with names and statements preserved |
| `Randomized.PolyAmp.lt_two_pow_bits` | Moves to `Complexity.LogProg.lt_two_pow_bits`, as approved |
| `Randomized.PolyAmp.two_pow_bits_le` | Removed in favor of `Complexity.LogProg.two_pow_bits_le_two_mul_add_one` |
| `Complexity.Codec.bitsVal_lt_two_pow` | Exact copy removed; consumers resolve to `Complexity.LogProg.bitsVal_lt_two_pow`, which stays beside `bitsVal` in Bin |
| `Complexity.LogProg.length_bits_eq_log`, `ofDigits_lt_two_pow` | Approved new equality and `ofDigits` form |

The latter two and the 2n+1 bound are the three approved additions. The optional `Nat.bits`
shift laws remain in Encoding. The root Contents and the deleted private `clCount_width` blueprint
entry are updated mechanically; the existing Encoding binding for `length_bits_le_self` remains.

The current diff changes 22 Lean files. The scope table's 21 member sites plus Meyer ×2 are
re-pointed; seven redundant private declarations are removed. Across changed files the census is
2,366 → 2,360 source declarations. All surviving statements, visibility and order are frozen.
Six public bodies change: Meyer `lenAll_inst` and `bits_pad`, `PolyAmp.bigK_le`,
`Randomized.le_two_pow_size_pred`, `Turing.record_pos_lt`, and `LogProg.halfL_run`. The latter is
the same pinned buffer-cell repair as #215, required after the import/simp-set change.

## Brief for the auditor

Follow `campaign/standards/TEMPLATE.md`, `policy.md`, `workflow.md` and the duplication ledger.
Do not review existing tactic scripts for logical correctness. Audit statements, API placement,
name resolution, semantic reuse, rule 10 and cumulative debt.

1. Check the ten statements literally, particularly zero: `bits 0 = []`, so the log equality
   requires nonzero input and the unconditional power bound is `2n+1`. Check the positive `2n`
   bound, the increment-width bound at its largest allowed input, and the empty `ofDigits` word.
   Give at least three adversarial instantiations; the executed sanity probe supplies seven
   boundary checks to challenge.
2. Verify the six preserved-name moves, the approved namespace move/removals and all surviving
   public/private statements and relative order. Distinguish source declarations from compiler
   constants: the imported-module census lists every non-private constant without filtering
   generated auxiliaries.
3. Check every scoped inline form, not just named copies: size conversions, logarithmic chains,
   `have` bounds, simp sets and rewrite chains. Verify that no consumer silently resolves the
   deleted 2n+1 name to the different positive-only statement.
4. Recheck dependency direction: NatBits is below both Encoding and Bin and has no TCSlib import.
   The two roots and the Meyer edits are approved; this pack requests no additional API or rename.
   The new module consequently has no foreign TCSlib definition to seal. Frag's exact changed
   cell step is checked under a bufferTape seal; this does not claim a global seal of legacy code.
5. Challenge the candidate classifications and cumulative counts. D9 families are record-only,
   as ruled. Searches include the current E-PAD landing and the original delivery: the delivery's
   duplicate bound and two inline length re-derivations were removed/re-pointed while landing
   #228, using already published declarations and without relying on this unmerged PR.

## Evidence and its limits

The complete changed-file list is `evidence/current/landing/changed-lean-files.txt`; all 22 files
are the screen population and are bundled in full. `evidence/current/README.md` summarizes the
actual source freeze, lint, blueprint, standalone preflight, imported-module axiom/census probes,
Frag seal and independent merged-tree replay. Raw inputs, outputs and per-run receipts are beside
it. Initial failed boundary-probe attempts are retained and are not claimed as successful checks.

`search/` enumerates candidates across all open campaign PRs, prepared landings and available
delivery refs. It is not an exhaustive duplication proof. `screen/` preserves both complete
outputs and the pair delta; a new in-file near-match alone is not a debt member under the ledger's
standing convention. The existing cumulative ledger is the debt baseline, not the raw screen count.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Include a verdict line with blocker/major/minor/note counts and the boundary analysis even for an
empty table. The gate closes at zero blockers and zero majors, with minors dispositioned.

**Deliver your findings as a downloadable file named `natbits-dedup-findings.md`** (the findings
table and the verdict line, no other wrapping), and also paste its content in your reply.
