# Chapter 4, phase P4.4 (logspace reductions, PATH, Immerman-Szelepcsényi) — audit loop resolutions

**Gate: CLOSED (round 1, 2026-10-08).** One round: **PASS — 0 blockers,
0 majors, 2 minors, 5 notes** (`audits/ch4-p44-findings.md`, verbatim). All 6
definitions blind-restated clean (with the received
`ImplicitlyLogspaceComputable` conjuncts spelled out exactly); all 11 sorried
statements accepted with independent derivations — the composite
output-length inequality, the exact `encodePATH` length equation
`2n² + 2n + 2|bits s| + |bits t| + 6` with full injectivity, the
inductive-counting invariant with the ascending-order/exact-count forcing
argument and a one-choice-word stream layout, the `O(S n)`-bit vertex-code
ledger for Corollary 4.21, and the bounded-carry invariant for `MULT`. The
bundle hash was independently recomputed; 15 adversarial instantiations plus
~32,000 finite checks (pair round trips, all graph encodings for `n ≤ 3`,
counting cases, multiplication triples) all passed.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | `mem_LOGSPACE_of_logspaceReducible`'s sketch no longer calls the characteristic function's length language "total": it is **exactly** `{pairEncode x [] | x}` — a regular language; index `1` and malformed strings are rejected |
| 2 | The same sketch's final step is now a fixed-index **paired-input** specialization: the index-`0` query string is `pairEncode x [] = dbl x ++ [false, true]` (the doubled word with separator, not `x` itself), decided by simulating the query machine on that doubled virtual input directly — independent of the theorem being proved, avoiding circularity |

Also applied with note 4's disposition (prose accuracy, disclosed here):
`PATH_NLComplete`'s sketch now says the P0 unique-terminal caveat is
**assigned for discharge here**, not already closed — the received `cleanTM`
is the model only (the P0 record notes it does not reset the input head), and
the normalization must park the input head and re-prove acceptance,
all-branch halting, and the space constant for the normalized machine.

Re-verification: `Reductions`, `Path`, `ImmermanSzelepcsenyi` re-elaborate
with zero errors (11 `sorry` warnings exactly across the four modules).

## Notes (dispositions recorded)

* **Note 3 (composition ledger)**: malformed-query rejection, index
  length/overflow handling before storing a value, the paired virtual-input
  layout `pairEncode (f x) (bits i)`, and the length-query boundary test —
  carried verbatim into the `comp` fill brief, with the auditor's full
  question-2 ledger.
* **Note 5 (counting verifier)**: the direction-sensitive negative test
  (`A u v = false` with `u` from the previous ball), strict ascending order,
  exact previous counts, canonical-field validation accepted on failure, and
  the stage/vertex/flag/certificate stream layout — carried verbatim into
  the fill brief.
* **Note 6 (`NL` downward closure)**: the recommended standalone contract
  `mem_NL_of_logspaceReducible` is recorded as a **future additive
  statement** (the named-fill-obligation policy needs no promotion to pass);
  its proof route (suspended simulation, ignored choice bits during
  deterministic query work, budget from the target's all-branch halting) is
  banked for the fill.
* **Note 7 ([P4.2], cross-filed)**: the P4.2 carrier-bridge distinction —
  disposition recorded in `audits/ch4-p42-resolutions.md` (that gate closed
  the same day); the P4.4 consumer builds the bounded codec and path
  lifting itself and does not treat them as exported by P4.2.
* **Auditor-supplied material banked for fill**: the exact validator
  requirements (canonical endpoint words — empty or ending in `true`), the
  `O(n⁴ log(n+2))` certificate-bit estimate, the erase-and-park alternative
  via a graph-level accepting sink (recorded as fallback only — the declared
  route stays machine-level normalization), and the suggested additive
  sanity contracts (encoding length/injectivity, `encodePATH ∈ PATH ↔
  GraphReach`, zero-product memberships, the fixed-index specialization).

## Consequences

* **The chapter-4 statement program is fully gated**: P4.1, P4.2, and P4.4
  closed; P4.3 is in its repair round (`audits/ch4-p43-findings.md` — its
  blocker concerns the P4.3-side codec statement, not this phase's surface).
* The nondeterministic-ARM extension keeps its two named customers (the
  `PATH` walk, the counting verifier) with the §12 gate; nothing here
  changes that deferral.
* Statement-freeze baseline for the closed surface: the closing commit
  (minors are sketch prose only; no declaration changed).
