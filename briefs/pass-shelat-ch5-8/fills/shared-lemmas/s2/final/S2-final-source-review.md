# S2 FINAL: independent source/freeze review

Reviewer: `/root/s2_route_review`, 2026-11-07. Internal review only.

**Verdict: 0 blockers, 0 majors, 3 minors.** No new proof, public-freeze,
admission, or H15 edge-case defect was found. The source/freeze review is
acceptable after the three documented minor landing corrections below. This is
not a native replay, a seal result, an external gate closure, final acceptance,
or merge clearance.

Reviewed the issued brief, checkpoint-4 review/feedback, verbatim FINAL REPORT,
all four patches and five source files, and relevant supporting evidence as
data. No delivered program, probe or driver was executed.

## Exact payload and reproduction

- Assigned exchange payload: `7a2e14829e0f2c43aae20b249f90e838822a7dc1`.
- Source ancestor: `31348fcf7dee32f84db1fc8f929d80653137995e`.
- REPORT SHA256: `0ba3e76869da060f190a48de04ce3efbd34c44a58909ef08e0b5ea3bbec32f47`.
- Archive SHA256: `f0cd4239b8ac1fac0f1f0d74fe9d7566217692f58fc5f8df84466a5888813109`.

Independently checked all 101 ordinary archived files against manifest byte
counts, SHA256 fingerprints and Git blob hashes. A read-only archive of the
exact local exchange commit reproduces that payload subtree byte-for-byte.
All four unified patches were applied in memory to the five exact ancestor
blobs, including checking their old/new Git blob prefixes and every hunk's
context/count. The result reproduces all five delivered source files exactly.
Changed paths are precisely the five owned files.

Full worker source identities recovered from the format-patch `From` lines:

| Patch | Reported source commit |
| --- | --- |
| 1 / milestone 2 | `144c99ea798e9d22d591e993dd749ac417075923` |
| 2 / milestone 3 | `5a6f802114dc5a44f9e515b73c06d5e3e0d80dca` |
| 3 / milestone 4 | `538b932d7f66c494ff3e9116a9541a4d617c02cc` |
| 4 / final | `125a29633892daebde9fbad46a131d5b66febbb7` |

These are patch metadata, not independently materialized/authenticated worker
source Git commits. The delivery exchange commit and its committed bytes were
independently checked.

## Freeze, admissions and final delta

The source comparison found no public addition/removal, header/hypothesis/
visibility change, or public non-theorem body change: 449 named public
declarations were compared, with seven anonymous instance blocks checked
separately. H15's public header is unchanged. No public API was added to rescue
the route.

The owned admission census is 1 to 0, solely H15's `sorry`. Replacing only these
five ancestor files gives the whole-library census 511 to 510, with `admit = 0`,
`axiom = 0`, and the one pre-existing outside-owned `sorryAx` token unchanged.
These are independent lexical source counts, not an axiom walk.

The private declaration census confirms 64 loop declarations retired
(DiscreteLog 15, ElGamal 15, RSA 18, Rabin 16), and 23 added private declarations
(Concrete 15, DiscreteLog 3, ElGamal 2, RSA 3). The harvest is disclosed and paid
back by removing all four copies. Final line counts are Concrete 935,
DiscreteLog 1194, ElGamal 2134, RSA 2417, Rabin 3553, agreeing with the worker's
table and the issued size exception.

Relative to checkpoint 4, four source files are byte-identical. Only RSA's
private `rsa_unitAcc_poly` docstring changes; all five files have identical Lean
code tokens to checkpoint 4. Patch 4 adds the missing proof sketch. It does not
resolve any of checkpoint 4's three review minors.

## Three minor landing corrections

1. **CP4-m1 remains: DiscreteLog sketch width, delivered source 678.**
   Replace `The output is the last |t| bits of` with
   `The output is the last |p| bits of`. The code at 698-703 correctly drops
   the payload-tail length from the zero-prefix/tail concatenation, retaining
   width `|p|`; this is a prose correction only.
2. **CP4-m2 remains: Concrete module status, delivered source 85.**
   Replace `is polynomial-time (host H15; statement only, its proof is an open fill).`
   with `is polynomial-time (host H15, via the repetition host).`
   Proof completion in the delivered source is distinct from maintainer
   verification and landing; the module prose need not claim either.
3. **CP4-m3 remains in the verbatim REPORT, lines 17-22: abbreviated identities.**
   Preserve the archived REPORT. Resolve this reporting minor in a companion
   maintainer identity record using the full source identities above, labelled
   with their patch-metadata provenance, and the following exchange identities
   independently expanded from local exchange Git objects:

| Identity | Full exchange commit |
| --- | --- |
| checkpoint 2 | `ae2be1b7ab37baf0ae08159fd0f7c86e3d0f2577` |
| checkpoint 3 | `6fc5aca0d6bbda7541a28763ed683141adc4e62c` |
| checkpoint 4 | `9b27244a5f583cde43040bfe6560cab7faf14436` |
| worker-reported exchange read | `d14a685250097d379744c4ecdf0e2b9bd083fc8d` |
| issued-pack staging | `d38aea9614bf072264e954a89e7078e7dd7dc24b` |
| FINAL payload | `7a2e14829e0f2c43aae20b249f90e838822a7dc1` |

Object resolution identifies the commits; it does not independently prove that
the worker actually read the exchange revision it reports.

## H15 route and total-input cases

The implementation uses the registered repetition host
`polyTimeComputable_iterateFind` with `R = var` and orbit bound `2n + 4`.
It carries the header `<<bw, kw>, par>` plus a counter and remaining coins.
After `i` steps the counter is `tw.drop i` and the coins are
`c.drop (i * |bw|)`. Acceptance is gated by `i < |tw|`, then uses the supplied
polynomial-time test on `<par, coins.take |kw|>`. The proof truncates the larger
orbit search with `IterateFind.find?_range_and_lt`, reads the frozen sampler
through `rejectBlocksL_eq_find?`, and obtains the unconditional tail bound from
`List.length_take_le`. The repetition result is handled by `split`, without
explicitly unfolding its generated matcher.

- `T = 0`: the counter gate prevents acceptance even if the numeric test is true.
- `k = 0`: the trial word is empty; successful `[true]` has an empty tail, which
  reads as zero and satisfies the zero bound.
- `B = 0`: coins stay fixed while the counter decreases; repeated trials match
  the total sampler's definition.
- `k > B`: successive takes overlap exactly as `drop (i*B)` followed by `take k`.
- Short/empty coins remain truncated words; there is no full-coin-length
  premise and later empty trials may test the value zero.
- The contents of `kw`, `bw` and `tw` are arbitrary. Their lengths, not their
  binary values, determine the width/block/trial counts.

The concrete witness uses `true :: trial`, but the consumers use only the
public nonempty marker, tail value and tail-length clauses. DiscreteLog and
ElGamal read zero from the empty failure tail. RSA retains its remainder
normalization and fallback `1 % N`, including the total `N = 0` case. No new
positivity, `k <= B`, exact-width, marker-head, or arithmetic-efficiency premise
was found. Efficiency of the numeric test still comes from `hacc` and `hspec`.

## Disclosed private Rabin behavior

The changed private `rabin_spOut` now always returns the `|U|`-bit numeral of
the selected value or fallback. It agrees with the old implementation when
`|ds| <= |U|`; on an overlong failed-sampling fallback it can differ. For
example, `U = []`, `ds = [true]` has zero trials: the old padding retains the
one-bit fallback, while the new zero-width numeral is empty.

This is within the brief's private-adapter allowance and disclosed at REPORT
138-154. The polynomial-time adapters now thread the numeric test
specification and fallback-width bound. Actual odd/Blum callers use words of
at most three bits, while `|U| = max n 3`; H15's tail bound supplies the success
padding condition. No public definition, hypothesis or actual-generator
behavior changes. No additional source issue was found here.

## Limits and landing use

No Lean, cache, build, worker program, probe or driver was run. No Git mutation
or library edit occurred; read-only Git object access supplied the ancestor and
exchange data. The JSON companion retains detailed hashes, declaration lists,
censuses and source-review findings. This is source analysis, not Lean AST or
kernel verification.

The FINAL report's native Checks, axiom comparisons, seals/controls and lints
were read as worker evidence. In particular it discloses reusing Gate08's base
Checks log and elaborating ancestor seal copies against current imported
owned-module objects. This review does not upgrade those claims to independent
replay results. No new missing-API or unproved-route premise was identified
from source; elaboration and imported proof dependencies remain for root's
verification workflow.

Apply the two source-prose fixes in the landing change, separately from the
immutable archive, and record full identities/provenance in a companion record.
Retain the harvest/payback and private-adapter disclosure. Root coordinates
the remaining verification and user-approved PR. HashAndSign work stayed
paused during this priority review.
