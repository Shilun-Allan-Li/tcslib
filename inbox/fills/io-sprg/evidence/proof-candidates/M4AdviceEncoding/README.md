# Six reduction encoding bodies — full candidates, UNRUN

This packet contains full replacements for exactly six frozen original proof bodies.
No Lean, build, cache, git, source edit, machine/sampler construction or agent spawn was used.
No compilation, exact?/apply?, kernel, standard-axiom or final-gate success is claimed.
All six bodies have one outer tactic block, no placeholders, balanced delimiters and
lines at most100 characters. Static checks are not elaboration checks.

| Original Params theorem | Candidate | Lines | Main public reuse |
|---|---|---:|---|
| lpnEnc_injective | 01-lpnEnc_injective.proof | 7 | LWE.encodeChallenge_injective |
| encLPNAdvice_injective | 02-encLPNAdvice_injective.proof | 39 | pair injection; M1 Basic fixed-width lists; modular vectors |
| encLPNAdvice_length_le | 03-encLPNAdvice_length_le.proof | 148 | encIdx'_length_le; public seed bound; M1 Basic exact list length |
| prgEnc_injective | 04-prgEnc_injective.proof | 6 | challengeStr reader; pair and List.ofFn injection |
| encPRGAdvice_injective | 05-encPRGAdvice_injective.proof | 21 | pair, buckets and actual modular matrix injection |
| encPRGAdvice_length_le | 06-encPRGAdvice_length_le.proof | 72 | encIdx'_length_le; public seed bound; matrix length |

frozen-six-map.tsv binds exact full names, frozen/current anchors, unchanged headers,
source hashes and candidate hashes. The current source snapshot has32 direct original
sorry bodies:8 M4,8 M4/M6,7 M5,9 M6. The six above are precisely six of the eight
M4/M6 rows; the other two are lpn_hop and prg_hop. The other two M4 security bodies
lemma42/prop41 and seven PRG/hybrid originals are covered by different packets.
This is a textual inventory, not a transitive kernel census or an audit of proof trust.

## Encoding fidelity and zero parameters

The LPN challenge proof uses EXACTLY the LWE parameters and residue width already in
lpnEnc_eq, with that same family's modulus_le_pow. No alternative challenge encoding,
coordinate equivalence, sampling law, layout or coin law is introduced.
The PRG challenge proof reads its existing canonical index/output pair unchanged.

Both advice injections split the literal existing prime-first and unary-parameter pairs.
The prime and unary word are fixed for each theorem's schedule/independent parameter;
discarding their equal left components in an injectivity proof does not remove them
from the definition or the length accounting. All data fields are then recovered.
LPN uniform vectors use the tagged BoolCircuit.encodeList, so the M1 Basic fixed-width
list theorem is required. PRG uniform vectors use the actual bare row-major matrix
encoder, for which the published modular matrix theorem is the correct API.

No positive-kappa or schedule-image premise was added. Fin(kappa+1) retains its sentinel,
and kappaOf_le/kappaOfN_le support every independent L/N, including0 and off-image inputs.
Prime parameters supply NeZero instances at each actual schedule prime. Empty vectors,
matrices and tagged lists are handled by the public APIs, including their final marker.

## Explicit finite length accounting

Set S to the six-term data sum already used by the frozen majorants. Public PolyExpr
monotonicity and the inverse-parameter readers bound every component at kappa by its
independent-parameter value. S>=L+1 or S>=N+1 implies S>=1 even at zero.
The existing encIdx'_length_le, read through its pair equation, supplies both index and
bucket bounds (and, for PRG, the hardwired matrix bound). No index sampler is constructed:
PRG uses the primitive's existing idxNonempty only in the proof to instantiate this bound.

The key saving for the repeated public vectors is the EXISTING pubLen_le_seedBound:
kappa*n(kappa) <= seedBound(kappa). Thus uniform vector data are quadratic in S,
rather than cubic before separators. The LPN code's tagged row markers are counted too.
LPN draw code is computed through encDraw_eq and encOneDraw_eq and M1 Basic's exact
fixed-width list length; its coarse bound is32*S^3. Literal seven pair separators,
prime kappa+2 bits, unary L, hop kappa+1 bits, index, buckets, draw, tail and uniform
rows fit128*S^3. The frozen4096*(L+1)*S^3 then follows by natural-number inequalities.
PRG's prime/unary/bucket/matrix/uniform layout fits100*S^3 and hence the frozen bound.
These are finite arithmetic calculations, with no new asymptotic or monic absorption proof.

Narrow overlap disclosure: the constant width of one construction-specific draw is also
calculated locally inside the completed Encoding.encDraw_injective proof. No public
encDraw length theorem was found by the recorded bounded name/shape searches. This packet
reuses both public Basic list lemmas, all encoder readers and public modular lengths;
it adds no generic fixed-width-list, prefix-free or length theorem. The remaining local
width arithmetic is reader composition for this same concrete layout. A later extraction
of that existing local calculation would need an owned helper and its normal inventory
coverage; it is not silently proposed or treated as already approved here. In particular,
the separate raw LPN family's variable Nat.bits selector code is not changed or unfolded.

## Public-only overlap templates and searches

overlap/probe-index.json lists six original expanded cores and two explicit M1 Basic
reuse controls; all exact/apply statuses are NOT_RUN. Root may replace the single
__PROBE_BODY__ placeholder in a fresh file with its recorded search command. No template
imports either reduction owner or assumes the desired whole conclusion as a premise.

Core01 is the exact public canonical LWE injection interface. Cores02/05 expand advice
records to Type0 finite products and their literal pair/list/matrix encoders. Core04
expands the canonical Boolean challenge pair. Cores03/06 expand the concrete byte counts
and assume only the published component-size inequalities used by the actual bodies;
they do not assume a final advice bound or an injectivity conclusion. These numerical
cores isolate final accounting and omit PolyExpr transport, which the actual bodies
supply via public eval_mono. Core03 includes every draw/tag/pair field in its code.

The two reuse controls deliberately import the already completed Basic helper module,
whose static import closure does not contain either reduction owner. They therefore
allow the required area-helper exact hits without exposing an owned target self hit.
All five TCSlib probe import roots are already in the current reduction import closure;
no source header/root change is proposed. Lean.Elab.Tactic.LibrarySearch is probe
harness only. Minimal openings name Turing and TCSlib.Cryptography, both present under
their listed imports. No absent area namespace is opened in a minimal Mathlib-only goal.

static-search-index.json records five bounded rg name/shape searches, exact arguments,
exit statuses, missing trial paths, raw output and hashes. All returned text hits.
An initial guessed LPN/Basic path was explicitly recorded as absent and excluded from
that command; StructuredSeed/LPN is the actual source used. There is no theorem-absence
claim from an invalid command, no-hit, timeout or any unrun diagnostic.
APIs.tsv has41 exact declaration anchors. The public names and parameter shapes were
checked by text; elaboration-sensitive defeq/implicit synthesis remains UNRUN.

Preparation corrections retained in metadata: the source inventory parser initially
needed section scopes to avoid omitting unrelated Buckets declarations; it now binds
all146 frozen names. A missing closing parenthesis in the draft core02 template was
repaired before any probe. Neither discarded draft supports a search-result claim.

## Implementation order and remaining risks

Recommended pretest order:01,04,05,02,06,03. Pin implicit q/vector length if elaboration
needs help;02 already supplies both explicitly at its fixed-width-list reuse point.
The length proofs use local let expansions only, public foreign readers and fields,
and explicit multiplication inequalities before omega. Every typed have, including
bullet-prefixed cases, was scanned for := assignments. No untyped probability API is
introduced by this packet; hop transport/coins remain the separate hop proof task.

The source remains unchanged. Correctness of the frozen six statements was not found
to require a repair: the generous constants account for all prefixes and zero cases.
This is mathematical/source review, not a kernel verdict on these candidate scripts.

## Required modular placement

line-budget.json gives exact known text assembly estimates before new wrappers/docs.
LPN would reach1090 lines from current428 plus these bodies and LPNHopFinal01–10.
Use the already staged LPNModularity four-child Defs/Encoding/Transport/Hop plan BEFORE
implementation, preserving frozen names/headers/docs and the import-only facade.
The old split note's description of two partial advice bodies is superseded by the
three full bodies here; it does not mean the old partial candidates are preferred.
PRG's analogous known assembly is721 lines including four proposed helpers. Root chose
a proactive three-child Defs/Encoding/Hop split; the read-only move ledger is at
/private/tmp/io-sprg-proof-notes/PRGModularity/existing-declaration-move-map.json. The split must introduce no external import roots or renamed aliases.
