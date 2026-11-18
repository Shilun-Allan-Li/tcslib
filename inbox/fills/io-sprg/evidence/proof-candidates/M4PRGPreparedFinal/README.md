# Reviewed PRG hop and hybrid packet — all candidates UNRUN

No Lean, source/import edit, Git, cache or agent was used. These are corrected
proof candidates, not kernel-checked bodies. The source files remain untouched.
Every staged body has exactly one outer tactic block, no sorry/admit placeholder,
and lines at most100 characters. Bindings and diffs retain every original string.

## Exact frozen coverage

This packet supplies candidates for SEVEN original M4 obligations:

- Params.hyb_real_eq_raw
- Params.hyb_random_eq_raw
- Params.hyb_prg_accept_eq_chain_zero
- Params.hyb_uniform_accept_eq_chain_zero
- Params.hyb_real_prg_le
- Params.hyb_uniform_random_le
- Params.prg_hop

The exact frozen TSV contains16 M4 or M4/M6 original obligations. The remaining
NINE are outside this packet: the four LPN reduction/encoding bodies, three PRG
encoding/advice-bound bodies, lemma42 and prop41. Other earlier packets may
address them, but that does not change this packet's seven-original coverage.
frozen-M4-obligation-map.tsv records all16 exact names, frozen and current anchors.

FOUR proposed theorem-only helpers support these bodies:
Params.sdCore_publicSeed; Params.prg_verdict_prob;
Params.prg_nuisance_average; Params.prg_chain_accept_average.
These are new helper declarations, not additional frozen original obligations.
Do not count the preferred typed nuisance body as a fifth helper.

## Staged files and repair scope

candidates/PRGHopFinal contains the seven original full helper/hop strings.
candidates/PRGHop contains the four old exact endpoint strings. Each has an
original/candidate hash binding and a unified diff. The repair script found17
missing typed-have assignments, including nested hpub/htail proof branches, and
inserted := ?_ plus swap. Helper04 also has explicit sample-coin predicates in
both probability bridges and its underlying uprob_comp_equiv call.

No Type* universe occurs in the new diagnostic goals. The probabilistic API is
Type0. Reader/definition-name inspection found no explicit foreign-definition
unfolding in these bodies: sampler, game, raw-bundle, activation and encoding
access is through published `_eq`/field readers. Only local c/er/ep/ix/x/sec/Q
abbreviations and proof-local finite tuples are expanded.

The old helper05's untyped reverse product/commute rewrites remain a high-risk
elaboration string, even after syntax scanning. A preferred alternative is:

  candidates/PRGHopFinal/05-prg_nuisance_average.typed.proposed.lean

It has the SAME helper header and a complete one-block candidate body. It
normalizes the actual IdDraw/Draw/uniform law into one explicitly typed finite
product, reorders its factors by a proof-local explicit permutation, invokes
existing expect_sample_equiv, splits only specified products with full function
arguments, and discards only the unused repetition coordinate with expect_const.
The original G.IdDraw coordinate is mapped through G.idCore on both sides;
there is NO sample from G.Idx and no uniform-index hypothesis. Advice is moved
through its supplied PRGAdvice.prodEquiv and public reader. The permutation is
proof-only tuple reassociation, not a new source algorithm, encoder, sampler or
probability primitive. Both original and typed variants remain UNRUN.

## Dependency order and implementation placement

1. sdCore_publicSeed belongs in Hybrids after publicSeed_eq. Correctness cannot
   own it because publicSeed is defined in Hybrids and Hybrids imports Correctness.
2. Both statistical hops use that helper. The real/prg hop also consumes the
   already-completed public G4_eval_sdCore and eval'_eq; the uniform/random hop
   uses the same literal comparison tail and needs no G4 polynomial conversion.
3. The four old endpoint bodies can be checked independently through the current
   raw/sampler/packing readers. The last two are ACCEPTANCE equalities required
   by SP-W2; never strengthen them to equality of free oracle programs.
4. prg_verdict_prob is independent of nuisance averaging. It consumes the shared
   layout-only RealizesOn readers on canonical encoded challenges and typed B
   coins, reindexes with coinsEquivPoly, and applies the existing uniform-prefix
   restriction/list-take APIs. No off-layout behavior is assumed.
5. Check nuisance_average with explicit factor types, then chain_accept_average
   with its explicit comparison-vector equivalence and the image guard.
6. prg_hop chooses the WHOLE advice family before B and its RealizesOn proof,
   and uses existing abs_expect_sub_le_expect/exists_expect_sample_le. Off-image
   advice uses the inhabited record; image cases use kappaOfN_n. This remains
   meaningful at κ=0. It constructs neither a realiser nor a machine.

The helper files carry `theorem Params.name` and assume the area namespace
outside an open Params block. If inserted INSIDE namespace Params, remove only
that redundant proposed-helper name prefix. Frozen original declarations keep
their exact full names/headers and receive body replacements only.

## Precise untested API risks

- SourceRaw field readers in the old real/random endpoints may leave beta/eta
  conversion goals after simp only. Prefer existing jlsSPRG_raw_idSamp/sdSamp and
  instance_eq readers when an opacity check requires them; do not unfold sources.
- Statistical hr/hp/he normalize a common retained RAW draw law. They never apply
  deterministic correctness to arbitrary SdCoreOut records. G4_eval_sdCore is
  the existing pointwise core fact; eval'_correct is support-level and has no
  published direct inverse-sample support eliminator in the inspected API.
- The new nuisance variant uses actual transparent finite-coordinate TYPES in
  its local aliases, as already exposed by the frozen reader signatures. If an
  owner seal requires explicit idDraw_eq/draw_eq/data_eq transport, add that
  reader transport rather than relying on a foreign value definition.
- chain_accept_average's generalize/subst image step, outputIndex/arrow-equivalence
  beta reduction and PRGAdvice product projections remain unelaborated. Its
  output reindex template is one component, not a proof of the whole statement.
- Typed public probability calls avoid the recent M3 Cardinal/defeq explosion
  from untyped finite-union lambdas. This is a preventive refinement, not a
  profiling claim about an unrun M4 body.

## Isolated search templates and evidence

overlap/probe-index.json has ELEVEN templates: four proposed helpers and seven
frozen original bodies. No StructuredSeed owner is imported. Every opening of
TCSlib.Cryptography/Games is backed by the explicit public Games.Hopping import;
no gratuitous scoped BigOperators opening is added. All goals use Type0.
The heartbeat bound is100000. Search status is PENDING_ROOT: no exact?/apply?
result, absence theorem or kernel proof is claimed here.

Scope is explicit in each row. Nuisance average has its full finite-law core;
coin prefix retains the actual pointwise shared-reader conclusion and e transport;
raw real/random retain all four exact sampling queries; the initial-chain endpoints
compare acceptance after inserting an unused uniform query. Statistical templates
are the exact reusable public agree-off-bad inequality, after the source's actual
law/reader normalization. The chain-average template isolates the explicit output
vector reindexing component; the remaining nuisance/guard obligations are mapped,
not hidden as exact self-goal assumptions. The advice-family template assumes
only the earlier real/uniform scalar-average identities and proves the absolute
section-gap selection. It contains no B-dependent advice premise.

No heavy BPPBridge, forbidden Games.Closeness, machine/sampler constructor,
CoinSampling transfer variant or alternative realization contract is introduced.
All necessary public prefix, probability, averaging and verdict APIs are already
reachable in the existing PRG owner closure. The original APIs.tsv in PRGHopFinal
remains useful; current API/hash bindings and corrections are recorded here.


## Preferred MRr3 repair for helper04

Use preferred-MRr3/04-prg_verdict_prob.proposed.lean (UNRUN) and its one-line
hash-bound diff. The coin-vector verdict now composes generic
NUPPT.distinguisherL_eq with the required
RealizesOn.runAt_coinsEquivPoly_symm, then the owned prgRed_eq reader. It retains
all actual probability reindex/prefix transport and supersedes the older helper04
only. preferred-MRr3/API-note.md records the exact API signatures/locations and
explains why no duplicate generic realizer-verdict step is added. Other proof
files remain unchanged. sdCore_publicSeed stays in Hybrids before its consumers.
