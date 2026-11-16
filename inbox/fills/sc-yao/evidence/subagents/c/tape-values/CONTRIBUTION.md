# Subagent c: actual tape/value-table bijection

Source `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/TapeValues.lean`. Namespace `...YaoHybridProof.TapeValues`.
464 lines,width<=97,23 public declarations,57 stored constants including
private helpers/generated auxiliaries; no sorry/new simp attributes.

## Contract and concrete sampler identification

equiv maps every Fin(10*S*n+2*S) tape bijectively to Rest × actual raw data.
Raw data is written structurally as the key table and actual-assignment nonce
pairs, K=Fin n→Bool. No duplicate Index/Data type or SelectedSeed import.
Rest retains ALL shift bits, unused key blocks and unused row blocks.

The image/complement splits use Mathlib piEquivPiSubtypeProd/ofInjective,
currying and existing product rearrangements. CoinRelabel.blocksEquiv gives
the complete padded tape layout. keyEmbedding uses castLE of real vertices;
rowEmbedding uses actual gates and CoinSeedRelabel.assignmentEmbedding.
Nonce halves use Fin.appendEquiv/finCongr, with no positive-width premise.

Exact getD readers expose extracted keys, both nonce halves, every shift and
every unused key/row block. Numeric range-complement contracts cover vertices
>=C.size, gates>=gatecount and row codes>=2^arity (codes1/2/3 for arity0,
2/3 for arity1). All unused shift positions, including unused gates, remain
in Rest.

permutation is XOR of retained argument-shift bits. seed_perm proves the
actual seed permutation equals it from the caller's addressed shift reader.
seed_eq identifies the entire caller seed with its extracted actual tables
and permutation(Rest), using four addressed readers. seed_on_inverse proves
seed(ofFn(equiv.symm(p,d)))=(d.keys,d.nonces,permutation p). No actual
protocol sampler or seed definition is copied or introduced.

The retained parameter is NOT a uniformly sampled whole permutation family.
The actual XOR-shift distribution is retained exactly in its shift bits.
b composes SeedCoordinates.paramEquiv/dataEquiv outside this module, and
root owns SelectedLaw to invoke the existing coordinate-fill/acceptance law.
No probability law is re-proved here.

## Reuse and overlap

Published CoinRelabel blocks/getD readers and CoinSeedRelabel assignment-code
embedding/injectivity/bounds are consumed directly. Private splitEmbedding
only composes existing Mathlib image/subtype function equivalences; its
readers and key/row adapters are equations of those compositions. No generic
probability/list/finite-sum machinery is copied.

SY5 nearest unmerged relatives remain sc-garble a73072f1
Garbling/CoinBlocks.lean:83 key_row_blocks_injective and:162
pushesUniform_key_row_blocks (also:51 pushesUniform_bits_of_blocks). Those
give restricted coordinate marginals; the present construction is a full
bijection retaining shift/padding parameters and exact actual seed identity.
No probability proof from that source is imported or re-derived. The
assignmentFold_small overlap was already disclosed in CoinSeedRelabel; it
is reused through that public embedding rather than reproved here. The
consulted CoinBlocks source is retained in the earlier c/relabel evidence.

## Verification

Final normal18 PASS; style-lint-18 reports0findings. APIs-02 verifies finite
and nonempty Rest inference in classical context plus n=0 inverse and shift
interfaces. All four whole-file seals A/B by strict/coe PASS with
-DmaxErrors=0. Axioms-01 enumerates all57 stored constants, standard
axioms only and every transitive closure sorried=[]. Both error forms counted.
All earlier failed probes/raw source versions/logs are retained.

Normal14 source+matching olean API snapshot was frozen separately for
downstream coordination; no existing signature changed afterward. Seal
tools are the provenance-recorded c/sampler-endpoints tools with path changes.
Root reruns final merged checks. No frozen-file edits or child commits.
