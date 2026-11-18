# LPN reduction M4 preparation — NOT RUN

Read-only source/API/mathematical audit. No Lean/lake/build/cache, source edit,
git mutation, new import, machine or fair-coin sampler construction. Exact
source hashes are in source-binding.json. No false existing LPN reduction,
encoding injectivity, or advice-size assertion was found.

Four replacement bodies are staged for the four existing nonreader theorems:

| File | Status and genuine remaining obligations |
|---|---|
| 01-lpnEnc_injective.lean.txt | no explicit placeholder; NOT_RUN; direct canonical LWE encoder theorem |
| 02-encLPNAdvice_injective.PARTIAL.lean.txt | one explicit fixed-width uniform-row list recovery gap |
| 03-encLPNAdvice_length_le.PARTIAL.lean.txt | one explicit exact-layout accounting gap; final majorant arithmetic drafted |
| 04-lpn_hop.PARTIAL.lean.txt | two specialized actual-law averaging / realiser coin-law gaps |

Each file contains exactly one tactic block and has width<=92. None is kernel
checked; root exact?/apply?/simp?/elaboration/seal probes remain pending. Keep
all existing theorem docstrings and proof sketches when inserting candidates.
The placeholders are deliberate, named dependencies, not hidden assumed facts.

## Mathematical and zero-case audit

- LPNChal/lpnEnc are EXACTLY the assumption's canonical LWE matrix/value type
  and LWE.encodeChallenge with the family's own width. Candidate1 does not
  introduce a stand-in encoding or prove a duplicate injectivity lemma.
- L=0 and kappa=0 do not empty advice: hop is Fin1, not Fin0; G indices are
  nonempty; bucket count and noise denominator are positive; function spaces
  into ZMod/Fin B are inhabited, including empty domains. The requested hop
  inequality is guarded by hop.val<kappa, so no hop at kappa=0 is demanded.
- kappaOf_ell makes the polynomial schedule injective on its image. Advice
  selected per independent L therefore cannot receive incompatible demands
  from two distinct kappa values. Off-image preprocessing is the empty word.
- The challenge matrix is NOT an advice field. It is the public matrix used
  in the challenged vector AND EVERY later real vector, as required by the
  shared-matrix LPN chain. Earlier public vectors remain the advice uniforms.
- Canonical real b is A*s+e; lpnPre adds the fixed Boolean sigma exactly once.
  Canonical uniform b plus sigma is still uniform, conditionally on sigma,
  even if the hardwired tail depends on that sigma. No unconditional
  independence shortcut is needed or valid for the correlated tail.
- Full draw advice contains secret/noise coordinates for the challenged hop,
  but lpnPre ignores those coordinates there. Keeping unused finite data is
  harmless; no false free-oracle equality is used to erase its sampling.
- Width kappa+1 encodes the sentinel hop value<=kappa faithfully. The prime's
  upper-width field makes modular vector blocks injective, including p=2.
- The generous4096 advice bound remains sufficient; a coarser128*S^3 estimate
  already fits it. No constant or statement correction is proposed.

## Canonical challenge injection

Read lpnEnc_eq, then apply LWE.encodeChallenge_injective at
(P.lpnFamily_raw pi).toLWE.parameters L with its OWN modulus_le_pow field.
This is precisely the public theorem's hypothesis. Do not substitute width
kappa+1 here: the assumption encoder's width is the family's L+1 expression,
and the whole point is to preserve that canonical input language unchanged.
No computation of a prime or fresh sampler is involved.

## Advice injection: recover the actual six fields

The candidate splits the seven nested pair encodings through
Turing.pairEncode_injective. Prime/unary-L prefixes are the same at fixed L;
they do not hide any varying advice field. Recover:

1. hop: apply NumberTheory.listToNat to the fixed-width numeral equality,
   then Candidates.listToNat_natToList using each hop's Fin bound and the
   existing natural inequality n<2^n. Use Fin.ext for the resulting values.
2. I: use G.encIdx_injective, never uniformity of G.Idx.
3. buckets: use Params.encBuckets_injective.
4. draw: use Params.encDraw_injective, retaining all sigma/secret/noise data.
5. tail: use List.ofFn_injective.
6. uniform: each row has EXACTLY n*(kappa+1) bits, by encodeVector_length.
   Peel encodeList_cons and its one-bit tag. List.append_inj at that known
   length separates equal row codes from equal remainders. Apply
   encodeVector_injective with the prime width, iterate over the fixed row
   count, and finish with List.ofFn_injective.

The last row-list argument is the one explicit candidate gap. It is important
that row lengths are fixed: BoolCircuit.encodeList is tag/concatenation code,
NOT the cryptographic nested-pair list encoding. Generic injectivity of f
ALONE would not make encodeList f injective for variable-length f. The public
LamportReduction.encodeList_injective concerns a DIFFERENT encoding and
MUST NOT be applied here. Fixed-width row code makes our statement sound,
including zero columns or zero rows.

Finish with the existing lpnAdviceProductEquiv.injective and its apply reader,
using nested Prod.ext on the six recovered fields. No choice-based finite
enumeration or decoder algorithm is needed.

## Exact advice layout and the numerical bound

Let k=kappaOf L, ell=P.ell k, n=P.n k, m=P.m k, and p=pi(k). Let Ilen be the
actual G index-code length and Bcode the actual encoded bucket-map length.
All field code lengths below are value-independent except Ilen/Bcode, which
are already controlled by the owner index bound.

The exact raw-draw formulas, using the published code readers, are:

- Noise-pair block: 2*ell+k+5 bits.
- One repetition: OneLen=2*ell*(k+1)+n*(2*ell+k+6)+3.
- Full Draw: DrawLen=2*n+3+k*(OneLen+1).
- Uniform-vector row list: Ulen=k*(n*(k+1)+1)+1.
- Complete advice:
    AdviceLen=4*k+2*L+20+2*Ilen+2*Bcode+2*DrawLen+2*m+Ulen.

The pair formula is EXACTLY 2*leftLength+2+rightLength. These formulas count
all true tags and final false markers in BoolCircuit.encodeList, not just
vector payloads. The full advice has eight components and seven pair nodes.

Let S be exactly idxBound(L)+(seedBound(L)+(mBound(L)+(nBound(L)+
(ellBound(L)+(L+1))))). Then S>=1 and k,ell,n,m<=S using kappaOf_le,
owner ell/n/m bounds and PolyExpr.eval_mono. The index's existing length
bound, applied to the concrete index (w.I,w.buckets,zeroMatrix), gives
2*Ilen+2*Bcode<=idxBound(k)<=S; its matrix-length term is nonnegative.
Thus no new independent G index/bucket asymptotic bound is required.

Crude pointwise estimates suffice:

- OneLen<=16*S^2;
- DrawLen<=22*S^3;
- Ulen<=4*S^3;
- 4*k+2*L+20<=26*S^3;
- 2*Ilen+2*Bcode<=S^3, and2*m<=2*S^3.

Consequently AdviceLen<=77*S^3<=128*S^3. Candidate3 leaves this layout
accounting as one explicit obligation, then converts128*S^3 to the EXISTING
4096*(L+1)*S^3 by public polynomial readers and natural arithmetic.
This argument does not need to unfold seedBound/sVarBound or estimate delta.

Reused length APIs: Turing.length_pairEncode,
Encoding.Modular.encodeVector_length, Candidates.length_natToList,
List.length_ofFn, BoolCircuit.encodeList_nil/cons; then the owner numeric
bounds. Derive the exact SPECIFIC full-code formula, not a replacement
generic encodeList upper-bound theorem. Searches found the public generic
length_encodeList_le' in BoolCircuit.AdjWalk, but that heavy module is not in
the current closure and no new import is authorized here. Its generic
inequality is not silently rederived: any new helper must be an exact
specialized layout equality with its reuse search disclosed, or root should
leave the accounting gap open until an existing suitable API is selected.

## LPN hop: actual nuisance law and correlated advice

The local gap in candidate4 is LWE.decisionAdvantage on the EXACT canonical
parameters/noise, with a deterministic distinguisher using lpnPre and A's
SHORT coins. It is proof-only analysis, not a new assumption, reduction,
machine, or sampler. It makes the final realiser identity precise.

M4-LPN-AVG must average the ACTUAL finite nuisance draw:

- the primitive's G.IdDraw seed, mapped by G.idCore to I;
- the independently uniform bucket placement;
- the complete source Draw (sigma plus every secret/noise seed);
- the uniform public vectors and uniform Boolean comparison tail.

It must NOT average uniformly over all LPNAdvice records: I may be nonuniform,
and when tails(k)=true, the advice tail is exactly G.eval(n,I,sigma). Fix
hop=hops(k), retain the actual I and source draw, and set tail to that G
output or the sampled comparison vector as the selector requests. The
challenge matrix is excluded from the nuisance/advice data.

For each fixed nuisance tuple, a REAL canonical LPN challenge supplies fresh
secret/noise to the selected hop. Reindex its finite seeds so that these are
exactly that hop's original secret/noise law; the old stored coordinates are
unused. All later vectors reuse the challenged matrix. A UNIFORM canonical
challenge supplies uniform b; adding sigma yields the next chain, by the
EXISTING HardcoreBit.pushesUniform_add_right on the finite additive group of
residue vectors and its .uprob_eq reader, conditionally on the fixed sigma.

Transport canonical dimensions/residues/noise through lpnChalEquiv_eq,
lpnMatrixAt_eq/lpnValuesAt_eq, kappaOf_ell, n_eq, W_eq_noiseDenAt, the raw LPN
parameter/noise readers and LWE.sample_fst/sample_snd/noisyValues_apply.
The challenge equivalence alone is a TYPE equivalence; a specialized
sample-law compatibility proof is still required. Do not infer preservation
of noisyValues merely from having an arbitrary equivalence of the types.
All transports are explicit finCongr/Equiv.cast, no chosen encodings.

Reorder/average the fixed-section acceptances with the existing product and
expectation laws. Apply ProbComp.abs_expect_sub_le_expect followed by
LamportReduction.exists_expect_sample_le on the uniform nuisance seed type.
Select the resulting advice. This fixes a signed absolute gap dominating the
requested hop without an orientation bit or factor2. Off image, or at a
sentinel hop not below kappa, choose any member of the already nonempty
advice type. Classical choice is in the theorem proof only.

The entire advice family is chosen BEFORE B is introduced. It may depend on
P,pi,A,tails,hops, but not on which B realizes it. The candidate's hfixed
implication records this image/valid-hop condition, and the final step uses
kappaOf_ell to recover the requested kappa. No incompatible choices across
kappa arise, since ell(kappa) is injective by that inverse identity.

## Exact realiser verdict and coin-prefix route

M4-LPN-COINS is valid for every advice family, on/off image, and uses the
following exact existing APIs (all already in the LPN import closure):

- LPNFamily.Raw.adv_eq -> LWE.Family.advantageAt_eq ->
  LWE.decisionAdvantage_eq -> Foundations distAdv_def/acceptProb_def.
- Read the canonical encoder through lpnEnc_eq.
- Shared RealizesOn.distinguisherL_eq, RealizesOn.coins_eq, and
  NUPPT.coinsEquivPoly/coinsEquivPoly_symm_ofFn transport B's actual coin type.
  The alternative shared runAt_coinsEquivPoly_symm reader is also sufficient.
- Read lpnRed_eq. Derive short<=long from kappaOf_le, NUPPT.coinLen_eq,
  PolyExpr.eval_mono/eval_subst/eval_var.
- Reuse HardcoreBit.pushesUniform_restrict with Fin.castLE_injective, then
  its .uprob_eq reader, and OneWay.ofFn_castLE_eq_take. These are the same
  lightweight prefix APIs documented in ../PRGHop/prefix-reuse-excerpt.lean.txt,
  replacing kappaOfN by kappaOf and prgPre by lpnPre.
- Bridge.prob_sample_eq_uprob or existing product uprob readers connect the
  exact canonical acceptance experiment to these prefix probabilities.

This uses only encoded canonical challenges and layout-length words. There
is no assumption about B on other inputs or other coin lengths. Both fixed
section acceptance probabilities agree with B's canonical experiment, so
their absolute gap equals the raw LPN family advantage. No RealizesOn body,
new realization predicate, randProb bridge, BPPBridge import or generic
probability lemma is needed.

## Reuse searches and pending work

Text searches covered canonical LWE encoding/experiment APIs, pair/numeral
round trips, list/vector encoding injection and lengths, the owner's index
bounds, finite averaging, public translation/restriction uniformity, and
shared realiser readers. Exact API locations are in APIs.tsv. The private
list bound in BoolCircuit.Uniform was not adopted, and the unrelated Lamport
nested-pair list injection was explicitly rejected for this code format.

The four explicit gaps above are specialized implementation proof obligations;
no new generic helper is proposed. Root must run exact?/apply? before adding
any helper and record actual results. Existing owner bodies should be probed
before their theorem is available, avoiding a spurious solution through its
own imported sorry theorem. No tactic result or kernel validation is claimed.
