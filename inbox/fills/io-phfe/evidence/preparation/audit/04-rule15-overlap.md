# Rule15 fields, uniformity and overlap/reuse

This is a static review of M0 interfaces and explicit proof sketches. Exact?/apply? probes,
Rule10 seals, StmtDump and a stored-constant axiom census are ROOT-ONLY and remain pending.
The companion source-header inventory is not a substitute for those checks.

## Efficiency is carried by interfaces

| Interface / target | Required fields / quantifiers | Static result |
|---|---|---|
| FEScheme extends Raw | pubGen_eff,setup_eff,enc_eff,keyGen_eff are shared SamplesEfficiently; dec_eff is ∃one PC string map before κ,pp,key,x,ct. | Fields present; no bare nonuniform machine existence. Approved extra pubGen field covers uniform nonidentity g after existing uniform description generation. |
| Simulator extends Raw | setup_eff,enc_eff,key_eff. Exact draw equivalence, encodings, public parameter words and cores are parameters of shared contract. | Fields present. Committed Enc receives Ω; key input includes Ω and index. Whole state and functions/values are encoded. |
| SASimulator extends Raw | setup_eff,enc_eff,key_eff independently, stateful cores. | Fields present. Enc receives x; Key receives x,f,µ. No assumption that converting a raw SA simulator automatically proves an unpublished PC closure. |
| PartialGarbling extends Raw | lgen_eff,rec_eff: ∃one PC map before κ AND arbitrary positive p and f,x. | Fields present. paramWord includes actual modulus, dimensions and encoded f. mBound is a structural polynomial size bound, not an algorithm-efficiency hypothesis. |
| SchemeTargets | Five literal propositions matching efficient field types. | Named Phase B targets, not admitted theorems asserting efficient machines exist. |
| SimTargets | Six literal propositions: committed3 plus SA3. | Both simulator interfaces receive separate proofs in pure assembly. |
| PGTargets | lgen_eff,rec_eff matching raw layered family. | Targets state arbitrary positive modulus uniformity; no local prime schedule evaluation. |
| LinearEfficient | ∃one FinTM,∃one q,∀numericℓ,n,d,κ,pp,typedpk,x,y,complete draw, 0<ℓ+n→time≤(ℓ+n)qκ. | Nonvacuous positive-size target, stronger than source circuit/support formulation. Do not remove guard while retaining literal zero RHS. Zero-size raw algorithms remain total. |
| MddhPreTargets | ∀p,hp,d,rows,D, ∃one PC preprocessor,∀κ,advice,DLINchallenge, specified encoded output. | Witness precedes κ and every input pair; dimensions are numeric advice headers and modulus is read from pp. p only indexes known scalar advice. |
| Targets / Assembly | Fields scheme,simulators,garbling,linear,mddh; pure constructors with toRaw readers. | Efficient scheme/simulators/PG are assembled only with matching proof arguments. Raw constructors elsewhere are permitted and carry no efficiency claim. |
| Reduction realizability | Shared RealizesOn; L1 MDDHRealizable; L2 Wee20RealizableSA/43. | L2 existence only for actual machine-derived adversaries; not an honest efficiency field and not asserted for every typed SAAdv. |

Shared SamplesEfficiently is MUST-REUSED from CoinSampling.Contract. It includes one explicit
UniformSampler with exact draw-type equivalence, failure≤2^(−κ), and a uniform PC core. No
product UniformSampler, sampler implementation, PolyHandler or oracle-machine builder is
introduced. Pure PG matrix/garbling formulas do not add another contract variant.

## Uniformity and actual input layout

| Item | Audited information flow |
|---|---|
| Honest operations | PublicParams stores actual description and nonidentity generator. classParam is pp.orderParam. Setup/Enc/KeyGen/Dec contain no p(κ) function. BilinearGen.Ops provides the uniform public group operations. |
| Class/PG codecs | Wire input words reduce integer blocks modulo actual p. Canonical encode/decode round trips require p≤2^w. PG canonical f descriptions instead use Nat.size p, so its uniform interface covers every positive modulus. |
| Draws | Finite exact draws are single complete types, including dependent enc/key draws. Existing product Fintype is used for a product TYPE; no product sampler is constructed. Dependent Sigma key packs are data, not sampled types. |
| Reduction advice | All scalars lie in ZMod(pκ). hp transports known scalar advice through the published public-order equality and Mathlib ringEquivCongr. No algorithm recovers a field scalar from a source or target group element. |
| Dimensions | L1 headers contain κ,d,rows; L2 Pi headers contain κ,ℓ,n',zDim,q,mBound; outer headers contain κ,n1,n2 plus the Pi header. A uniform map can read numbers, without hardwired PolyExpr evaluators. |
| Machine coins | RealizesOn enforces D.coins=the stated layout and only encoded typed challenges with r.length=layout.evalκ. Reductions output singleton verdict words. dlinToMddh passes r.take(D.coinLenκ) to D.runAtL. |

## Overlap and nearest public APIs

| New declaration family | MUST-REUSE / nearest public result | New content / disclosed overlap |
|---|---|---|
| Exponents group actions and transport | Pairing/Group pow_val_add:254,pow_val_neg:260,pow_val_mul and GT version; Mathlib finite products, Matrix.mulVec/vecMul, kroneckerMap. | Source-specific vector/matrix/pairing wrappers. **Disclosed near-copy**: pow_val_add_GT/pow_val_neg_GT mirror source-group Group proofs because published GT addition/negation laws were absent. They must reuse generic pow/card laws, not silently re-prove a public GT lemma. |
| PublicParams/order schedule | BilinearGen.inst_eq, BilinearGroup.order_prime; Mathlib ZMod.ringEquivCongr and ringEquivCongr_val at Basic:459. | Shared Parameters helpers centralize order equality; no per-layer cast/prime lemma copies. Generator coins are NOT stored in assumption challenge encodings, so duplicate description coin strings are faithful. |
| DLIN/matrix comparison | Canonical tuple from JLS; ordinary union/event bounds, shared advantage API. | New assumption/game definitions, plus explicit zero-coordinate discrepancy. No import/copy of frozen Pairing.Assumptions. |
| MDDH column reduction | Games.Hybrid/advantage API; Lamport/Averaging.exists_expect_sample_le:114; Probability.abs_expect_sub_le_expect:409. | One chosen nonuniform column index family and one realiser, multiplied by dκ. Does not sum an unbounded family of unrelated negligible advantages. |
| Advice encodings/width | Encoding.Modular.encodeVector/encodeMatrix and their readers/injection; pairEncode length/injection; BB1Machine/Draws.order_le_two_pow:156. | Explicit metadata/vector wrappers only. **Disclosed dependency**: Pairing→IBE Draws solely to reuse order width. No decoder/draw/Words implementation copied. Request promotion of the existing width lemma after scope opens. |
| Realization links | Asymptotic/Realization realizesOn_iff:103, verdict readers:132, congr:157, exists_realizesOn_of_preTarget_id:233–250. | No local RealizesOn, variant or stronger all-string predicate. Targets link is a direct application of the shared theorem. |
| Generic/typed adversary runs | Games/Machines Move:70,buildComp:112 and published readers/cost bound; FE.Run runDet and simulate_buildComp_detImpl_eq_pure. | One deterministic interpreter defined at FE.Run and reused at both layers. No second runDet in Linear/Quadratic. |
| Fresh/padded adaptive laws | Games/Tapes freshImpl:125,tapeImpl:167,expect_simulate_tapeImpl:209,state abstraction; Games/Relational expect_simulate_rel:85,prob_simulate_rel:111. | New source-specific couplings and coordinate restrictions. Do not re-prove generic tape or oracle-simulation machinery. Endpoint equalities compare actual fresh raw laws with padded laws. |
| Class finite coordinates | Mathlib Fin.snoc/init; Algebra/BigOperators/Fin finFunctionFinEquiv:555/reader585 and finSigmaFinEquiv:656/reader667; finProdFinEquiv/finSumFinEquiv. | Canonical coefficient/tuple/prefix wrappers, not alternate finite bijections or cardinality-choice encodings. |
| Class modular decoding | Encoding.ModularDecode decodeVector_eq and round-trip/injectivity readers; Candidates.listToNat_lt_two_pow:166. | decodeResidues is total reduction modulo p; original aliases retained by wrapper/adversary replay. No new integer parser or scalar codec algorithm. |
| Polynomial completeness | Mathlib MvPolynomial finite coefficient expansion, eval, monomial algebra, exponent-block sums. | pad_one is a new class-specific bidegree completeness theorem; nearest totalDegree APIs do not state its separate public/private block condition. No general polynomial algebra lemma is re-proved. |
| Layered path sums | Fin.prod_univ_castSucc, empty-product/sum APIs, Fin.append/standard cast lemmas, Equiv.addRight and Probability.expect_sample_equiv:304. | New specialized forward/backward action identities; determinant/canonical-form proof deliberately not copied. No IK02 theorem re-proof. |
| Pi raw/group lift/correctness | New PG.reconstruct/rec_spec/exactPrivacy readers; Exponents group actions; source/GT laws already published in Group. | Reconstruction coefficient identities specialize the existing law to basis vectors. Proof-only representatives may be used for arbitrary group M; no algorithm outputs them. |
| Pi rank/slack | Mathlib LinearAlgebra/Matrix/GeneralLinearGroup/Card.card_GL_field:82; shared expectation/monotonicity and SubexpSmall APIs. | Exact 3×3 rank probability and its 3/p bound are source-specific arithmetic specializations, not new GL counting or asymptotic closure proofs. |
| Quadratic tensors/cross leakage | Classes.privateTensor/polyTensorEval; Mathlib kroneckerMap mixed-product laws; Exponents pairTensor/known scalar actions. | crossLeakLeft/Right are new explicit source-group reduction functions. Known-scalar compatibility laws reuse these APIs. |
| Typed protocols/advice | Linear.protocolHandler versus Quadratic.protocolHandler; Linear.adviceDraw/Enc versus outer counterparts. | **Disclosed near-copies**: same four refusal cases over DIFFERENT typed query/answer families, and scalar-cast/codec wrappers for DIFFERENT tape lengths. No new generic probability lemma. Consider a future shared protocol abstraction only if scope opens. |
| PHFE adapter | Published raw equivalences/readers; List.foldl state replay and typed Option answer encoders. | Original wire x,y,f aliases are retained. It checks typed payload and key-index consistency; no inverse group decoder. |
| Perfect→zero correctness / security closure | Shared AllOutputs/probability readers, Negligible.add/mono, SubexpSmall/SubexpHard closure. | New FE-specific glue headers, not replacement probability or negligible definitions. Final proofs must use these existing implications. |
| Universal subexp exponent | Shared SubexpDLIN common exponent, polynomial absorption, rank/mddhSlack decay. | Choose e<min(c_DLIN,1) BEFORE adversary/q and apply explicit DLIN-composed bound. Per-dimension existential mddh_subexpHard alone is insufficient for this quantifier order; FE agent corrected sketches accordingly. |

No genuine completed mathematical proof duplicate was identified in the static term-reader
and M0-sorry code. This is not an exact?/apply? certificate: those required probes remain
pending root execution. The clearly identified near-copies above must stay in REPORT's
Overlap/reuse section. Root is splitting PHFE.embedValue_injective into a proof-only Embedding
module: its use of pow_val_bijective.injective proves losslessness and returns NO exponent.
