# Wee20 construction, games, assumptions and readings

These are source-to-M0-header correspondences. No substantive sorry is represented as a
proved theorem. Source facts were rechecked from the verified local text and complete page
images already inspected; Wee20 printed page equals PDF page.

## Security notion and assumptions

| Source | Actual clause | Lean counterpart / reading |
|---|---|---|
| §2.1 p4, implicit representation | g^a encodes field a; pairing multiplies exponents. | Pairing/Exponents expVec/expMat/target analogues, group actions, pairVec/pairMat/pairTensor. Honest code uses powers/products/pairings, not a scalar inverse of exp. |
| §2.1 p4, Assumption1 | Uniform M:rows×k, S:k×d; response MS versus independent uniform U:rows×d. | MatrixDH.Defs mddhSample/mddhGame/mddhAdv, k=2, explicit sequential draws. **Uniform** M, not uniform full-rank M. |
| §2.1 p4, bilateral version | Both source-group copies share the same exponents and branch. | Symmetric setting identifies the copies. The printed W5 equation is recorded below; no malformed bilateral definition is copied. |
| §2.1 p4, k-Lin⇒MDDH | Paper cites a tight implication without constructing it here. | SelfReduction.dlinToMddh and mddhAdv_le give a disclosed polynomial-column implementation with loss d*DLINAdv+4d/p. No tightness claim. |
| §2.1 p4, rows≤k | The source says unconditional security in these dimensions. | mddh_smallRows_adv_le uses explicit statistical rank loss (≤2/p for rows≤2), not false exact equality for singular uniform M. |
| §2.2 p5 | mpk first, one scalar (x,z) challenge, ct, then adaptive key queries. | Generic SemiAdaptive game; typed Linear/Quadratic SAAdv and freshSaGame. Total budget includes challenge; early keys and repeated challenges return None deterministically. |
| §2.2 p5 | Simulator Setup* then Enc*(state,x), KeyGen*(state,x,f,allowed value), stateful. | SASimulator.Raw; Pi SimState; Quadratic SimState retaining y1,y2; PHFE wee20SASim_raw. State update from Enc is used for later keys. |
| §2.2 p5, Remark1 | Scalar-output extraction is practical only for bounded values. | Actual Dec outputs GT exponent. No bounded brute-force discrete log is implemented. |
| §3 p6, unnumbered claim | Main quadratic PHFE under bilateral k-Lin and k'-Lin. | Symmetric k=k'=2, canonical DLIN. Public claim cited as §3 with §3.3; it has NO numbered main-scheme theorem. |

Canonical-DLIN fidelity: JLS26 §1.1 PDF3 is the primary tuple (g^a,g^b,g^(ar),g^(bs),g^(r+s))
versus final g^t. GJLS21 Def3.3 printed p18/PDF22 gives the matrix-style response. Linear.lean
keeps both games separately: real branches agree exactly; random branches agree conditioned
on a,b≠0 and otherwise differ by at most 2/p−1/p². This discrepancy is not silently erased.
The direct SelfReduction column randomizer already accounts for its zero-coordinate cases;
do not add dlinMatrixSlack again after mddhSlack.

## Quadratic honest and simulator algorithms (§3.1 p6, §3.2 p7)

| Source step | Lean counterpart | Important shape / limitation |
|---|---|---|
| Setup A1:k×n1, A2:k'×n2. | Quadratic.SetupDraw/setupCore; public MPK group A1,A2. | Both are 2-row matrices in this instantiation. Secret scalar samples occur only in draws/theorem parameters; public algorithms retain group encodings. |
| Fixed M stacks A1⊗I_n2 over I_n1⊗A2. | mixScalar/mixGroup. | M rows=2n2+2n1, columns=n1*n2. mixGroup computes with GROUP A1,A2 and known identity scalars. |
| Setup0 with M, or per-key KeyGen0 with M. | Quadratic.MSK.matrix plus each Key.matrix; keyCore forwards (f,M). | R2 chooses §4's per-key group-M form; one fixed PUBLIC M is retained for every outer key. |
| Enc chooses s1,s2, masked y1=s1A1+z1,y2=s2A2+z2. | encCore; EncDraw=(s1,s2,Pi seed). | No unused s0. y1 is computed only in the GROUP by honest Enc, because A1 is public group data. |
| Pi signal s1⊗z2 concatenated with y1⊗s2. | signalGroup; signalScalar only for known scalar samples/advice. | Actual second block is group y1 raised to known s2. No recovery of y1 or A1 scalars. Canonical product/sum coordinate equivalences fix ordering. |
| KeyGen forwards f. | keyCore/group-M metadata. | Arbitrary typed f in raw construction; no hidden class or efficiency restriction in correctness/security. |
| Dec Eq(4)–(5). | pairTensor, Quadratic.dec; tensor/mixing helpers and quadratic_dec_eq. | Weighted target-group pairing of y1,y2 divided by Pi Dec; output e(g,g)^(private value). |
| Setup* draws A1,A2 and Pi Setup*. | simSetupCore. | Scalar y defaults to zero before Enc; singular Pi basis uses total specified inverse behavior. |
| Enc* chooses uniform scalar y1,y2 and Pi Enc*. | simEncCore. | Returns exactly these exponentiated vectors and stores the same scalar vectors in next state. |
| KeyGen* uses [(y1⊗y2)f(x)]/[µ]. | crossLeak/simKeyCore. | Both factors are SOURCE group values. Known scalar y's form the first factor; supplied group µ is inverted as a group element. |

## Quadratic Games0–4 (§3.3 pp7–8)

| Source hop | Exact implementation | Bound / reading |
|---|---|---|
| Game0 p7 | QuadraticSecurity.game0Handler and actual fresh honest endpoint. | Honest encCore/keyCore; public M fixed. |
| Game1 p7 | game1Handler uses actual Pi simulator and actual Linear.leak of the known scalar signal. | Pure toLinear adversary, typed history replay, same A.coins/A.budget. First-hop gap bounded by Pi ACTUAL fresh-law advantage. |
| Game2 p7 | game2Handler replaces key leakage with source-group cross quotient. | game1_game2_accept via Eq(5), exact. No output-group inverse. |
| Game3 p8 | game3Handler replaces y1 only. | red2 receives MDDH one-column,n1-row GROUP A1/y1, retains known scalar y2, answers adaptive leakage with crossLeakLeft. Random shift by adaptively chosen z1 is exactly uniform. |
| Game4 p8 | game4Handler replaces y2 as well. | red3 receives GROUP A2/y2, knows scalar uniform y1, uses crossLeakRight. One-column,n2-row MDDH. No additional rank loss. |
| Actual simulator endpoint | Fresh.freshSaGame uses actual setup/enc/keyGen or simSetup/simEnc/simKey; ideal state stores simEnc's result. | saGame_eq_freshSaGame is substantive acceptance-law coupling, not just the indexed padded game selector. |
| Combined bound | quadratic_saSimAdv_le; quadratic_saSimAdv_dlin_le; PHFE wire bound. | Four MDDH advantages+ONE Pi rank loss; DLIN factors1,ℓ,1,1 and total matrix correction4(ℓ+3)/p. Advice precedes EVERY realiser. |

## Pi setup, honest algorithms and correctness (§4 p8, §4.2 pp9–10)

| Source clause / equation | Lean counterpart | Exact reading |
|---|---|---|
| Input is group z; function key includes different group M. | Linear.encCore group z; KeyQuery (f,GROUP M). | Encryption private length zDim is DISTINCT from PG output length n'. M:zDim×n'. No uncomputable wire-to-exponent decoder. |
| Setup draws A:k×(k+1),W,U,V. | Linear.SetupDraw/setupCore. | A:2×3,W:3×zDim,U:3×(ℓ×2),V:3×2, all unconditioned uniform. |
| mpk=[A],[AW],[AU],[AV]; msk=W,U,V. | Linear.MPK/MSK. | Source transpose orientation is normalized through Matrix.vecMul/mulVec. |
| Enc emits [sA],[z+sAW],[sAU X(x)+sAV]. | Linear.encCore. | Known s∈F², group products/powers only. Ciphertext blocks3,zDim,2. |
| Key draws T:(k+1)×t,R:k×m. | Linear.KeyDraw/keyCore. | T:3×(TIdx⊕Fin n'), R:2×MIdx(f). Actual m may vary with f but is bounded by PG.mBound. |
| Key blocks [Tbar+WM], [TL1+U(I⊗R)], [TL0+VR], [R]. | keyCore; group matrix actions and Hadamard products. | Tbar selects n' OUTPUT columns, not zDim. Shapes TL1:3×(ℓm), TL0:3×m. |
| Dec Eq(6). | decFirst. | Pair ct1 with R-independent key/output block and divide by appropriate first ct pairing. |
| Dec Eq(7). | decSecond. | Mixed-product cancellation uses public tensor X(x), L1/L0 and R; all results in GT. |
| Dec Eq(8). | Linear.dec using PG.recVec. | Reconstruct weighted first/second garbling outputs. |
| Correctness Eq(9)–(11), every t. | LinearCorrect helpers/pi_dec_eq/raw correctness transfer. | Known scalar z but arbitrary GROUP M. rec_output_eq_eval and rec_matrix_eq follow from PG rec_spec using basis vectors; no scalar M witness is computed by an algorithm. |

## Pi simulator (§4.2 p10)

| Source step | Lean counterpart | Reading / status |
|---|---|---|
| Uniform Acol:3×2,c:3; inverse of H=(Acol|c)^T. | simSetupCore, basisMatrix, total Matrix inverse. | All A,c are unconditioned. Inverse is total (zero on singular determinant in Mathlib's total inverse convention). |
| Cperp,aPerp inverse columns. | SimState.basisInv and projections/combineRows. | On good H they satisfy the exact dual-basis laws. No incorrect inverse identity is stated on singular H. |
| Uniform WUV,wtilde,vtilde; projected public key. | SimSetupDraw/simSetupCore. | Same public projection law as honest setup. |
| Enc*=[c],[wtilde],[vtilde]. | simEncCore/simEnc. | Deterministic after setup. No z supplied to simulator. |
| Eq(12) simulated key using PG*. | groupPGStar/simKeyCore. | pgbStar at zero leakage plus supplied group µ at m0; all source-group powers/products. group lift can use scalar representatives only inside a proof. |
| Simulator total before challenge. | Protocol refuses pre-challenge keys; core remains total. | Outer defaults y=0; Pi static setup state. No extra security assumption restricts zero dimensions. |

## Pi Theorem1 and Lemmas2–5 (Appendix B pp12–14)

| Source item | M0 counterpart | Proof route / exact loss |
|---|---|---|
| Theorem1 p12 | LinearSecurity.linear_saSimAdv_le and linear_freshSaSimAdv_le. | Two MDDH advantages (one response column,3 rows) and (ℓ response columns,mBound*q rows), one exact rank failure. This theorem is for Pi, not the main quadratic scheme. |
| Game0 p12 | honest masked ciphertext, honest keyCore. | Fresh actual algorithm laws linked by Endpoint.saGame_eq_freshSaGame. |
| Game1 p12 | replace sA by independent c; honest keys. | Unfiltered first MDDH hop, explicit red0. |
| Game2 p13 | decomposedKey using Cperp/aPerp. | Equal to Game1 on good H. Only this and later middle games are filtered to false on singular H. |
| Game3 p13 | semiKey with common hidden global U row times each R. | game2_game3_accept via exact adaptive public-fixing change of variables. |
| Game4 p13 | semiKey with independent uhat per query/node/public coordinate. | red1 embeds group R and uhat from matching MDDH rows; exact good filter known from advice. |
| Game5 p13 | actual simKeyCore with source group leak. | Exact PG privacy identifies Game4→5; fresh actual simulator endpoint linked separately. |
| Lemma2 p13 | game0_game1_le and red0. | One MDDH¹_2,3; no rank term in the reduction. |
| Lemma3 statement p13, proof p14 | game2_game3_accept. | Fix public projections exactly; replace paper's random-guessing argument. No guessing factor or complexity leveraging. |
| Lemma4 p14 | game3_game4_le and red1. | One MDDH^ℓ_2,mBound*q for all adaptive key blocks together. Finite row map node*q+query; no growing family of unbounded-index machine advantages. |
| Lemma5 p14 | game4_game5_accept. | Exact privacy of layered PG, δ=0; source ≈s strengthened to equality for this instance. |
| Source's printed +1/p p12 | rankSlack/linearSlack and good-event endpoint comparison. | Corrected exact unconditioned rank loss, charged ONCE. See counterexample and adaptive bijection below. |

### Exact rank discrepancy and counterexample

H is an unconditioned uniform3×3 matrix over Fp, so
success=(1−p⁻¹)(1−p⁻²)(1−p⁻³),
failure=p⁻¹+p⁻²−p⁻⁴−p⁻⁵+p⁻⁶.
At p=2 failure=43/64>1/2. The source's 1/p is correct conditional on Acol having full column
rank, which its printed draws do not impose. The draft keeps the actual draws and this exact
failure. Shared Matrix.card_GL_field supplies the cardinality; no local GL counting lemma.
The comparison partitions both endpoint acceptance laws by the SAME good event, bounds the
bad conditional difference by1, and hence charges failure once. A naive triangle through two
separately filtered endpoints would incorrectly charge it twice.

### Adaptive bijection, including latent U

For good H let a be its final inverse column, so Acol^T a=0 and c^T a=1. Given the challenge
selected from the public projections, set

U'=U; W'=W+a z*; V'=V+a((c^T U)X(x*)).

This preserves Acol^T U, Acol^T W and Acol^T V, hence preserves the selected x*,z*. It is
triangular: unchanged latent U determines the same shift in both directions; the inverse
subtracts these shifts. U is NOT asserted to be determined by the public projections.
Remaining inverse-basis coordinates and unused latent components are reindexed/resampled to
get the independent target low-row law. This conditional law, not a guessing argument, is
the substantive exact Lemma3 obligation. No group-to-scalar algorithm is hidden in this proof.

## Required misprint/readings table

| ID | Verified source location | Printed issue | Chosen reading and Lean counterpart |
|---|---|---|---|
| W1 | Wee Lemma1 p8; inherited AGW Lemma2 p12 | L0/L1 shapes swapped. | L1:t×(ℓm),L0:t×m; AGW(32)/AppB p38 and Wee KeyGen p9 agree. PG.Raw fields use these shapes. |
| W2 | Wee Enc* p7 and Game4 p8 | y2 source tag1 instead of2. | Intended second source group; symmetric copies coincide. Quadratic CT contains source-group y2. |
| W3 | Wee Games3/4 p8 | Uniform vectors over Z_q although group order is p. | Draw over actual public group order Z_p; no unrelated q modulus. q in Lean is only query budget. |
| W4 | Wee KeyGen* p7 | First cross term tagged GT, multiplied by source-group µ inverse. | Both factors source group, as Game2 p7 and Pi simulator signature require. crossLeak and reductions perform this source-group computation. |
| W5 | Wee bilateral MDDH p4 | Duplicate [MS]_1 and output2 in real experiment. | Second copy [MS]_2, Boolean1; actual symmetric assumption uses canonical Boolean game. No malformed definition copied. |
| R1 | Wee Setup* p7 | Private dimension n1,n2 lacks primes. | Pi input length2*n2+n1*2 from actual outer private dimensions; piDim fixes it. |
| R2 | Wee Setup p6 vs §4 p8/KeyGen p9 | Fixed M passed at setup vs per-key M. | Per-key GROUP M at Pi; outer stores its one fixed public M in MSK/key metadata and forwards it. |
| R3 | Wee Game1 p7 | Samples unused s0. | Omitted; raw and simulator encryption draws contain only used seeds. |
| R4 | Wee Lemma1 pp8–9, Lemma5 p14 | Privacy stated statistically. | Exact equality for the specialized AGW/IW layered instance, no PG slack term. |

## Citation repairs identified during this read-only audit

The current LinearSecurity/Fresh freshSaSimAdv doc and QuadraticSecurity/Theorems bibliography
incorrectly say Theorem1 is on p8. It occurs ONLY in AppendixB p12. The parent was notified to
repair these two prose locations before statement freeze. Main-scheme security remains the
unnumbered §3 claim with §3.3. No source proof or Lean statement was edited by this audit.
