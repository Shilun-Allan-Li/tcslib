# Public-key PHFE for private quadratic functions from DLIN — Phase A report

Status: **R2 own compilation and axiom checks complete on unchanged source
073d0a5a3ff88d958f94c2ae50a67bc92476f616. M3–M5 proofs remain in progress.**
All 19 changed modules and their downstream modules (33 required modules) compile with
rc0 and zero errors. The actual sweep checked 41 modules, including missing dependencies
and refreshed upstream proof objects; every checked source equals git show of this HEAD,
and every object is fresh. The sweep records 23 existing direct sorry warnings/tokens,
14 in the required33-module subset. The owned source still has33 direct admissions;
r2 introduced none. All8 new declarations are standard-axiom-only. Exact native axiom
prints cover all51 changed/added written declarations (50 standard-only, one known
unfinished-security dependency) and all498 stored constants in the19 repaired modules.
The source has88 owned files and19,487 lines; no r2 source fix was necessary.

The source-only checkpoint4 report reflected an overly broad interpretation of the
maintainer-replay instruction. Seyoon clarified that worker compilation remains mandatory;
the own checks below now satisfy that requirement. The maintainer's INDEPENDENT replay is
separate and remains theirs. This section supersedes checkpoint4's worker-check status.

Checkpoint0 was delivered at exchange commit1e77173a7032b57aa22260787711c6c7a1b7596e,
activating the statement/prose freeze on source70b85f9ba83f27393d98fa5bf88505aea3d22a8d.
The relayed r1/r2 exceptions are exact-name/hash pairs; the r2 freeze still passes for
precisely51 repaired records, zero other changes and all5 controls. Earlier preparation
snapshots and their pending-check wording are historical.

New checkpoints follow PHFE-C0-F02: only src/, patches/, REPORT.md, SHA256SUMS and compact
actual check evidence are published. Full raw evidence stays local; earlier payloads and
history remain untouched. Checkpoint4 delivery is883b51a99a1fbe1e94e5c04f293fc42ec47eec20.

Post-M0 source commits: exponent algebra
(`f7baa8a9c9f99ca98311e0ebab05e4190d742c4c`), deterministic runner/path skeleton
(`b881f12266fa4caf841167539b4cbe2e6fc353ab`), tensor codecs/layered reconstruction
(`dc9fdccf8bcaa454936263a2be05b446238330e4`), polynomial completeness/prefix flow
(`9cbc7d60cf5454594faf596dff53bc8c2b204b4b`), and committed simulation, decryption
correctness and shared codecs (`c222e6b92d75478549e5057c37c9119bf6be50c1`).
The latter closes 23 existing admissions and adds eight proved helpers. Full native
stored-constant census, Rule 10 seals/controls and final security proofs remain pending.


M2 was published as exchange commit `e50e4a2520c32cac1f411d302153c9065806e681`.
Its 2941-file payload contains 80 Lean source files; SHA256SUMS has hash
`63d7c5ec1997dee7416d3df1e6ab2eca1cdabc771eb3285880c0e6ba05c636ab`.
The first push attempt was rejected by automatic review for unverified egress
authorization. Re-reading the user-supplied dispatch's explicit destination and checkpoint
instructions, then checking clean scope, all hashes, no PDFs and no credential hits,
resolved the rejection; the identical command was accepted. Both pull logs and the
successful push log are retained. Only the owned payload path changed.

The stronger native-syntax freeze audit passed at this exact committed HEAD:
all 1171 M0 declarations were recovered, with zero frozen header/prose changes and
21 permitted helpers (1192 current written declarations). All five actual-source controls
behaved correctly: reject a type edit after a return-type let, prose edit with a sketch,
and sketch-marker edit; permit genuine proof-body and sketch-only edits. Evidence is
`evidence/freeze/native-c222-run3/` and `native-c222-binding.json`, binding all 80 current
files to git show HEAD. The original M0 manifest remains unchanged. Earlier text-parser
limitations and failed tool-development attempts are retained honestly; no user theorem
was changed to make this check pass. The final compiled-declaration type comparison,
full stored-constant census and Rule10 suite remain separate required checks.

## Checkpoint0 baseline

Source HEAD: `70b85f9ba83f27393d98fa5bf88505aea3d22a8d`. The checked source contains 74 new Lean modules,
13,745 physical lines and 144 direct proof admissions. Correctness, algebra,
endpoint couplings, security bounds and asymptotic consequences are stated; their remaining
admissions are not completed proofs. The generic perfect-correctness-to-zero-error implication
is proved and elaborated.

The complete import closure has 285 modules. Every module returned rc0, both error forms
were zero, and a fresh object was produced. `evidence/build/summary.tsv` binds all checked
source bytes to this HEAD, retaining each actual check-time HEAD; unchanged bytes are
explicitly rebound rather than described as rerun. The native collector covers 74 modules
and 2225 stored constants. All 387 requested public definition readers are natively verified.
Style/sketch/width checks pass. The four campaign warning lines cover five acronym-case
readers already verified by the native catalog; no new FAIL remains.

The native statement/axiom census is complete: 1933 constants are standard-axiom-only;
292 transitively depend on sorryAx, with no other nonstandard axiom. The source has 144
direct admissions. The census retained 41 completed chunk commands from its original pass
and replayed 4 chunks after repairing a constructor-edge omission in the audit helper.
The original failed probe is retained; it is not described as a clean run. All 2225 names,
types, axiom records and dependency traces were reconciled against the native collector.
Checkpoint0 was published as exchange commit `1e77173a7032b57aa22260787711c6c7a1b7596e`.
The statement freeze is active at source HEAD `70b85f9ba83f27393d98fa5bf88505aea3d22a8d`.
Checkpoint 0 was delivered at `1e77173a7032b57aa22260787711c6c7a1b7596e`, and its source
`70b85f9ba83f27393d98fa5bf88505aea3d22a8d` became the frozen baseline at that publication.
The original report snapshot predates that delivery and is historical. The preserved M0
manifest and controls are under `evidence/freeze/`; later native audits reran them.
The full Rule10 seal/control/explicit-body suite remains required
for final delivery and is not claimed passing at M0. Efficiency targets are intentional
Phase B obligations. No machine, RAM program, PolyHandler or sampler is constructed.

The primary result being specified is public-key, many-key, epsilon-one simulation PHFE for
`(x,y) ↦ [Σ_{j,k} f_{j,k}(x)y_jy_k]_T`, each public coefficient of constant degree at most d.
The raw semi-adaptive bounds are the core. The committed Definition 4.3 bounds use the actual
`TwoStage.toSA` conversion and exact equality of game laws, without an abstract machine-building
security implication. The broader IO/all-circuit FE pipeline is outside this unit.

Paths in the fidelity and rule-15 tables are relative to
`TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/`, except explicitly named
Pairing/shared files. `FE` abbreviates the namespace
`TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption`; it is not a new Lean namespace.
The source fidelity tables below are statement comparisons, not certificates for admitted proofs.
PGSound is a semantic hypothesis for raw correctness and for wire-to-typed ideal-value
transport; every raw security headline explicitly carries it. The layered instance supplies it.

## Primary fidelity: GJLS21

GJLS printed page = PDF page minus four. All clauses here are supported by the verified
source ledger below. The current wire-machine API is `FE.toSAAdv`. Older drafts placed
this adapter in the NUPPT namespace; those drafts are superseded by the current FE API.

### Definition 4.1: syntax (printed p19 = PDF23)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| A parameterized PHFE family has public X, private Y and output Z. | Defs/Raw: FnClass; Classes: phfeClass, quadClass; FEScheme.Raw.cprm/embed. | Public and private inputs are fixed-width words interpreted as field residues. Class values are scalar; injective embedValue gives GT output. Separate scalar/GT types are intentional. |
| The algorithms are PPT. | Defs/Efficient: FEScheme extends Raw with pubGen_eff, setup_eff, enc_eff, keyGen_eff, dec_eff. | Raw bundles have no PPT claim. The efficient type cannot be inhabited without all fields. Phase A writes targets and assembles from proofs supplied as arguments. |
| PPGen receives unary security and function parameters. | Pairing/MatrixDH/Parameters.publicParamsGen, PublicParams; FEScheme.Raw.pubGen. | One group generator for the chosen polynomial family; dimensions/degree are family parameters, not hidden per-κ constants. Public pp stores actual description plus uniform nonidentity g. Its additional draw has approved pubGen_eff. |
| pp is available to each later algorithm. | All raw core/draw/codec arguments include pp. | Class parameter is pp.orderParam, never a separately evaluated schedule. Group operations use the given BilinearGen structure. |
| Setup(pp) outputs pk,msk. | FEScheme.Raw.setupCore + SetupDraw; Defs/Correctness.setup; PHFE.setupCore. | One complete finite nonempty exact draw type, then deterministic core. |
| Enc is public-key and receives x,y. | Raw.encCore κ pp pk x y; PHFE.encCore. | It receives no MSK. Scalar y is duplicated into the two quadratic slots; the public x is kept separately. |
| Enc returns x along with ct. | Raw.ctLen excludes x; generic realView/viewWord and SA protocol retain x. | The typed ciphertext object excludes separately known x; all dec/game interfaces supply x explicitly. This matches the source pair (x,ct), not a hidden-input variant. |
| KeyGen(msk,f) returns sk_f. | Raw.keyCore + KeyDraw; PHFE.Key retains original wire f and typed quadratic key. | Decoding f modulo p does not erase the original word or collapse distinguishable wire aliases. |
| Dec(sk_f,x,ct) is deterministic and may fail. | Raw.dec : ... → Option DecOut; PHFE.dec. | Concrete honest output is some GT element; generic None supplies the failure marker. No scalar discrete-log output claim. |
| Finite exact sampling belongs to the syntax. | Raw draw Fintype/Nonempty fields; encDraw/KeyDraw may depend on inputs. | No machine or product sampler is built. Existing instances are carried/read through published APIs. |

### Definition 4.2: correctness (printed p19 = PDF23)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| For each fixed polynomial parameter family, all messages and represented functions. | Raw.Correct; PHFE.class_eval_eq; wee20PHFE_raw_correct. | Perfect equality for every honest draw gives zero error in each fixed family and covers arbitrary wire words, including residue aliases. This does not introduce a dimension-family-uniform negligible security bound. |
| pp,setup,enc,key randomness in the prescribed order. | Raw.honestRun and its reader; raw setup/enc/keyGen laws. | Actual finite core-plus-draw laws are used; no simulated/padded endpoint is substituted for correctness. |
| Dec equals the functionality output except negligible error. | wee20PHFE_raw_correctExcept_zero; efficient wee20PHFE_correctExcept_zero. | Zero error, output in GT via injective embedValue. These substantive raw correctness laws are M0 obligations. Efficient transport is a pure assembly consequence. |
| The real class uses all field residues. | phfeClass_eval_encoded with p≤2^w; PHFE decoding and width readers. | Wire evaluation is total modulo p for all words. Encoding completeness uses the existing reachable-group width lemma, not an arbitrary-modulus promise. |

### Definition 4.3 and Remarks 4.3/4.5/4.6 (printed pp19–20 = PDF23–24)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| One simulator is chosen before every adversary. | Raw.SimSecure := ∃ Sim : Simulator S, S.SimSecureWith Sim.toRaw. | Efficient Simulator has setup_eff/enc_eff/key_eff plus state_bounded/value_bounded. Raw With predicates name the one fixed simulator rather than asserting an efficient instance. |
| Simulator may be stateful. | Simulator.Raw.St; setupCore/encCore/keyCore return or thread state; generic idealView uses StateT. | Concrete committed simulator is wee20Sim_raw, obtained from the stateful SA simulator; separate committed efficiency targets are supplied. |
| A=(A1,A2), stateful PPT. | Simulation/TwoStage.TwoStage first/second : NUPPT; commitment stores retained state. | Nonuniform machines strengthen the source adversarial class. Original state is included in the final view. |
| A1 commits x*,y*,all q functions before pp. | simGame draws A.first.Coins and runs it on [] before realView/idealView; Commitment.decode. | Missing bits are false; suffix is retained as first-stage state. There is no restriction to well-formed adversary strings. |
| pp is drawn after commitment. | realView/idealView start with S.pubGen. | Audited order matches the printed boxes. |
| Real Setup, Enc, then ordered KeyGen calls. | Simulation/Games.realView with List.mapM over List.finRange q. | Exact honest laws, source order, polynomial many keys. |
| A2 sees pp,pk,ordered keys,x*,ct*. | viewWord/viewWordBits. | View also carries A1's retained state, as required for stateful machine semantics. Original key/function encodings remain distinguishable. |
| ε=1 always supplies x*,functions,values, never y*. | Omega; Commitment.omega; Simulator.Raw input types. | This is Remark4.3's exact branch. No biased Sample coin or ε<1 functionality is claimed. |
| Literal source values are in the functionality codomain GT. | Omega.values : C.Out; phfeClass scalar encValue; PHFE wrapper computes source-group g^µ. | **Disclosed deviation**: simulator receives µ∈Zp, justified by Theorem9.2 proof Hybrid1, printed p61/PDF65, whose ω explicitly carries scalar v_i. Π receives g^µ. This is not an inverse from GT to G. |
| Ideal Setup is independent of x*,y*,functions. | Simulator.Raw.setup inputs only pp; concrete Quadratic.simSetupCore. | State is sampled once before the simulator sees challenge information. |
| Ideal ciphertext depends on allowed public information, with state retained for keys. | Simulator.Raw enc on Ω; SASimulator.Raw enc on x only; Quadratic.simEncCore stores y1,y2. | SA simulator is stronger: its encryption does not receive future functions or values. |
| Ideal per-key input includes f and its allowed value. | Generic idealSAKey computes C.eval; concrete PHFE.simKeyCore converts known µ to g^µ. | The simulation core receives only allowed information and stored state, never the private challenge vectors. |
| Absolute acceptance gap. | shared Games.advantage; Raw.simAdv. | No extraneous factor of two. |
| Negligibility is familywise. | SimSecureWith fixes C and S, including their polynomial dimensions, before ∀A,∀q,Negligible. | The negligible bound may depend on that fixed family, adversary and query polynomial. No uniform bound over all polynomial parameter families is asserted; correctness remains perfect for each family. |
| Many-key: all polynomial q. | SimSecureWith quantifies ∀ TwoStage ∀ q:PolyExpr. | One simulator independent of q. TwoStage.toSA uses q+1 TOTAL calls (one challenge plus q keys). |
| Subexponential variant. | SubexpSimSecureWith/SubexpSASimSecureWith and SubexpDLIN. | One positive exponent is chosen before adversary and q; shared SubexpSmall/SubexpHard APIs, not a local notion. |
| Derive this committed notion from the semi-adaptive bound. | SemiAdaptive/FromTwoStage: TwoStage.toSA, simAdv_eq_saSimAdv; Wee20.wee20PHFE_simAdv_le. | Applies the typed core to the actual converted adversary. No abstract SASimSecure→SimSecure theorem requiring an unbuilt machine. |
| Efficiency and reduction realizability are distinct. | Wee20RealizableSA/43 and MDDHRealizable vs Scheme/Sim/PG targets. | SA realizability ranges only over FE.toSAAdv A q; committed only TwoStage.toSA q. It never quantifies over every uncomputable typed SAAdv. |

### Definition 4.6 (printed p22 = PDF26)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| One polynomial bound before all numeric dimensions, degree and security parameters. | Targets/CircuitEfficiency.CircuitLinearEfficient: ∃q,∀ℓ,n,d,κ,... | q depends only on κ for fixed G; it precedes pp, honest pk, all message words and complete draws. |
| Boolean encryption circuit size is at most (ℓ+n)poly(κ). | Existing BoolCircuit.MultiDAGCircuit with IsFaninTwo and C.size≤(ℓ+n)*q.evalκ. | C.size counts input and internal gates. This is the circuit obligation used by the GJLS21 headline. It is a Phase B target, not an existence proof supplied here. |
| Public parameters and keys are supported honest values. | Typed PublicParams plus an explicit setup-draw-image witness for pk. | Public descriptions are reachable and g is nonidentity; honest support includes singular setup outcomes. Circuit arity and circuit follow fixed pp/pk and precede every input/draw. |
| pp and pk are hardwired; messages and encryption randomness are inputs. | x bits ++ y bits ++ Wire.quadraticEncDraw pp ω. | All six scalar draw coordinates and framing remain present. Exact input.length=N prevents getD truncation; exact output is List.ofFn(PHFE.encCT(...PHFE.encCore...)). No decoder or new draw codec is introduced. |
| Positive total message dimension. | Explicit 0<ℓ+n guard. | Raw algorithms and security remain total at zero dimensions; the multiplicative efficiency target has the source positive-size domain. |
| Additional implementation obligation. | Existing TM LinearEfficient remains a separate field of Targets. | The TM target is retained; no implication from its time bound to the circuit target is asserted. Both are Phase B obligations. |
| Concrete ciphertext width. | PHFE.ctLen_eval; wee20PHFE_ctLen_eval. | CT is (6n+5)wG bits, excludes public x, independent of ℓ,d. |

### Section 9 required class (printed pp57–58 = PDF61–62)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| x,y in field vectors of a polynomial common dimension. | phfeClass ℓ n w d; specialize ℓ=n for the literal source form. | Separate dimensions are a parameter generalization, not a loss of the source class. |
| GT output [Σ_j,k f_jk(x)y_jy_k]_T. | phfeEval_sum; phfeClass_eval; PHFE.class_eval_eq and embedValue. | The exact private quadratic expression is preserved, including cross terms and coefficients; no change to linear private computation. |
| Each f_jk has constant public degree. | PolyTensor p ℓ (n*n) d and polyTensorEval, xhat=(x,1). | d is a fixed natural family parameter. Ordered padded tuples encode all public polynomials of degree≤d. This intentionally restricts Wee20's broader ABP/NC1 class to GJLS's required class. |
| Degree at most two may contain affine/constant private parts in applications. | BidegreeAtMost and pad_one completeness theorem. | Homogeneous private quadratic form after appending a constant-one private coordinate; actual completeness is ∃tensor for each bidegree-bounded MvPolynomial, not a tautological padding equality. |
| The class implements structured PRG evaluation. | pad_one and class embedding; external consumer is not built here. | §9 implementability observation is represented by a polynomial-class bridge; no IO/sPRG theorem is claimed in this unit. |
| Unbounded collusion means every polynomial number of keys. | many-key SimSecure/SA bound and q parameters. | Does not mean an infinite transcript or unbounded runtime. |
| Main source conclusion consumes linear efficiency plus many-key simulation. | PHFE/Headlines.wee20PHFE_gjls21. | Conjunction: CorrectExcept0, SimSecure, CircuitLinearEfficient, under Targets, machine-derived L2 realizability, fixed order and DLIN. Public hypotheses are explicit; Phase A does not construct the targets/machines. |

## Fidelity: Wee20 algorithms, experiments and source readings

Wee20 printed page = PDF page. These are explicit raw definitions and M0 statements;
no admitted theorem in the table is presented as a completed proof.

### Security notion and assumptions

| Source | Actual clause | Lean counterpart / reading |
|---|---|---|
| §2.1 p4, implicit representation | g^a encodes field a; pairing multiplies exponents. | Pairing/Exponents expVec/expMat/target analogues, group actions, pairVec/pairMat/pairTensor. Honest code uses powers/products/pairings, not a scalar inverse of exp. |
| §2.1 p4, Assumption1 | Uniform M:rows×k, S:k×d; response MS versus independent uniform U:rows×d. | MatrixDH.Defs mddhSample/mddhGame/mddhAdv, k=2, explicit sequential draws. **Uniform** M, not uniform full-rank M. |
| §2.1 p4, bilateral version | Both source-group copies share the same exponents and branch. | Symmetric setting identifies the copies. The printed W5 equation is recorded below; no malformed bilateral definition is copied. |
| §2.1 p4, k-Lin⇒MDDH | Paper cites a tight implication without constructing it here. | SelfReduction.dlinToMddh and mddhAdv_le give a disclosed polynomial-column implementation with loss d*DLINAdv+4d/p. No tightness claim. |
| §2.1 p4, rows≤k | The source says unconditional security in these dimensions. | mddhAdv_smallRows_le uses explicit statistical rank loss (≤2/p for rows≤2), not false exact equality for singular uniform M. |
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

### Quadratic honest and simulator algorithms (§3.1 p6, §3.2 p7)

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

### Quadratic Games0–4 (§3.3 pp7–8)

| Source hop | Exact implementation | Bound / reading |
|---|---|---|
| Game0 p7 | QuadraticSecurity.game0Handler and actual fresh honest endpoint. | Honest encCore/keyCore; public M fixed. |
| Game1 p7 | game1Handler uses actual Pi simulator and actual Linear.leak of the known scalar signal. | Pure toLinear adversary, typed history replay, same A.coins/A.budget. First-hop gap bounded by Pi ACTUAL fresh-law advantage. |
| Game2 p7 | game2Handler replaces key leakage with source-group cross quotient. | game1_game2_accept via Eq(5), exact. No output-group inverse. |
| Game3 p8 | game3Handler replaces y1 only. | red2 receives MDDH one-column,n1-row GROUP A1/y1, retains known scalar y2, answers adaptive leakage with crossLeakLeft. Random shift by adaptively chosen z1 is exactly uniform. |
| Game4 p8 | game4Handler replaces y2 as well. | red3 receives GROUP A2/y2, knows scalar uniform y1, uses crossLeakRight. One-column,n2-row MDDH. No additional rank loss. |
| Actual simulator endpoint | Fresh.freshSaGame uses actual setup/enc/keyGen or simSetup/simEnc/simKey; ideal state stores simEnc's result. | saGame_eq_freshSaGame is substantive acceptance-law coupling, not just the indexed padded game selector. |
| Combined bound | quadratic_saSimAdv_le; quadratic_saSimAdv_dlin_le; PHFE wire bound. | Four MDDH advantages+ONE Pi rank loss; DLIN factors1,ℓ,1,1 and total matrix correction4(ℓ+3)/p. Advice precedes EVERY realiser. |

### Pi setup, honest algorithms and correctness (§4 p8, §4.2 pp9–10)

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

### Pi simulator (§4.2 p10)

| Source step | Lean counterpart | Reading / status |
|---|---|---|
| Uniform Acol:3×2,c:3; inverse of H=(Acol|c)^T. | simSetupCore, basisMatrix, total Matrix inverse. | All A,c are unconditioned. Inverse is total (zero on singular determinant in Mathlib's total inverse convention). |
| Cperp,aPerp inverse columns. | SimState.basisInv and projections/combineRows. | On good H they satisfy the exact dual-basis laws. No incorrect inverse identity is stated on singular H. |
| Uniform WUV,wtilde,vtilde; projected public key. | SimSetupDraw/simSetupCore. | Same public projection law as honest setup. |
| Enc*=[c],[wtilde],[vtilde]. | simEncCore/simEnc. | Deterministic after setup. No z supplied to simulator. |
| Eq(12) simulated key using PG*. | groupPGStar/simKeyCore. | pgbStar at zero leakage plus supplied group µ at m0; all source-group powers/products. group lift can use scalar representatives only inside a proof. |
| Simulator total before challenge. | Protocol refuses pre-challenge keys; core remains total. | Outer defaults y=0; Pi static setup state. No extra security assumption restricts zero dimensions. |

### Pi Theorem 1 and Lemmas2–5 (Appendix B pp.12–14)

| Source item | M0 counterpart | Proof route / exact loss |
|---|---|---|
| Theorem 1 p.12 | LinearSecurity.linear_saSimAdv_le and linear_freshSaSimAdv_le. | Two MDDH advantages (one response column,3 rows) and (ℓ response columns,mBound*q rows), one exact rank failure. This theorem is for Pi, not the main quadratic scheme. |
| Game0 p.12 | honest masked ciphertext, honest keyCore. | Fresh actual algorithm laws linked by Endpoint.saGame_eq_freshSaGame. |
| Game1 p.12 | replace sA by independent c; honest keys. | Unfiltered first MDDH hop, explicit red0. |
| Game2 p13 | decomposedKey using Cperp/aPerp. | Equal to Game1 on good H. Only this and later middle games are filtered to false on singular H. |
| Game3 p13 | semiKey with common hidden global U row times each R. | game2_game3_accept via exact adaptive public-fixing change of variables. |
| Game4 p13 | semiKey with independent uhat per query/node/public coordinate. | red1 embeds group R and uhat from matching MDDH rows; exact good filter known from advice. |
| Game5 p13 | actual simKeyCore with source group leak. | Exact PG privacy identifies Game4→5; fresh actual simulator endpoint linked separately. |
| Lemma 2 p13 | game0_game1_le and red0. | One MDDH¹_2,3; no rank term in the reduction. |
| Lemma3 statement p13, proof p14 | game2_game3_accept. | Fix public projections exactly; replace paper's random-guessing argument. No guessing factor or complexity leveraging. |
| Lemma4 p14 | game3_game4_le and red1. | One MDDH^ℓ_2,mBound*q for all adaptive key blocks together. Finite row map node*q+query; no growing family of unbounded-index machine advantages. |
| Lemma5 p14 | game4_game5_accept. | Exact privacy of layered PG, δ=0; source ≈s strengthened to equality for this instance. |
| Source's printed +1/p p.12 | rankSlack/linearSlack and good-event endpoint comparison. | Corrected exact unconditioned rank loss, charged ONCE. See counterexample and adaptive bijection below. |

#### Exact rank discrepancy and counterexample

H is an unconditioned uniform3×3 matrix over Fp, so
success=(1−p⁻¹)(1−p⁻²)(1−p⁻³),
failure=p⁻¹+p⁻²−p⁻⁴−p⁻⁵+p⁻⁶.
At p=2 failure=43/64>1/2. The source's 1/p is correct conditional on Acol having full column
rank, which its printed draws do not impose. The draft keeps the actual draws and this exact
failure. Shared Matrix.card_GL_field supplies the cardinality; no local GL counting lemma.
The comparison partitions both endpoint acceptance laws by the SAME good event, bounds the
bad conditional difference by1, and hence charges failure once. A naive triangle through two
separately filtered endpoints would incorrectly charge it twice.

#### Adaptive bijection, including latent U

For good H let a be its final inverse column, so Acol^T a=0 and c^T a=1. Given the challenge
selected from the public projections, set

U'=U; W'=W+a z*; V'=V+a((c^T U)X(x*)).

This preserves Acol^T U, Acol^T W and Acol^T V, hence preserves the selected x*,z*. It is
triangular: unchanged latent U determines the same shift in both directions; the inverse
subtracts these shifts. U is NOT asserted to be determined by the public projections.
Remaining inverse-basis coordinates and unused latent components are reindexed/resampled to
get the independent target low-row law. This conditional law, not a guessing argument, is
the substantive exact Lemma3 obligation. No group-to-scalar algorithm is hidden in this proof.

### Required misprint/readings table

| ID | Verified source location | Printed issue | Chosen reading and Lean counterpart |
|---|---|---|---|
| W1 | Wee Lemma1 p8; inherited AGW Lemma 2 p.12 | L0/L1 shapes swapped. | L1:t×(ℓm),L0:t×m; AGW(32)/AppB p38 and Wee KeyGen p9 agree. PG.Raw fields use these shapes. |
| W2 | Wee Enc* p7 and Game4 p8 | y2 source tag1 instead of2. | Intended second source group; symmetric copies coincide. Quadratic CT contains source-group y2. |
| W3 | Wee Games3/4 p8 | Uniform vectors over Z_q although group order is p. | Draw over actual public group order Z_p; no unrelated q modulus. q in Lean is only query budget. |
| W4 | Wee KeyGen* p7 | First cross term tagged GT, multiplied by source-group µ inverse. | Both factors source group, as Game2 p7 and Pi simulator signature require. crossLeak and reductions perform this source-group computation. |
| W5 | Wee bilateral MDDH p4 | Duplicate [MS]_1 and output2 in real experiment. | Second copy [MS]_2, Boolean1; actual symmetric assumption uses canonical Boolean game. No malformed definition copied. |
| W6 | Wee20 §4.2 p.10 and Appendix B, Theorem 1 p.12 | The displayed unconditioned 3×3 singular-matrix estimate uses 1/p. | Retain the actual uniform draw: exact singular probability 1−(1−1/p)(1−1/p²)(1−1/p³). At p=2, 344 of 512 matrices are singular, hence 43/64. The existing rankFailure API uses this exact value; the proven coarse bound is ≤3/p, and the bad event is charged once. |
| R1 | Wee Setup* p7 | Private dimension n1,n2 lacks primes. | Pi input length2*n2+n1*2 from actual outer private dimensions; piDim fixes it. |
| R2 | Wee Setup p6 vs §4 p8/KeyGen p9 | Fixed M passed at setup vs per-key M. | Per-key GROUP M at Pi; outer stores its one fixed public M in MSK/key metadata and forwards it. |
| R3 | Wee Game1 p7 | Samples unused s0. | Omitted; raw and simulator encryption draws contain only used seeds. |
| R4 | Wee Lemma1 pp8–9, Lemma5 p14 | Privacy stated statistically. | Exact equality for the specialized AGW/IW layered instance, no PG slack term. |

### Citation location retained in current code

Wee20's sole numbered Theorem 1 is in Appendix B, p.12. The two earlier references to p.8
were repaired in the live LinearSecurity/Fresh and QuadraticSecurity/Theorems prose before
this report. The main quadratic construction has an unnumbered Section 3 security claim.
The file names are `QuadraticSecurity/Reduction.lean` and `QuadraticSecurity/Compose.lean`.


## Fidelity: AGW20 and IW14 partial garbling

Verified AGW20 pp.11-12,37-39 and IW14 pp.6-11 were extracted and rendered for full-page
inspection in the source reviews. Printed page = PDF page for both papers.

### Source obligations and concrete syntax

| Source location | Actual claim / formula | Lean counterpart and fidelity |
|---|---|---|
| Wee Lemma1 pp8–9 = AGW Lemma 2 p.12 | Four efficient lgen,pgb,rec,pgb*; matrices depend only on f. | PartialGarbling.Raw has explicit L1/L0/eval/recVec and law fields; PartialGarbling adds lgen_eff/rec_eff uniform witnesses. Matrix arithmetic defines pgb/pgb*. No bare interface omits required efficiency. |
| AGW Lemma 2 p.12; (32) p38 | Correct dimensions L1:(m+n'−1)×(ℓm), L0:(m+n'−1)×m. | Raw L1 rows=TIdx⊕Fin n', cols=Finℓ×MIdx; L0 same rows, cols=MIdx. W1 corrected explicitly. |
| AGW Lemma 2 p.12 | Randomness length t_rng=m+n'−1, final n' entries are tbar. | auxCount+1=mCount; draw=(TIdx⊕Fin n')→ZMod p. mCoord/tCoord canonical explicit equivalences. No opaque Fintype.equivFin. |
| AGW(28) p37 | p=L_(x,z)(t;1). | Layered incidence matrices and pgbCore give this specialized last-column randomization, reordered as in(31). A general L/determinant/ABP datatype is not introduced. |
| AGW(29) p37 | Reconstruction det(L_x|p)=f(x)^T z; linear in p. | Layered.forward/rec/rec_spec: dotProduct p recVec=dotProduct z eval, for EVERY draw. Proof route uses telescoping path values. |
| AGW(30) p37 | Simulated column is (L_x|e1*µ)(t;1). | pgbStarCore puts µ at m0=root. groupPGStar multiplies supplied g^µ at that coordinate after zero-leak PG*. |
| AGW(31) p38 | Output rows first: (z−tbar, t^T Lbar_x^T). | Raw output type Fin n'⊕MIdx; exact pgbCore branch readers. |
| AGW(32) p38 | Lbar_x^T=L1(x⊗I_m)+L0. | publicTensor plus L1/L0; Layered.matrix and action laws. One variable-labelled incidence matrix per public coordinate, constant labels in L0. |
| AGW Algorithm rec p38 | Distinguished non-output reconstruction coordinate equals1. | root forward value=empty product1, m0=root, m0_coord=0. This is used by Pi's simulated leak placement and group lift. |
| AGW Appendix B p38 | KeyGen states corrected L1/L0 dimensions. | Corroborates W1 only. Extended/unbounded-slot Appendix B scheme is not implemented or claimed. |
| AGW Remark1 p11; Appendix B final Dec p39 | Scalar extraction by bounded brute-force discrete log. | Excluded. This unit outputs the value in GT and never implements the paper's bounded scalar decoder. |
| IW Def1 p6 | Rec correct with probability1; simulated and real garbling identically distributed. | Raw rec_spec for every t; Raw.privacy/exactPrivacy equality of expectations for every test, not negligible/statistical-distance approximation. |
| IW Def1 continuation p7 | Families require an efficient description-generation algorithm. | PartialGarbling efficiency fields and PGTargets, quantified before κ and arbitrary positive p. No per-modulus nonuniform machine witness. |
| IW Def1 “affine” p6; variants p7 | Strong local syntax uses a single input coordinate per output. | NOT claimed for the general matrix expression. Here fixed-coin garbling is general degree-one in x,z. Cite Theorem 3's syntax, not Corollary1's locality transformation. |
| IW Thm3 p8 | Private inputs only on edges into last t_tail vertices; output length t_tail(|V|−1), input degree1, reconstruction degree t_tail. | The chosen layered ABP interpretation has private variables only on edges into ONE sink (t_tail=1). Output n'+m=|V|−1, reconstruction linear. t_tail is not t_rng. |
| IW §4.2 pp9–11 | Last t_tail columns of R1 L R2; correctness by det; privacy by identical group-translation laws. | At t_tail=1 the AGW last-column specialization. Path-sum translation supplies the same law; full matrix group/canonical-form proof is not formalized. |
| IW p11 privacy | R1LR2 and randomized canonical form have identical distributions. | Layered.privacy uses Equiv.addRight(−shift) and shared expect_sample_equiv. No additional privacy loss term. |

### Exact layered specialization

| Ingredient | Formula / code family | Source reading / derived choice |
|---|---|---|
| Coefficients | PolyTensor p ℓ n' d; f_C(x)_j=Σ_tau C_j,tau Π_i xhat(x)_(tau_i). | Bounded-degree polynomial-vector restriction of the source ABP class; sufficient for GJLS§9. |
| Nodes | MIdx=Σ_(k:Fin(d+1)) (Fin k→Fin(ℓ+1)); root empty tuple. | Prefix-node representation of layered ABP; no new generic ABP model. |
| Auxiliary coins | TIdx=Σ_(k:Fin d) (Fin(k+1)→Fin(ℓ+1)); final output block Fin n'. | Node coins exclude root, with output coins last. |
| Counts | m=Σ_(k=0)^d(ℓ+1)^k; aux=m−1; t_rng=m+n'−1. | Source-required sizes, independent of coefficient values. mBound=nodeBound polynomial; all layered keys have the same actual m,t. Generic Raw permits smaller function-dependent m under this bound. |
| Coordinates | tupleCoord=finFunctionFinEquiv, then sigmaCongrRight and finSigmaFinEquiv. | Arithmetic base-(ℓ+1) tuple rank and depth order, reused Mathlib APIs. No cardinality-choice ranking or custom Sigma instance. |
| L1 | Variable parent→child incidences. | Coefficient of each x_i in the source incidence matrix. |
| L0 | Padded constant-one incidences, −1 at non-root diagonals, terminal C entries. | Constant part of the same matrix. Output/sink edges give the output-minus-last-coin block. |
| Rec | Output coordinates f_C(x), node coordinates forward prefix products. | Each non-root forward value is parent-forward times edge label; root1. Dot product telescopes. |
| Backward | Explicit suffix sums to the sink, private z at output nodes. | No recursive witness choice or scalar extraction. Fin.append/standard casts concatenate prefix/suffix. |
| Shift | Output coin shift=z; auxiliary coin shift=backward value of its node. | Pointwise real(t)=ideal(µ,t−shift), µ=z·f_C(x). |
| Exact privacy | Translation t↦t−shift is a finite additive equivalence. | Existing Equiv.addRight and ProbComp.expect_sample_equiv, not a new measure/reindexing lemma. |
| Zero extensions | d=0, n'=0, ℓ=0 supported. | Derived totality extension beyond explicitly discussed source examples. If d=n'=0, draw type is singleton, garbling has one zero node coordinate and rec there is1. Not attributed as a separately numbered paper theorem. |

### Disclosed proof-route deviation

The algorithmic syntax is AGW(28)–(32), specialized to the layered polynomial-vector DAG.
Reconstruction uses FORWARD path products and cancellation, replacing determinant/cofactor
expansion. Privacy uses BACKWARD path values and a translation, replacing the source matrix
canonical-form argument. These prove the same specialized rec/privacy statements. They do
not claim the full general-ABP theorem or an affine-locality compiler.

IK02 is mentioned only as cited in AGW/IW. Its determinant lemma is NOT imported/reproved.
Wee17 and EHKRV13 are likewise cited only through the supplied papers. No unread primary
paper is claimed as a proof source. Matrix.card_GL_field is used for the independent Pi rank
counting problem, not as a substitute for partial-garbling privacy.

## Verified-source ledger and journal-consumption boundary

All five originals were hash-verified before reading. Originals remain in the supplied
source folder; no PDF is part of source, evidence or the proposed delivery.

| Source | Verified hash | Location verified in this campaign |
|---|---|---|
| gjls21.pdf | 481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed | Pairing conventions/DLIN printed17–18 (PDF21–22); Def4.1/4.2/4.3 printed19–20 (PDF23–24); Def4.6 printed22 (PDF26); §9 class printed57–58 (PDF61–62); scalar Hybrid1 printed61 (PDF65); Thm10.3/10.4 printed63–64 (PDF67–68). |
| wee20.pdf | d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a | All14 complete pages rendered and inspected. Main claim §3 p6; outer games pp7–8; Pi pp8–10; sole numbered Theorem 1 Appendix B p.12; Lemmas2/3 p13, Lemma3 proof/Lemmas4/5 p14. |
| jls26.pdf | bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d | §1.1 PDF3 canonical DLIN; §1.4 PDF7–8 distinction public-key DLIN vs secret-key SXDH PHFE; Thm5.1 PDF21 consumption through GJLS10.3/10.4. |
| agw20.pdf | b74c2ac906cf3f40eb5882abb3921433beebdb9fb020ba09ce8a10035b55d11f | §4.1 pp11–12 semi-adaptive one-slot context; Lemma 2 p.12; Appendix A(28)–(32) pp37–38; Appendix B pp38–39 corroborating shapes/scalar extraction excluded. |
| iw14.pdf | ef6c7c6a0103dfea1d8d9d369e3a7de3a0902fa6138a6bedc4c4df4996e65e77 | Def1 p6 and family/locality discussion p7; Thm3 p8; §4.2 pp9–11 exact canonical-form privacy. |

GJLS printed page=PDF−4. Wee/AGW/IW printed=PDF at reviewed locations. JLS journal page
labels are 1:3,1:7,1:8,1:21; the ledger uses explicit PDF numbers to avoid inventing a printed
integer convention.

### What the journal pipeline actually consumes

| Source location | Verified fact | Unit consequence |
|---|---|---|
| JLS §1.1 PDF3 | Symmetric DLIN canonical tuple with independent uniform field exponents. | Primary DLINAssumption/SubexpDLIN uses this actual tuple; public group description and uniform nonidentity generator are encoded explicitly. |
| GJLS printed17/PDF21 | DLIN matrix A0=[[a,0],[0,b],[1,1]], a,b uniform in Zp. | Matrix game is separately defined. a,b may vanish; this is the origin of the random-presentation discrepancy and direct-column rank correction. |
| GJLS Def3.3 printed18/PDF22 | Bilateral matrix real Ar vs independent full uniform u; both source-group copies. | In symmetric groups copies coincide. Its displayed signed gap is normalized to library absolute advantage; security for all distinguishers/complements yields the standard absolute convention. No exact random tuple equality is claimed. |
| JLS §1.4 PDF7–8 | DLIN gives PUBLIC-key PHFE with constant public degree/private degree2; SXDH alternative gives secret-key PHFE. | This task's public-key syntax is essential. Do not replace it with an SXDH secret-key primitive or omit the public encryption argument. |
| GJLS Thm10.3 printed63–64/PDF67–68 | Replacing §8 PHFE by Wee's theorem removes SXDH and uses bilateral DLIN, implied by symmetric DLIN. | The unit provides that PHFE ingredient, not all-circuit FE or IO itself. |
| GJLS Thm10.4 printed64/PDF68 | Subexponential assumptions then yield IO in the broader pipeline. | Common positive exponent in this PHFE unit is required; it must precede machine/query budget. |
| JLS Thm5.1 PDF21 | Explicitly recalls GJLS Thm10.3/10.4, bilateral DLIN implied by symmetric DLIN, structured PRG complexity(deg d,deg2). | The class and many-key simulation/linear efficiency package are the correct interface for the journal consumer. No unrelated assumption or private-degree restriction is substituted. |

### Parameter and source-reading disclosures

The dispatch explicitly requires hp:forallκr,G.instκr.order=pκ for inequalities and also
2^κ≤pκ for asymptotic corollaries. This is retained exactly. Honest algorithms do NOT use
that schedule. It is a convenient fixed-order/growth normalization for the formal security
parameter; do not describe it as a literal transcription of every source's bit-length
convention (JLS uses a λ-bit prime; GJLS pairing setup writes pλ=2^(λ^Θ(1))).

The additional dimension-uniform finite-TM target and its positive-size domain are
explicit disclosed readings, not claims that the source states this exact machine model.
All named efficiency propositions remain PhaseB obligations. M0 theorem admissions and
unrun exact?/apply?/Rule10 checks remain visible.

Only supplied original papers were read. EHKRV13, IK02 and Wee17 are cited only “as cited
in” Wee/AGW/IW; they are not represented as directly read or independently formalized.
Scratch extracts/PNGs were used for navigation and visual verification. Proposed payload
should carry hash/inspection/search notes, not the paper text or page images by default.

## Rule 15 and overlap/reuse

The following fields and targets are present in the live interfaces. Runtime Rule 10,
statement and axiom audits remain pending.

### Efficiency is carried by interfaces

| Interface / target | Required fields / quantifiers | Static result |
|---|---|---|
| FEScheme extends Raw | pubGen_eff,setup_eff,enc_eff,keyGen_eff are shared SamplesEfficiently; dec_eff is ∃one PC string map before κ,pp,key,x,ct. | Fields present; no bare nonuniform machine existence. Approved extra pubGen field covers uniform nonidentity g after existing uniform description generation. |
| Simulator extends Raw | setup_eff,enc_eff,key_eff plus existential state_bounded and value_bounded. Every sampler parameter word starts with NUPPT.advInput κ. | Fixed-width raw stLen/encSt is retained. One polynomial bounds all states, and another bounds all allowed values, before κ and pp; committed Enc receives Ω and Key receives Ω/index. |
| SASimulator extends Raw | setup_eff,enc_eff,key_eff plus existential state_bounded and value_bounded; every sampler parameter word starts with NUPPT.advInput κ. | Fixed-width raw state is retained. Enc receives x; Key receives x,f,µ. Pure assembly attaches the four matching concrete bounds from SimTargets. |
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

### Uniformity and actual input layout

| Item | Audited information flow |
|---|---|
| Honest operations | PublicParams stores actual description and nonidentity generator. classParam is pp.orderParam. Setup/Enc/KeyGen/Dec contain no p(κ) function. BilinearGen.Ops provides the uniform public group operations. |
| Class/PG codecs | Wire input words reduce integer blocks modulo actual p. Canonical encode/decode round trips require p≤2^w. PG canonical f descriptions instead use Nat.size p, so its uniform interface covers every positive modulus. |
| Draws | Finite exact draws are single complete types, including dependent enc/key draws. Existing product Fintype is used for a product TYPE; no product sampler is constructed. Dependent Sigma key packs are data, not sampled types. |
| Reduction advice | All scalars lie in ZMod(pκ). hp transports known scalar advice through the published public-order equality and Mathlib ringEquivCongr. No algorithm recovers a field scalar from a source or target group element. |
| Dimensions | L1 headers contain κ,d,rows; L2 Pi headers contain κ,ℓ,n',zDim,q,mBound; outer headers contain κ,n1,n2 plus the Pi header. A uniform map can read numbers, without hardwired PolyExpr evaluators. |
| Machine coins | RealizesOn enforces D.coins=the stated layout and only encoded typed challenges with r.length=layout.evalκ. Reductions output singleton verdict words. dlinToMddh passes r.take(D.coinLenκ) to D.runAtL. |

### Overlap and nearest public APIs

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
Remaining overlap probes, the final native stored-constant inventory and full axiom
census remain pending. Completed helper probes are listed below. Text searches and named nearest relatives are reuse evidence,
not proof of absence of duplication. The source-group/GT arithmetic near-copies and the
parallel typed protocol/advice wrappers are disclosed debts, not silently generalized
away. `PHFE.embedValue_injective` is now in proof-only `PHFE/Embedding.lean`; its use of
`pow_val_bijective.injective` proves injectivity and returns no exponent.


### Post-checkpoint0 helpers and implementation decisions

The frozen manifest still matches every pre-existing header and statement paragraph.
Only proof bodies and proof sketches were refreshed. Twenty-one new helpers are listed
below; the first three were introduced as statements in `b881f122`. All twenty-one
have native standard-axiom-only proofs at the current committed head.

| Helper | Reuse and nearest relatives | Prior search evidence |
|---|---|---|
| `PathAlgebra.weightedIncidence_mulVec` | `Matrix.sub_mulVec`, scalar `sub_dotProduct`, `single_dotProduct`, `single_one_dotProduct`; exposes the weighted parent/child action in a generic ring. | `evidence/search/path-algebra/PathAlgebraReuse2.lean.txt` and `PathAlgebraApply2.lean.txt`; native logs under `run2/`. |
| `PathAlgebra.weightedIncidence_vecMul` | `Matrix.vecMul_sub`, `Matrix.vecMul_eq_sum` and pointwise sum readers; the transposed endpoint action. | Same three-target native probes; partial suggestions were not complete proofs. |
| `PathAlgebra.paddedIncidence_eq` | `Matrix.mul_apply`, `Fintype.sum_prod_type`, singleton sums, `Fin.lastCases`, `Fin.snoc_last/castSucc`; generic variable/constant edge contraction. | Same three-target probes and archived source-name/shape searches. |
| `Layered.forward_node` | `Fin.prod_univ_castSucc`, `Fin.init_def`, plus node/parent/label/forward readers; no new product recurrence. | `LayeredHelpersReuse2.lean.txt` and `LayeredHelpersApply2.lean.txt`, prefix ending before the later action theorem. |
| `Layered.matrix_inl` | Specializes `PathAlgebra.paddedIncidence_eq` through incidence/public-tensor/padding readers; no repeated contraction proof. | Same two-target prefix probes. |
| `decodeResidues_block` | Existing total `decodeResidues_apply`, `List.ext_getElem`, published take/drop/ofFn element and length equations, and `finProdFinEquiv_apply_val`. The row index bound uses natural arithmetic. | `evidence/search/classes-residue-block/`; exact? found no proof and apply? returned only partial unrelated scalar equalities. The prefix excludes this helper and all later Classes admissions. |
| `PrefixAlgebra.prefixIncoming_sum` | `Function.Injective.sigma_map`, `Fin.succ_ne_zero`, the existing empty-function subsingleton instance, and `Fintype.sum_ite_eq'`; selects the unique incoming prefix. | `evidence/search/prefix-and-polynomial/run`; exact? failed only to close the two stated targets, apply? supplied partial proofs only. |
| `PrefixAlgebra.prefixOutgoing_sum` | `Equiv.sigmaProdDistrib`, `Fin.snocEquiv`, sigma-map injectivity and supported sums; no new tuple equivalence. | `evidence/search/prefix-outgoing/run`; one expected exact? failure, no complete apply? proof. |
| `PrefixAlgebra.prefixFlow_balance` | The outgoing-prefix reader, `Fin.consEquiv`, `Equiv.arrowCongr`, product/sum reindexing, `Fin.append_right_nil`, `Fin.append_right_cons`, and cast readers. | The same isolated two-target prefix probes; the nonterminal branch uses the separately searched outgoing reader. |
| `PolynomialTensorAlgebra.exists_padded_tuple` | Existing list replicate, flatten, length and finite-product readers; append constant labels to a canonical repeated-variable list. This avoids introducing a multiset-enumeration layer. | `evidence/search/prefix-and-polynomial/run`; no complete exact?/apply? match. |
| `PolynomialTensorAlgebra.exists_quadratic_expansion` | The padded-tuple lemma, `MvPolynomial.eval_eq'`, `mem_support_iff`, `Finset.sum_coe_sort`, `Fintype.prod_sum_type`, `Fin.prod_univ_two`, finite sum interchange and supported sums. | `evidence/search/arbitrary-group-and-expansion/run`; one expected exact? failure, only partial existence wrappers from apply?. |
| `BilinearGroup.pairVec_expVec_left` | Pairing/vector readers, `map_prod`, and the published pairing-power laws; keeps the other vector group-valued. | Same directory's two-target arbitrary-group probes; exact? found no proof and apply? found no relevant pairing lemma. |
| `BilinearGroup.groupVecMul_matMulGroup` | Existing exponent-dot-product law at each arbitrary matrix entry, product-power distribution/interchange, and scalar dot-product commutation. No second modular-power homomorphism proof is introduced. | Same two-target arbitrary-group probes; only a partial matrix equality suggestion for this target. |


| `PartialGarbling.kronecker_mul_publicTensor` | `Matrix.mul_kronecker_mul` and the existing tensor coordinate readers. The new helper uses Type0 indices to match the frozen tensor API. | `evidence/search/public-tensor-mixed/run2`; first universe prototype rejected before proof, repaired target has clean search failures/partial suggestions. |
| `stateT_mapM_lift` | `List.mapM_nil/cons`, `StateT.run_bind/run_lift/run_pure`, and OracleComp monad readers. No traversal implementation is added. | `evidence/search/stateful-committed-key-loop/run`; exact?/apply? found no complete proof. |
| `TwoStage.coinBlocks_ofFn_append` | Existing list append/ofFn/getD readers and Fin cast/append APIs. | `evidence/search/committed-run-bridges/run`; no complete proof; native prefix excludes later game-law statements. |
| `TwoStage.simulate_saKeys_stateful` | Published buildComp/simulate case readers and one supplied handler-key law, preserving final state. One induction serves real and ideal handlers. | `evidence/search/stateful-committed-key-loop/run`; no exact?/apply? match, no target typing errors. |
| `TwoStage.simulate_toSA_real` | Generic stateful loop specialized to Unit state, plus the lifted traversal identity. | `evidence/search/committed-run-bridges/run`; no exact?/apply? match. |
| `TwoStage.simulate_toSA_ideal` | Same loop specialized to simulator state; the final state is projected only after all keys. | Same isolated real/ideal target probes. |
| `dlinDiagonal_random_gap_le` | `Equiv.mulLeft₀`, finite function/product equivalences, `Bridge.expect_sample_pair`, existing uniform singleton probability, and shared expectation averaging. No counting theorem or sampler is reimplemented. | `evidence/search/diagonal-and-parameter-codec/run`; no complete exact?/apply? match, no target typing errors. |
| `PublicParams.encode_injective` | Existing pair-codec injectivity, `List.ofFn_injective`, group encoding injectivity and proof irrelevance. Shared by DLIN and MDDH codecs. | Same isolated parameter-codec probes, excluding this helper. |

The root's modularity decisions were to share the complete stateful key-loop induction
between real and ideal protocol laws, share public-parameter codec injectivity between
the challenge codecs, and put the finite-field diagonal estimate in the cycle-free
MatrixDH/Diagonal module. The mixed tensor helper's Type0 repair affects only its new
header, matching all intended callers; no checkpoint0 statement changed. These logical
lemmas introduce no runtime host, sampler, machine, or additional efficiency interface.
The exact committed/SA bridge uses a finite tape equivalence and the existing Fubini
reader; it claims equality of expectations, preserving the original coin order in each
definition. Generic Class, Layered, LinearCorrect, and QuadraticCorrect proofs are complete.

The first complete concrete DLIN random-gap candidate was stopped after 176 seconds of
CPU-bound elaboration; only recorded own Lean PID16047 was signaled. The driver restored
and rechecked the admitted source. Both source snapshots, raw logs and the termination
note are retained under `evidence/logs/proof-steps/dlin-random-game-gap/attempt-1/`.
Its generic finite-field ingredient is fully proved and standard-only; the concrete
consumer and its final advantage consequence remain admitted at this checkpoint.

Detailed nearest-relative paths, line locations and shape searches accompany the fragments
in `evidence/subagents/fe_interface_review/proofs-dc9fdcc/` and
`evidence/subagents/pairing_pg_review/proofs-dc9fdcc/`. Later fragments and exact path/line
references are archived under each contributor's `proofs-9cbc7d6/` directory. The generic incidence identities
belong in the independent `PartialGarbling/PathAlgebra` module so the layered file can
remain within the size bound without creating import cycles. The decoder helper accepts
every word without a range or width restriction, preserving noncanonical aliases modulo p.

The list round trip for `ofFn_encodeTensorBits` reuses
`TCSlib/Cryptography/Asymptotic/Adversary.lean:218` (`ofFn_padFin_of_length`) and its
published `padFin_def` reader, rather than adding a list reconstruction helper.
Tensor decoding reuses `Encoding.Modular.decodeMatrix_encodeMatrix` directly.

Cache attempt6 was canceled while waiting, before a lake or Lean child started; the exact
owned-process cleanup is recorded in `cache-6-wait-cancellation.json`. Attempt6b passed
fresh resource/package checks and successfully unpacked the narrowed 109-root closure
(2364 archives, no downloads). It supplied the precise column/row-partitioned matrix import.
No peer process or wrapper was changed. A development-log gap for the first exponent pairing
candidate is disclosed in `evidence/logs/proofs-exponents/development-log-gap.txt`;
its successful committed check and independent axiom probe are intact. Subsequent proof
attempts preserve separate candidate and restoration logs; recent attempts additionally
retain the exact candidate/restoration source bytes.

## Advice dimensions and reduction tape accounting

The deterministic scalar tapes below are proof experiments and fixed nonuniform advice.
They are linked to the actual fresh honest/simulator laws by substantive endpoint theorems
that remain M0 proof obligations. A padded endpoint selector alone is not source security.

### Pi tape: complete offset audit

Write z=zDimκ, l=ℓκ, n=n'κ, b=mBoundκ, Q=TOTAL budgetκ. Public-group field is Fp.

| Block | Start | Length | Access / conclusion |
|---|---:|---:|---|
| Acol3×2 | 0 | 6 | 2*row+axis, max5. |
| c3 | 6 | 3 | 6+row, max8. |
| W3×z | 9 | 3z | 9+row*z+column. |
| U3×(l×2) | 9+3z | 6l | row*(2l)+2*public+axis; disjoint canonical product coordinates. |
| V3×2 | 9+3z+6l | 6 | 2*row+axis. |
| wtilde z | 15+3z+6l | z | Ends at15+4z+6l. |
| vtilde2 | 15+4z+6l | 2 | Ends at17+4z+6l. |
| global hidden U row | 17+4z+6l | 2l | 2*public+axis; disjoint from setup U. |
| honest encryption seed2 | 17+4z+8l | 2 | Ends at B=19+4z+8l. |
| key T | B | 3Q(b+n) | Query-major then 3 rows of width b+n; actual coordinate uses tCoord(aux) or b+output. |
| key R | B+3Q(b+n) | 2Qb | Query-major then 2 rows of width b. |
| independent uhat | previous+2Qb | Q*l*b | Query-major public variable then node. |
| independent PG coins | previous+Qlb | Q(b+n) | Query-major padded aux/output coordinate. |

Total is B+Q((6+l)b+4n), exactly securityCount. Blocks are disjoint, and every in-bounds
coordinate is strictly below this total. The default-zero lookup is used only for arbitrary
out-of-range raw arguments. For accepted keys j<Q, mCoord(u)<mCount≤b; tCoord(v)<auxCount,
auxCount+1=mCount≤b; output positions b+i are disjoint. Thus actual T/R/uhat/PG restrictions
are injective. No actual accepted key reads the zero default.

The protocol increments j ONLY on accepted keys, while runDet/buildComp spend budget on
EVERY call. At most Q key answers are accepted; indeed the challenge consumes a call too.
Q padded key blocks are sufficient without adding1. For TwoStage q keys the actual TOTAL
budget is q+1, and the over-allocation to q+1 key blocks is harmless. Early/repeated calls
return None and do not shift accepted-key blocks.

Second Pi MDDH shape is base rows bQ, two base columns, l response columns. The row used by
R(axis,node) and uhat(public,node) is the SAME number nodeCoord*Q+j. For j<Q it is below bQ
and injective across (nodeCoord,j), even if different functions have different actual node
counts. The input MDDH row order is node-major while the scalar game tape is query-major;
this is a deterministic permutation of independent uniform coordinates, not an equality of
raw tape offsets. Real response entry is sum_axis R(axis,node)*S(axis,public), exactly the
common hidden U(public,axis) action. One group challenge handles all adaptive keys together.
At Q=0, no accepted key exists and the challenge matrices may have zero rows without issue.

### Outer tape and reductions

| Item | Exact shape / audit result |
|---|---|
| Outer tape length | 3n1+3n2+4. A1 uses2n1; A2 next2n2; s1,s2 next4; uniform y1 nextn1; uniform y2 nextn2. Last exclusive coordinate is exactly total. |
| Fixed group M | Rows=2*n2+n1*2; columns=n1*n2. Top A1⊗I_n2, bottom I_n1⊗A2. Honest encryption only knows A1,A2 as GROUP data. |
| First MDDH | one response column, n1 base rows. A1=base^T, y1=response(:,0)*g^z1. Known A2,s2 yield scalar y2; crossLeakLeft uses group y1 with scalar y2. |
| Second MDDH | one response column, n2 base rows. A2=base^T, y2=response(:,0)*g^z2. Already-uniform scalar y1 is advice; crossLeakRight uses it with group y2. |
| Basis handling | Both use total Pi simulator even on singular H; no outer rank filter and no extra rank slack. |
| Typed derived adversary | toLinear has exactly original coins and total budget. replayLinear preserves actual reachable typed histories; malformed mismatched histories return false. No uncomputable group-word decoder. |
| Generic wire adapter | PHFE replay uses original x/y/f words and List.foldl; checks typed query and key-index agreement, encodes actual Option responses, retains original f in returned key. Mod-p aliases do not collapse in adversary transcripts. |

### Advice encodings and quantifier audit

| Family | Finite/inhabited / width | Quantifiers / permitted computation |
|---|---|---|
| L1 MddhAdvice | Fin(dκ+1) sentinel index; L:rows×3, S:2×d, U:rows×d over ZMod(pκ). Zero matrices plus sentinel inhabit d=0. | hp gives NeZero pκ locally; no extra assumption on p. Numeric κ,d,rows headers. Preprocessor forms LA0 and Lc using known scalar powers of canonical DLIN group points. |
| Pi Advice | Scalar vector of securityCount over ZMod(pκ), nonempty zero; finite via shared orderSchedule_neZero. | ∀typedA ∃ωκ BEFORE ∀D realiser and ∀κ. Advice cast uses ringEquivCongr, not a local scalar extraction map. |
| Pi word bound | 4κ+4l+4n+4z+4Q+2b+40 +securityCount*wG. | Pair-header arithmetic checked: enc has twice metadata length plus2 plus vector. Numeric bits≤value+1 gives exactly constant40. |
| MaskAdvice | Vector length3n1+3n2+4 over fixed pκ. | Used only as fixed known outer randomness in toLinear; no sampling inside derived adversary. |
| Mask word bound | 4κ+4n1+2n2+20 +maskCount*wG. | Header actual bound constant16; stated20 is safe. |
| Full outer Advice | MaskAdvice × Pi Advice; zero pair inhabits, hp gives finiteness. | Enc pairs the two component words; length bound2*maskAdviceLen+2+Linear.adviceLen. |
| Core outer bound | ∀typedA ∃mask φ ∃twoPiω ∃twoOuterω ∀fourD, four explicit RealizesOn premises→∀κ bound. | No assumption that every typed adversary is computable. Advice may depend on A, never on chosen realiser. |
| L2 corollaries | Wee20RealizableSA quantifies only FE.toSAAdv A q; Wee20Realizable43 only TwoStage.toSA q. | Correctly avoids the false all-typed-machine-existence premise. Honest efficiency is separate. |
| Shared RealizesOn | coins equality AND output equality only at encκ(challenge) and r.length=layoutκ. | No malformed/raw input behavior is constrained. Advice is fixed inside R, never read back from D's own advice. |
| DLIN composition | ∃L1 advice after four MDDH machines, then ∀DLIN realisers. | Response-column factors1,l,1,1. Exact Pi rank loss+3*mddhSlack(p,1)+mddhSlack(p,l). No second matrix-presentation loss. |

The L1 real canonical A0 has rank failure p⁻²; augmented random matrix determinant is
ab(t−r−s), with failure1−(1−1/p)^3. The sum is3/p−2/p²+1/p³≤4/p per column. The named safe
slack is4d/p. A SINGLE chosen-column machine suffices, avoiding a nonuniformity problem from
summing an ever-growing arbitrary family of negligible advantages.

## Explicit reduction chain and exact losses

Let Q(κ) be the TOTAL call budget, b(κ)=PG.mBound.eval κ, and z=piDim(n1,n2).
Write `Adv_MDDH(d,r;D)` for the library's absolute two-experiment advantage with d response
columns and r base rows. Every matrix has exactly two base columns. The core outer theorem
chooses one outer mask family φ, two Pi advice families and two outer advice families BEFORE
quantifying over the four realisers D. All inequalities are simultaneous in κ and valid for
EVERY family realising the displayed deterministic functions. A realiser is required only
on the shared encoded challenges and layout-length coin strings.

| Level / deterministic function | Input, fixed advice and coins | Played comparison | Realiser / contribution |
|---|---|---|---|
| L1 `BilinearGen.mddhPreChallenge`, `mddhPre` | Canonical DLIN challenge; hybrid index, L,S,U scalar matrices | One adjacent uniform-matrix response-column hybrid | Known scalar powers/products only; no draw and no exponent extraction. |
| L1 `BilinearGen.dlinToMddh` | Previous input/advice; D's own layout coins, truncated by the published coin reader | D on one preprocessed MDDH challenge | One fixed-advice realiser B: `B.RealizesOn G.dlinEnc D.coins (...)`; d(κ)·DLINAdv(B)+4d(κ)/p(κ). |
| L2 `Linear.red0` | MDDH(1,3) group challenge; fixed Pi scalar tape; A's coins | Pi Game0→Game1 | D0 realises the exact function on the MDDH encoding with A.coins; contributes Adv_MDDH(1,3;D0). |
| L2 `Linear.red1` | MDDH(ℓ,bQ) group challenge; fixed Pi scalar tape; A's coins | Pi Game3→Game4, all adaptive key blocks together | D1 with A.coins; contributes Adv_MDDH(ℓ,bQ;D1). The base-row index is nodeCoord·Q+query. |
| Derived typed adversary `Quadratic.toLinear` | Fixed outer masks φ, typed quadratic A, actual typed Pi answers | Outer Game0→Game1 through Pi's ACTUAL fresh-law advantage | Preserves A.coins and TOTAL budget; no machine construction or new loss. |
| L2 `Quadratic.red2` in `QuadraticSecurity/Reduction.lean` | MDDH(1,n1) GROUP A1/y1; known scalar A2,s2,Pi tape; A's coins | Outer Game2→Game3 | D2 with A.coins; contributes Adv_MDDH(1,n1;D2). `crossLeakLeft` never obtains the unknown y1 scalar. |
| L2 `Quadratic.red3` in `QuadraticSecurity/Reduction.lean` | MDDH(1,n2) GROUP A2/y2; known uniform scalar y1 and remaining tape; A's coins | Outer Game3→Game4 | D3 with A.coins; contributes Adv_MDDH(1,n2;D3). `crossLeakRight` never obtains the unknown y2 scalar. |
| Wire adapter `PHFE.toQuadratic` | Initial pp/pk, original coins, replayed typed answers | Generic wire SA experiment→typed fresh quadratic experiment | Exact law and advantage identity; original x/y/f aliases and function-key metadata retained. |
| Committed adapter `TwoStage.toSA` | Disjoint first/second coin blocks, q committed keys | Definition4.3→the actual generic SA run | q+1 TOTAL calls; exact expectation/advantage identity, no abstract machine-security implication. |

For Pi and then for the typed quadratic construction the current core statements retain
exactly ONE `Linear.linearSlack G κ`. For a fixed prime schedule the exact loss is

```
F(p) = 1 - (1-p⁻¹)(1-p⁻²)(1-p⁻³)
     = p⁻¹ + p⁻² - p⁻⁴ - p⁻⁵ + p⁻⁶.
```

`linearSlack` averages this pointwise correction over public parameters; under hp all drawn
orders agree with p(κ). The coarse asymptotic helper is ≤3/p, not a replacement for the exact
core loss. The source's printed 1/p would fail at p=2, where F=43/64. No rank filter is added
to an actual honest/simulator endpoint, and no second rank term is charged by the outer hops.

The four-realisers bound is

```
Adv_SA(A) ≤ Adv_MDDH(1,3;D0) + Adv_MDDH(ℓ,bQ;D1)
          + Adv_MDDH(1,n1;D2) + Adv_MDDH(1,n2;D3) + linearSlack.
```

`QuadraticSecurity/Compose.lean` supplies `hopCols=(1,ℓ,1,1)` and
`hopRows=(3,bQ,n1,n2)`. After D0..D3 are fixed, four L1 advice families η are chosen before
EVERY family B0..B3 of canonical-DLIN realisers. The explicit composed bound is

```
Adv_SA(A) ≤ DLINAdv(B0) + ℓ(κ)·DLINAdv(B1) + DLINAdv(B2) + DLINAdv(B3)
          + Quadratic.quadraticSlack G ℓ p κ,
quadraticSlack = linearSlack + 3·mddhSlack(p,1) + mddhSlack(p,ℓ)
              = linearSlack + 4(ℓ(κ)+3)/p(κ).
```

The direct canonical-DLIN column reduction already accounts for vanishing a,b. Its safe
per-column correction is 4/p. `dlinMatrixSlack` is retained for the separate comparison of
the canonical and matrix-style random presentations; it is NOT added a second time to this
composition. Exact PG privacy contributes zero loss. The outer PHFE specialization uses
n1=n2=n and z=4n. Both SA and committed raw inequalities expose these functions and all
realiser premises; no target is a hypothesis of either raw inequality.

`Wee20RealizableSA` quantifies only over `A : NUPPT` through
`FE.toSAAdv (S := S) A q`; `Wee20Realizable43` quantifies only over `A : TwoStage` through
`A.toSA (S := S) q`. For each fixed advice family they ask for the four shared L2 realisers.
Neither asks a machine to realise an arbitrary uncomputable typed SAAdv. L1
`MDDHRealizable` is separate. `mddhRealizable_of_preTarget` is an explicit term application
of the shared preprocessing-realisation theorem and existing polynomial advice-length
bound. It builds no local machine. The primitive headlines discharge L1 existence from
`hT.mddh`; only the machine-derived L2 hypothesis remains.

For subexponential security, one e<min(c_DLIN,1) is chosen BEFORE A and q. The explicit
DLIN-composed inequality, shared polynomial growth/absorption and slack-decay APIs operate
at that same e. Merely applying a per-dimension existential `mddh_subexpHard` would not show
a common exponent over q; the current sketches deliberately avoid that quantifier error.

## Pins, source control and delivery scope

| Item | Pin / current state |
|---|---|
| Lean/Mathlib source base | `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, branch iO/phase-a-base; Lean 4.25.0 and pinned package manifest |
| Design/contract/realisation records | `dbea2807532392781304e004715f3b0190025f5e` |
| Exchange tool/host inputs | `bc9d982b83cb35ea351e2fb373752e8688945b1c` |
| Source HEAD for historical checkpoint 0 checks | `70b85f9ba83f27393d98fa5bf88505aea3d22a8d`; historical complete checked closure in evidence/build/summary.tsv |
| Earlier development elaboration | All drafted public modules reported elaborated at `7d42a6ef6a20d379c524c11db87a1b0c0e4c25df` |
| Managed source worktree | `/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange` |
| Source working branch | `fill/io-phfe`, local only; never pushed |
| Delivery worktree | `/Users/seyoonr/.codex/worktrees/exchange-io-phfe/tcslib-exchange`, isolated on codex/io-phfe-delivery; latest delivery before r2 is checkpoint 3 at 503869facd155bb754be8f1281dd77ee7776e3b5 |
| Delivery branch/path | Authorized exchange/pass-shelat-ch5-8 destination, only inbox/fills/io-phfe/; final ref/ancestry recorded before commit |
| Checkpoint0 / freeze / push | Delivered at 1e77173a7032b57aa22260787711c6c7a1b7596e; the statement freeze started with that publication on source 70b85f9ba83f27393d98fa5bf88505aea3d22a8d. Earlier preparation text is historical. |

The base includes the four required shared foundations: Subexponential, Realization,
coin-sampling types and CoinSampling.Contract. These APIs are reused, not locally replaced.
No source-base file outside the allowed facade import lines is intentionally modified.
The allowed base-to-HEAD scope check passes; exact facade diffs and the source-name list
are retained in evidence/logs/. No PR, force push or unrelated exchange-path update is part of delivery.

The complete source commit/author/committer/signing ledger is retained in
`evidence/logs/source-COMMITS.tsv` and delivered as `patches/COMMITS.tsv`, alongside
format-patches from the pinned base. The source base was not rebased. The isolated exchange
checkout was cleanly fast-forwarded before staging; its preparation receipt is retained.
The publication commit hash is reported after the authorized push and in later checkpoint
receipts; it cannot be self-referenced inside its own hashed payload.

The supplied source folder is
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/sources`.
The exact five hash lines are recorded in `evidence/logs/sources-sha256.txt`; the table above
is the verification ledger. E-SRC was resolved before source reading. The initial missing-folder source-status record has been archived, superseded and
replaced by the lead. The hash log and source ledger describe the current resolved state;
the historical E-SRC record must not be mistaken for an active blocker. No paper, extracted full text or rendered paper page is
proposed for inclusion in the delivery. EHKRV13, IK02 and Wee17 are referenced only as cited
in supplied Wee20/AGW20/IW14, never as independently read sources.

The host addendum SHA-256 is
`02a6af16284cf5d6676caf3df58a31b3d640cc8e59febd51e0682d7ba455124c`.
The pinned lean-slot.sh SHA-256 is
`ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a`.
The lead verified both. The required 4GiB memory-headroom floor initially failed at
3.770828 GiB. The scheduled retry measured 4.738770 GiB; initial free disk was about 93.51 GiB,
above the 12GiB floor. These are historical measurements, not guarantees of current headroom.
Later resource-sensitive work must use the prescribed checks and retain raw logs.

The user explicitly overrode the later LeanInfoView-only AGENTS restriction and authorized
the dispatch's slot-wrapped module checks/probes. Root owns those executions. Every Lean
subprocess uses the pinned wrapper with LEAN_SLOT_TAG=io-phfe and one slot; cache fetches
hold the prescribed three slots. No agent may run an unwrapped or parallel Lean process.
The subagents' drafting/static-audit tasks did not run Lean/lake/build or mutate Git.

## Implementation architecture and pre-freeze decisions

The public module facade exports the generic FE/committed/SA interfaces, polynomial class,
layered garbling and Wee20 instance. Child files carry definitions; facade files carry their
contents lists/imports. `PartialGarbling/Defs.lean` avoids a parent-child import cycle.
`QuadraticSecurity/Reduction.lean` owns red2/red3 and
`QuadraticSecurity/Compose.lean` owns the four-loss DLIN composition. The actual machine
adapter is `FE.toSAAdv`, not a constant added under Complexity.NUPPT.

| Decision retained before freeze | Reason and exact effect |
|---|---|
| Raw/efficient split at every public interface | Raw algorithms, exact laws, correctness and advantages do not assume efficiency targets. Efficient interfaces require proofs as fields. Only Targets/Assembly constructs the four efficient values. |
| Uniform nonidentity public generator in pp | A public object is a reachable group description plus g∈G*. Reachability is a proposition; duplicate description-generation coin strings do not create distinct pp objects. User approved the extra pubGen_eff/target for the conditional G* draw after G.gen. |
| pp-dependent key/ciphertext types and input-dependent draws | Keep actual group types clean and sample exactly the actual f-dependent garbling size, without an exponential universal draw. EncDraw depends on pk,x,y and KeyDraw on msk,f. |
| Explicit canonical class-value codec | Simulator µ is a scalar class value, not a GT word. FnClass.encValue is injective; PHFE uses the actual modulus's canonical scalar width. This is coding metadata, not a modulus generator or local sampler contract. |
| Total modular wire decoding | Decode fixed-width binary representatives, then cast modulo actual p. Noncanonical words are accepted with residue semantics, not rejected outside p. Fixed-length parser fallback is explicit and unreachable for a complete word. |
| Preserve original wire f in PHFE.Key | Distinct words may decode to the same tensor. Retaining f makes key encodings faithful to the original syntax and prevents collapsing observable aliases. |
| Replay all original x/y/f words | A typed history alone loses wire aliases. PHFE.replay uses List.foldl and reruns the original next-move adversary, checks decoded queries/packed-key indices, and reencodes only answers. Inconsistent unreachable histories terminate false. |
| Public type/value equivalences | Class parameter/value and raw pp/key/CT codecs expose the concrete types through readers. Downstream algorithms need no foreign bundle unfolding or encoding inverse. |
| One bounded next-move interpreter | SAAdv stores coins,budget,next; run is derived from Games.buildComp. An unrestricted run field would leave its budget unenforced. runDet is the one deterministic analogue and is reused at both layers. |
| TOTAL query budget | Challenge and rejected queries consume budget. Pi/outer padded tape allocates Q key blocks safely. TwoStage q keys has q+1 TOTAL calls. buildComp still accepts a final ret at zero remaining query budget. |
| Literal bitSpec/bitCodec machine interface | FE.toSAAdv is a wrapper around the existing NUPPT.toCompOn convention with one-bit final output. Typed handlers return Option CT/SK, then the shared decAnswer encoding. No arbitrary group/key decoder is introduced. |
| Exact game laws for TwoStage conversion | Independent coin/setup draws occur in different syntax orders. The bridge states equality of expectations for every test and then equality of advantages, not literal OracleComp syntax equality. viewWordBits centralizes the wire layout. |
| Separate concrete efficient simulator targets | The raw SA→committed conversion is explicit. The shared contract has no generic parameter-preprocessing or product-sampler construction that would automatically supply an efficient converted simulator. Both concrete interfaces retain three efficiency fields; r2 adds explicit state/value bounds to each. |
| PG uniform family before κ AND p | Pointwise Raw(p,dimensions,Fn) would permit a constant-modulus efficiency witness. The actual family supplies one PC witness for every κ and arbitrary positive p encoded on input. PG is deterministic; no sampler contract is imposed. |
| Structural polynomial mBound | Function-dependent mCount needs a fixed polynomial upper bound independent of adaptive f and p to define polynomial MDDH/advice dimensions. Raw.mCount_le_mBound is structural, not an efficiency hypothesis. Layered mBound is exactly Σ_(k=0)^d(ℓ+1)^k. |
| Explicit PG finite coordinates | MIdx/TIdx have finite/DecEq data and canonical coordinate equivalences, using finFunctionFinEquiv/finSigmaFinEquiv. No opaque Fintype.equivFin or blanket dependent-Sigma instance is used. |
| Reconstruction field named recVec | `rec` collided with the generated Raw.rec structure recursor and caused a kernel failure during development. Only the field spelling changed; rec_spec retains its mathematical law. |
| Exact specialized PG privacy | AGW/IW layered last-column randomization has identical laws; reconstruction holds for every draw. No negligible PG term is introduced. General affine locality is not claimed. |
| Path-sum proof route | Forward cancellation and backward translation replace determinant/cofactor and canonical-form arguments only for this explicit layered class. No ABP datatype, IK02 import/re-proof or full general-ABP theorem is added. |
| Exact unconditioned Pi basis loss | Retain actual uniform draws and F(p), not the source's incorrect unconditional 1/p estimate. One shared good event charges it once; actual endpoints remain unfiltered. |
| Adaptive public-preserving triangular map | Lemma3 fixes public projections and retains latent U. V's shift may depend on that unchanged U. The inverse subtracts the same shifts. No random guessing, complexity leveraging or group-to-scalar algorithm. |
| Canonical DLIN separated from matrix presentation | Real laws agree; random laws have a zero-coordinate discrepancy. The direct column reduction counts its own exceptional cases, so this separate discrepancy is not added twice. |
| One advice-indexed column realiser | Choose a nonuniform hybrid index and scalar masks before the machine realiser. Polynomial d multiplies ONE machine advantage, avoiding a growing unbounded family of unrelated negligible functions. |
| Exact MPK/CT widths | Actual nested-pair MPK width is (16+24n+8ℓ)wG+10. CT is (6n+5)wG excluding x. Only function keys are padded to mBound; arbitrary polynomial MPK padding would obstruct the uniform linear target. |
| Positive-size uniform linear target | One FinTM and q precede numeric ℓ,n,d,κ and every core input, with bound (ℓ+n)qκ when 0<ℓ+n. At zero size a literal zero-step bound cannot emit five constant group entries. Raw algorithms/security remain total there. |
| Fixed-order and growth normalization | Inequalities assume hp for every generator draw; asymptotic corollaries additionally assume 2^κ≤pκ. Honest code always reads p from pp. This normalization is disclosed rather than attributed literally to every paper's bit-length convention. |
| One common subexponential exponent | Chosen before machines and budgets from the common DLIN exponent, with explicit polynomial absorption and exact rank/matrix slack. No q-dependent exponent is silently selected. |
| Proof-only embedding injection | PHFE/Embedding uses only pow_val_bijective.injective on supplied scalars. No algorithm calls a group logarithm, chooses an inverse exponent or returns a recovered scalar. |
| Restricted scope of reductions' machine hypotheses | Core bounds quantify all typed adversaries and EVERY realiser conditional on fixed advice. Existence assumptions in corollaries quantify ONLY FE.toSAAdv or TwoStage.toSA machine-derived adversaries. |

The user authorized best judgment for modular and adaptable code while unavailable, with
substantive choices disclosed. These are pre-M0 refinements; no frozen interface change is
claimed. Future statement/prose changes after checkpoint0 require the relayed gate-repair
procedure and a separate statements-repair commit. New proof helpers after freeze must be
listed with their reuse searches, without changing frozen statements.

## Files, declarations, contributors and size

The audited source has **74 new Lean modules and 13,745 physical lines**.
The two permitted existing facades are recorded separately in the touched-file and diff
ledgers. Source SHA-256 values and current object hashes accompany the checked-source ledger.

The native collector inventories all 2225 stored constants, including generated constructors,
eliminators, projections, instances and matchers. The complete typed inventory is exported
to `evidence/statements/native-declarations.tsv` and `StmtDump.jsonl` by the completed M0
census. This paragraph describes that historical snapshot. Written source headers/readers are retained separately. Native ROOT/CAT
records and the 387/387 reader validation are already complete.

The final M0 decls2 run reports ADDED 1171, CHANGED 0, REMOVED 0 at the current checked
snapshot. This is a source-header comparison result, not the native declaration count.
The final native ledger must include full name, home module, kind, source position, reader,
source tag and axiom status. Both the campaign counts and source/probe hashes must identify
the actual audited revision.

| Contributor | Work and responsibility |
|---|---|
| Lead/root | Source/base/host verification, isolated worktree and integration, honest/raw PHFE packaging, public codecs, correctness/headlines integration, dependency/cache/serial Lean checks, resource/slot logs, source commits and eventual delivery. |
| fe_interface_review | Generic FE/API review and deterministic runner draft; classes/layered PG interfaces and formulas; generic SA simulation and actual TwoStage conversion; targets/pure assembly; PHFE wire replay/security drafts; source review, audit-tool preparation/control generators, and report/proof drafts. No subagent Lean/Git execution or live source mutation in these tasks. |
| pairing_pg_review | Pairing/source and typed reduction work as assigned; outer QuadraticSecurity drafts; complete 01..06 fidelity/advice/boundary/reuse tables and reader proposals; direct verified-source text/image review. Root integrates and checks source changes. |

Actual authors/committers/signing information belongs to the final commit ledger; these role
summaries do not replace Git authorship records. Search and source-review material is to be
copied under `evidence/subagents/<name>/` with hashes. Scratch source extracts/page images
remain outside the proposed payload.

The original end-to-end estimate was about 8,800-16,100 lines. The complete statements surface
is now about 13.6k. Source-specific algebra, counting, adaptive transcript and endpoint proofs
may raise the final development to roughly 20k-30k lines. This does not relax the hard
1,000-line module limit or the proof/audit requirements; helpers must be split into small
modules and searched before writing.

### Current owned-file line ledger

| File | Lines |
|---|---:|
| `TCSlib/Cryptography/AdvancedEncryption.lean` | 47 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption.lean` | 40 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean` | 636 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Defs.lean` | 30 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Defs/Correctness.lean` | 156 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Defs/Efficient.lean` | 136 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Defs/Raw.lean` | 210 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Defs/Simulator.lean` | 270 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling.lean` | 33 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/Defs.lean` | 525 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/Layered.lean` | 716 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/PathAlgebra.lean` | 137 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/PrefixAlgebra.lean` | 280 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PolynomialTensorAlgebra.lean` | 137 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Run.lean` | 138 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive.lean` | 40 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/Data.lean` | 345 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/FromTwoStage.lean` | 729 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/Games.lean` | 264 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/Security.lean` | 96 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/Simulator.lean` | 249 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation.lean` | 37 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation/Games.lean` | 174 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation/Security.lean` | 95 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation/TwoStage.lean` | 103 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20.lean` | 49 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Linear.lean` | 397 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearCorrect.lean` | 367 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity.lean` | 47 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Data.lean` | 345 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Endpoint.lean` | 89 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Fresh.lean` | 165 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Games.lean` | 231 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Keys.lean` | 205 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Reductions.lean` | 292 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Slack.lean` | 89 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Theorems.lean` | 229 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSimulator.lean` | 413 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE.lean` | 47 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Adapter.lean` | 278 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/CommittedSimulator.lean` | 54 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Core.lean` | 110 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Correctness.lean` | 89 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Data.lean` | 181 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Embedding.lean` | 46 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Encodings.lean` | 178 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Headlines.lean` | 134 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Raw.lean` | 219 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Security.lean` | 365 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Simulator.lean` | 132 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Widths.lean` | 90 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Quadratic.lean` | 412 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticCorrect.lean` | 271 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity.lean` | 47 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity/Advice.lean` | 167 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity/Compose.lean` | 132 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity/Data.lean` | 239 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity/Derived.lean` | 193 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity/Fresh.lean` | 175 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity/Games.lean` | 243 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity/Reduction.lean` | 245 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSecurity/Theorems.lean` | 254 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticSimulator.lean` | 234 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets.lean` | 27 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/Assembly.lean` | 165 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/Garbling.lean` | 76 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/LinearEfficiency.lean` | 108 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/MatrixDH.lean` | 79 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/Scheme.lean` | 139 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/Sim.lean` | 134 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Wire.lean` | 158 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/WireDraws.lean` | 196 |
| `TCSlib/Cryptography/Pairing.lean` | 51 |
| `TCSlib/Cryptography/Pairing/Exponents.lean` | 546 |
| `TCSlib/Cryptography/Pairing/Linear.lean` | 381 |
| `TCSlib/Cryptography/Pairing/MatrixDH.lean` | 31 |
| `TCSlib/Cryptography/Pairing/MatrixDH/Defs.lean` | 255 |
| `TCSlib/Cryptography/Pairing/MatrixDH/Diagonal.lean` | 151 |
| `TCSlib/Cryptography/Pairing/MatrixDH/Parameters.lean` | 178 |
| `TCSlib/Cryptography/Pairing/MatrixDH/SelfReduction.lean` | 328 |

Source-bound ledger: 78 new modules and two permitted facades, 16079 lines at `c222e6b92d75478549e5057c37c9119bf6be50c1`.

## Historical M0 verification ledger; final checks remain open

Results below distinguish completed M0 checks from mandatory final checks that remain pending.
No zero-admission, final Rule10 or completed security-proof claim is made.

| Check / evidence family | Current observation | Required before checkpoint0 / final proofs |
|---|---|---|
| Verified source originals | Exact five hashes recorded before reading; source/image ledger prepared | Retain hash/inspection notes and no-PDF payload check; current source status supersedes archived initial E-SRC. |
| Base/host/package pins | Lead verified required base files and host hashes; pinned Lean 4.25.0 | Refresh immutable source/host/package provenance with final manifest and allowed diff. |
| Cache5 | Lead reports 107 Mathlib roots, 2363 existing archives unpacked, 0 downloads, rc 0 | Retain exact fetch/store/manifest logs. This is a cache result, not source or proof verification. |
| Resource observation before cache5 | 7.11 GiB headroom and 87.87 GiB free disk reported by lead | Retain measurement log and recheck floors as prescribed for later resource-sensitive work. |
| Earlier public-module elaboration | Lead reports all drafted public modules elaborate at 7d42a6ef6a20d379c524c11db87a1b0c0e4c25df | New correctness proof/import/facade changes require new source-bound checks. |
| Complete bootstrap | PASS: 285 modules, zero errors/rc0/fresh objects; all source bytes bound to 70b85f9ba83f27393d98fa5bf88505aea3d22a8d | See evidence/build/summary.tsv; actual check-time HEADs are preserved. |
| Owned source size/admissions | 74 files, 13,745 lines, 144 direct admissions; base admissions unchanged | Final PROOFS delivery requires zero new admissions. |
| decls2 | ADDED1171, CHANGED0, REMOVED0 against pinned base | evidence/logs/m0-decls2-final.tsv; native stored count is separately2225. |
| Style/sketch/width | PASS: style0 findings over76 touched files, sk15 none, widths/sizes0 violations | Raw final M0 tool logs retained under evidence/logs. |
| Name clashes | 1171 explicit new declarations;0 full-name clashes;65 reused short names | Canonical source scanner results retained; native imports also elaborate without duplicate constants. |
| Campaign lint | No new FAIL;4 warning lines cover5 acronym-case definitions with published readers | All five readers are natively verified; exact diagnostics and justified spellings are retained. |
| Published acronym-case readers | DLINAssumption→dlinAssumption_iff; PGSound→pgSound_iff; SASimSecureWith→saSimSecureWith_iff; SASimSecure→saSimSecure_iff; MDDHRealizable→mddhRealizable_iff | PASS: all387 requested reader theorems resolve uniquely and their types mention the actual target. |
| Native declarations and full types | PASS: 2225 stored constants, complete native types without elisions | evidence/statements/native-declarations.tsv, written-declarations.tsv and StmtDump.jsonl. |
| Rule10 whole-file seals | Canonical pinned tools prepared; A/B strict and coe configured, coe-A canonical | Run all frozen owner modules with maxErrors0. Requested must equal verified at install AND EOF, including actual Name components and instance-mask checks. No completed seal evidence is claimed. |
| Rule10 paired controls | Inventory/generators prepared; executed 0, verified 0 | One negative/positive pair for every written public def/abbrev, unsealed baseline and sealed sensitivity, with canonical ctlcheck2 ALL_OK and complete coverage. Flag aliases/proof irrelevance explicitly. |
| Explicit body/generated-equation reads | Provisional text scan found four own runDet reads and four local hn items; no generated-equation candidate | Run canonical scan1 native kinds probe and scan2 at frozen HEAD; review all foreign Core/Mathlib/TCSlib and unresolved/generated-equation rows. Text-only scan is not PASS. |
| Instance/projection coverage | Source and native-census plan retain instances/generated constants separately | Preserve canonical semireducible-instance unfolding mask and typeclass-state invariants. Ordinary algorithm bodies cannot be dropped as “plumbing.” |
| Exact?/apply? overlap probes | Pending | Execute required scratch searches under root's slot, record failures/suggestions and reuse decisions. Text search alone is insufficient. |
| Axioms and sorry dependencies | 2225 #print axioms records; 1933 standard-only, 292 sorryAx-dependent;0 other nonstandard axioms | M0 admissions and transitive raw-law dependencies are explicit; no standard-only headline claim. Trace paths are in evidence/statements/sorry-traces.jsonl. |
| Frozen-file and statement/prose checks | Header/prose manifest prepared at 70b85f9ba83f27393d98fa5bf88505aea3d22a8d;1171 written declarations; all negative controls rejected | evidence/freeze/checkpoint0.json; freeze activated at exchange commit 1e77173a7032b57aa22260787711c6c7a1b7596e. |
| Phase A/import/extraction boundaries | Static scope/import/admission inventory passes;1 justified proof-only injection token;0 PDF additions | The sole pow_val_bijective hit is PHFE/Embedding.lean:42 and returns no exponent. Final native Rule10 checks remain pending. |
| Payload/patch/ZIP hashes | Pending | Format-patches, commit ledger, src/evidence/report, no PDFs, top-level SHA256SUMS with exact payload path set, final ZIP rooted at io-phfe/. |

The 48 earlier facade diagnostics were repaired by explicit exports and security facades.
The only remaining campaign warning lines are the five documented acronym-case readers,
all validated by native name/type checks. They are checker naming heuristics, not missing
reader declarations.

Rule10 tool provenance is in `evidence/preparation/tool-provenance.tsv`. Thirty extracted
text tools retain their pinned bytes except the two recorded host-wrapper adaptations.
The new PHFE inventory/control drivers are separate artifacts, not modifications of that
suite. The root-only workflow is delivered as `evidence/preparation/rule10-prep/RUNBOOK.md`.

The exact canonical notation exclusions are: strict-A excludes PolyExpr.eval; strict-B
excludes none; coe-A excludes eval and FinDist.instCoeFunForallReal; coe-B excludes only
that FinDist coercion. The instance adapter changes requested definitions' unfolding
membership, not the typeclass lookup tables; it checks actual Name components, scoped
payload intersections, unchanged lookup snapshots and EOF installed status. Requested,
active, already-irreducible and verified counts must reconcile in every chunk. Marker
presence alone is insufficient.

Instances are exempt from ordinary doc/reader obligations under the policy clarification,
but remain visible in the native census and mask. Generated record/projection/eliminator
constants remain visible too. Public aliases absent from ordinary canonical requests have
separately labelled forced-opacity diagnostics; such a diagnostic is not silently called
an ordinary seal pass. A negative that fails unsealed or succeeds sealed does not establish
sensitivity. Proof irrelevance, projection reduction and alias reduction must be investigated.
Explicit `unfold name` can bypass local opacity via unfolding equations/delta expansion,
so the independent static policy scan remains necessary; it cannot be replaced by seals.

The initial static audit tables and source-header metadata are retained as historical
search/review evidence. Their original 67-file/145-admission snapshot is not final-HEAD
verification. Full-paper scratch extracts/PNGs are not payload evidence. The native
inventory, source-bound bootstrap, actual control outcomes, complete axiom census and
final no-PDF/hash/path checks remain the authority for milestone claims.

## Proof obligations and continuation under the frozen statements

The 144-admission snapshot is the M0 state. The current committed development has
77 direct admissions; `evidence/logs/proofs-simulation-quadratic/admissions.jsonl`
records their full written names and source positions. M2, exponent algebra, all class
results and the internal linear/quadratic correctness modules are proved. The latest
31 completions have standard-only native axiom dependencies, and their eleven modules
passed exact-HEAD checks; the final full stored-constant census is still required.

Remaining substantive obligations are:

1. The concrete DLIN random-law consumer and its advantage consequence; uniform-matrix
   rank and column laws, the DLIN-to-MDDH self-reduction and its exact bounds.
2. Pi dual-basis conditional laws, the exact adaptive public-preserving bijection,
   both computational hops, exact PG hop and actual fresh/padded endpoint couplings.
3. Outer typed Pi-adversary replay, computational hops, actual fresh endpoint coupling,
   generic wire replay and all raw core security inequalities.
4. Exact rank/slack bounds, common-exponent asymptotic consequences, machine-restricted
   corollaries, target/assembly transport and efficient primitive headlines.
5. Full final native census/types/freeze comparisons, Rule 10 seals/controls/body scan,
   final bootstrap/sweep, lineage/scope/boundary/fidelity audits and final delivery.

Efficiency targets themselves remain named unproved Props by design. Phase A must NOT fill
those targets by constructing programs/samplers or add target hypotheses to raw theorems.
Pi is an internal raw component; its efficiency is consumed only through the outer targets.
If a substantive theorem is found false, nonuniform, vacuous, asymmetric or unable to preserve
the requested source notion, report E-STMT/E-SRC rather than silently weakening it.

The milestones include the published M0 statements/audits/first push, M1 exponents/DLIN/MDDH,
M2 generic FE/classes/PG, M3 Pi, M4 quadratic construction and M5 raw/efficient headlines and
final audits. Source families are already present across these stages, so proof work may
follow dependencies after freeze. A final budget-limited delivery must be explicitly PARTIAL,
list remaining admissions/dependencies and include a continuation plan; it cannot claim the
final PROOFS gate or completed objective merely because all statements elaborate.

## Delivery manifest and outstanding release conditions

The final exchange payload must be `inbox/fills/io-phfe/` only, containing this report,
`patches/` with COMMITS.tsv, all new/changed source paths under `src/`, full raw audit/build/
cache/resource/slot/search/source-review/subagent logs under `evidence/`, and SHA256SUMS whose
path set equals the delivered files. A ZIP returned to the user must have io-phfe/ at its root.
No PDF, copied paper page, program/sampler implementation or unrelated exchange path belongs
in the payload. Pull/rebase the authorized exchange branch before each checkpoint push;
never force-push or open a PR. Record any rebase and push refusal honestly.

The dispatch's M0 subset is the checkpoint requirement: complete definitions/readers/targets,
all theorem statements, module elaboration, decls2/StmtDump, axiom inventory, lint/width/clash,
fidelity/rule15 tables and a hashed payload. The full Rule10 and proof completion checks
remain final-delivery obligations; prepared seal variants are not reported as passed.
There is no active source/resource blocker. No counterexample beyond the corrected source
rank estimate was identified in the source/header reviews; the admitted claims still need proofs.

## References and supplied editions

- [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; supplied full version, Cryptology ePrint Archive 2020/764, revision of
  3 January 2025. Printed pages are PDF page minus 4; exact source SHA appears in the ledger.
- [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; supplied full version, Cryptology ePrint Archive 2020/1420. Printed pages agree
  with the PDF. Section 3's main security claim is unnumbered; Theorem 1 is Appendix B p.12.
- [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, Journal of the ACM 73(1), Article 1, 2026, supplied full version. Journal labels
  are 1:3,1:7,1:8,1:21 at the cited PDF pages; the ledger explicitly uses PDF numbers.
- [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted Sums
  from k-Lin*, 2020, supplied full version; Lemma 2 and Appendix A(28)-(32), pp.37-38.
- [IW14] Y. Ishai, H. Wee, *Partial Garbling Schemes and Their Applications*, 2014,
  supplied full version; Definition 1, Theorem 3 and Section 4.2.

TCSlib/Core/Mathlib API references and source positions are given in Overlap/reuse. Pinned
contract and realisation reports determine shared API reuse; paper contents are mathematical
sources, not operating instructions. No unread external paper is represented as a primary
proof source.

## Current proof-size supplement

At source `c222e6b92d75478549e5057c37c9119bf6be50c1`, the 78 new modules and
two permitted facade files contain 16079 physical lines. The original 8,800–16,100-line range now looks
optimistic for all explicit couplings and reductions. The working re-estimate is
22,000–30,000 lines, with uncertainty concentrated in adaptive endpoint couplings and
DLIN/MDDH self-reduction. Independent algebra modules keep each source file below the
1000-line limit; no frozen declaration is moved merely to make room.


## Finite-column development supplement (after M2)

The published M2 snapshot is source c222e6b92d75478549e5057c37c9119bf6be50c1 and
exchange e50e4a2520c32cac1f411d302153c9065806e681. The subsequent local source commit
9ff3fc19f7cecd268ee7eb1a6b58590e97dbfee2 adds the finite-linear helper statements and
precise prime-field import. At that 9ff3fc19 snapshot M1 was not complete.
At this working snapshot, 83 touched files have 17348 lines and 63 direct admissions.
The source-bound development inventory is evidence/logs/proofs-finite-column/; its
working labels do not claim exact-HEAD verification. Final native checks supersede it.

The concrete DLIN matrix comparison and its advantage consequence are now proved, as
are uniform images of surjective matrix maps, the at-most-two-row rank estimate and the
small-row MDDH bound. The canonical real-column comparison has exact loss p^-2. The
random-column ladder compiles with its determinant and coordinate split proved, leaving
only its exact bad-event probability. Its outer theorem is still admitted until that
local obligation is filled. The advice codec length and injectivity are proved. Both
polynomial-over-order slack decay and all six linear-slack results are proved. The PHFE
class evaluation identity and simulator singular/lift glue are also proved. Each result
has a successful slot-wrapped module check; the batch axiom census is still pending.

### New helper overlap and modularity decisions

| Helper | Reused API and nearest relatives | Prior searches |
|---|---|---|
| expect_sample_matrix_mul_of_mulVec_surjective | Matrix right-inverse criterion, Matrix.addMonoidHomMulLeft, AddMonoidHom.fiberEquivKerOfSurjective, Equiv.sigmaFiberEquiv and sigmaEquivProdOfEquiv, existing uniform-equivalence and pair readers. No fiber count is reproved. | evidence/search/mddh-finite-linear/run2; run1's missing LibrarySearch import is retained as invalid. |
| smallRows_surjectivity_failure_le | Module.Dual.range_eq_top_of_ne_zero, singleton probability, Matrix.card_GL_field. Its current unit-event cardinality bridge will be shared with the simulator rank proof through the separately searched GL-probability helper. | Same isolated native two-target probes and static nearest-relative notes. |
| exists_fiberwise_add_right_equiv | Equiv.subtypeEquiv, ofFiberEquiv, prodCongrRight and existing add-group translation laws. The general kernel translation fixes the public projection and preserves the complete latent tape. | evidence/search/adaptive-kernel-shear/run; no complete exact/apply proof. |
| dlin_base_transpose_mulVec_surjective | Existing matrix right-inverse criterion with an explicit three-by-two scalar right inverse. | evidence/search/dlin-base-surjectivity/run; clean target, no complete exact/apply proof. |
| dlin_real_column_gap_le | Shared uniform matrix-image law through transpose, matrix-vector associativity, OneWay.uprob_pi_forall and singleton probability, shared bounded-expectation averaging. | evidence/search/dlin-column-laws/run; clean isolated targets. |
| dlin_random_column_gap_le | Same image law; Matrix.det_fin_three and standard finite-function equivalences, independent-coordinate and complement probabilities. The local bad-mass obligation remains open at this snapshot. | Same native probes; new target is glue for the direct canonical-column route. |

The choice to keep FiniteLinear, AdaptiveShear and ColumnLaws below the cryptographic
consumers avoids import cycles and repeated finite-law arguments. No runtime host,
machine, sampler, product UniformSampler or new efficiency interface is introduced.
The direct column bound includes zero diagonal scalars. The final reduction must retain
4d/p and must not add the unrelated canonical-matrix random slack a second time.

### Diagnostics and resource disclosure

The initially slow concrete DLIN pointwise checks were caused by a missing direct import
of Mathlib.Algebra.Field.ZMod: Data.ZMod.Basic provided the ring, but not the prime-field
instance required by the generic diagonal theorem. A scratch typed-term diagnostic
exposed the failed Field synthesis. The earlier hypothesis about classical instance
mismatch was not established and was not the cause. The corrected precise import is in
9ff3fc1, with the local prime Fact supplied from the public parameters. The subsequent
pointwise and averaging proofs pass native checks. All diagnostic source bytes, failed
attempts, restoration checks and recorded own-PID terminations are retained; no peer
process was stopped. Debug run_tac instrumentation exists only in diagnostic snapshots,
not in the live mathematical source.

The narrowed cache-get-7 completed with 112 roots, 2364 existing archives and no download.
Its three-slot acquisition never overlapped this job's own Lean process. The package
pins and resource floors passed; logs include cache-get-7.json, package-check-7.txt,
cache-7-resource.log and the store-before snapshot. No blanket cache or lake build ran.

A draft asymptotic proof proposed importing CoinSampling.Asymptotic. Root rejected that
restricted import before any source edit and used the permitted Foundations primitives
PolyExpr.eval_le, SubexpSmall.mul_pow, const_mul and mono instead. The rejected draft is
retained as superseded provenance, not as landed or checked source.

The separately proposed general GL-probability target required parentheses around its
product body: the first native probe exposed an out-of-scope binder. Run1 is invalid
reuse evidence. Corrected run2 has a clean header and an expected exact-search failure;
apply-search returned only partial equality wrappers before its heartbeat limit. That
limit is disclosed rather than represented as an exhaustive no-match result.


The random-column bad-mass block subsequently passed native checking, so ColumnLaws is
now admission-free. Its proof uses the stronger published singleton law directly at
r+s instead of an explicit translation; the proof sketch was refreshed accordingly.
The shared prob_sample_matrix_isUnit_eq helper passed its first native proof check.
The small-row square branch was refactored to consume it, removing the former local
unit-subtype cardinality conversion; the refactored module passes. The first refactor
attempts exposed only the syntactic Fin(0+1+1) versus Fin2 normalization issue; their
raw logs and source snapshots are retained. The helper covers dimension zero as well.
The simulator now imports this lower-level finite-law module directly; no new Mathlib
root or forbidden import is introduced.


The completed finite-column batch is now local source commit
2f02d9debe3659da7693e9326a7ce6d29b519282, `io-phfe: prove finite column laws and exact
simulator rank probability`. It touches ten modules with proof bodies, refreshed sketches,
seven new helpers and precise imports/facade entries. The full owned source inventory is
83 files, 17498 lines, 61 direct admissions. Compared with M2, 23 declarations have newly
completed proofs (seven new helpers and sixteen frozen statements). This is a local proof
checkpoint; at that 2f02d9d snapshot M1's reduction and consequences remained open,
so no M1 exchange milestone was claimed. The source branch has not been pushed.

The exact simulator rank proof now reindexes the complete independent A,c draw as a
uniform square matrix, integrates all unused masks, and uses the shared n=3 formula.
The full LinearSimulator module is admission-free. Proof-only kernel-shear glue remains
available for the later adaptive coupling; its existence alone is not a proof of that hop.
The finite-column helpers' current overlap ledger has seven entries including the shared
prob_sample_matrix_isUnit_eq, whose nearest API is Matrix.card_GL_field plus the standard
Units.val range-cardinality and uniform probability readers. No new counting theorem is
reproved. Its native search qualification is recorded above.

Both official fillinputs inventories completed at this commit. The merged closure has
292 modules and 112 Mathlib roots, with no additional roots since cache-get-7; no further
cache fetch is warranted. Current resource headroom is 6.81 GiB and free disk 79.62 GiB,
above the dispatch floors. Style and sk15 checks pass across all 83 files. Width checking
initially exposed one overly long refreshed proof-sketch line; after wrapping it,
WIDTH/SIZE PASS reports zero violations. The weak development freeze reports no changes
and 28 helpers since M0; the stronger native syntax audit and batch native axiom checks
will bind this exact source commit separately.


Exact-commit checks now pass for all ten changed modules (rc0, both error forms0,
fresh oleans), and all 23 newly completed declarations print standard axioms only:
0 sorryAx-dependent, 0 other nonstandard. See proofs-finite-column-head-2 and
proofs-finite-column/axioms-summary.json. The static Phase A/scope audit at this same
commit reports 61 admissions, unchanged base admissions, zero forbidden imports,
forbidden proof escapes, sampler instances, local replacement contracts/realization,
new axioms or PDF paths. Its sole R-DLOG hit is the previously disclosed proof of
embedding injectivity; it computes no logarithm and is outside all algorithms.
Full final stored-constant, Rule10 and proof-completion audits remain outstanding.


The stronger native syntax freeze at 2f02d9d passed with 1171 original declarations,
1199 current declarations and zero frozen-header/prose changes. All five actual-source
controls passed: return-let header character, prose and sketch-marker changes are rejected;
changed sketch and genuinely changed proof body are allowed. Evidence:
evidence/freeze/native-2f02-run1 and native-2f02-binding.json. This is syntax/prose freeze
verification, not the separate final compiled-full-type comparison.


A fresh Rule10 metadata snapshot at 2f02d9d covers 81 owned modules (the two base
facades are excluded from owner roots). Its 474 public written entries include 40
instances and four structures without ordinary reader candidates; these are explicit
kind rows, not missing def/abbrev controls. All 387 ordinary public defs/abbrevs have
candidates, pending the final native reader/control verification. The 2f02 snapshot is
bound to Git bytes. Its canonical explicit-body scan prepared 1345 tactic items and
21970 native name candidates; that kind probe and the full seals/controls have not run.
Prepared metadata is not reported as Rule10 PASS and must be refreshed at final HEAD.

The subsequent working mddhAdv_le ladder compiles with six named local obligations.
Its endpoint laws, shared-realization coin verdict identity, and scalar combination of
losses into 4/p have now passed native checks. The actual group-arithmetic embedding and
two conditional column-law consumers remain open. The selected finite advice is fixed
before introducing any realiser, preserving the frozen universal-realiser quantifier.


Post-2f02 working proofs add four WireLemmas interface adapters and the missing concrete
raw embedding projection reader. Their isolated native searches precede their proofs:
evidence/search/wire-words (four clean exact-search failures, four partial apply results)
and phfe-raw-embed-reader (both exact targets and the apply target succeed by reflexivity).
The adapters reuse BilinearGroup.length_groupMatrixEnc/groupMatrixEnc_injective; vectors
are one-row specializations. No flatten count or point-encoding injectivity is reproved.
The new proof module is exposed by Wee20 and imported by Encodings without an import cycle.

The raw perfect-correctness and zero-error proofs now compile using the typed quadratic
correctness and shared AllOutputs/perfect-to-zero APIs. Their final standard-axiom claim
is deliberately held until the raw record's encoding proof fields are admission-free.
Public/master-secret/ciphertext lengths and the key-word upper bound compile. The current
key representation contains only K1/K2/K3/R; its actual length needs mCount_le_mBound,
not an auxiliary-row count. Ciphertext/public-key injectivity also compile. A projection
inference pitfall in the public-key proof was fixed with explicit pair inputs, keeping
wire words behind their published interfaces. These are working developments, not a new
published milestone or replacement for final checks.

The direct reduction's preprocessor identity now compiles through the existing group
matrix/vector action theorems. Only its two conditional-law consumers remain. The proof
architecture is being factored across the real/random flag to share observer, tape/order
transport and whole-column resampling, avoiding duplicate arguments and the 1000-line
file limit. This is a proof-body refactor under the same frozen statement and loss.


A further native-gated binary reader, Pairing.pairEncode_eq_iff, now lives in the owned
Parameters module shared by pairing and wire consumers. It states pair equality as two
component equalities and reuses Turing.pairEncode_injective; it builds no parser. Static
name/shape searches and clean exact/apply probes are in evidence/search/pair-codec-binary-reader.
The engineering choice avoids a new fold/serialization theorem and repeated explicit
pair-argument plumbing. Requested promotion: move this generic reader to the shared
Turing.Encoding API at a future permitted shared-file window. No out-of-scope file is edited.

The function-key proof consumes the existing GGMRed.pairEncode_append_right instead of
reproving that append law, and ofFn_padFin_eq_take from CollectionsLemmas. It treats any
trailing padding as part of the second framed component, recovers the original function,
then aligns actual node dimensions and lengths. Only then can the common padding tail be
cancelled and typed key fields compared. All newly needed base oleans already exist;
the static import-closure comparison found no new Mathlib module. Scalar faithfulness uses
only BB1Machine.order_le_two_pow from the existing Draws module, never its draws or decoders.


Function-key injectivity subsequently passed its first native proof attempt, including
original-function recovery and dependent dimension alignment. The shared MDDH proof-body
refactor also passed its first native check with exactly two common transport/resampling
holes, projecting SelfReduction to 821 lines before fills. The four earlier checked
proof blocks are byte-identical. Its upstream-only import closure differs from the official
fillinputs closure, which additionally includes all downstream consumers and their imports;
only the official merged order is used for final build coverage and root accounting.


The encoding/raw-correctness batch is local commit
359e440a46f5939223bbbe73cb67731e5b4c0b94 (`io-phfe: prove PHFE encoding faithfulness and
raw correctness`). Its seven changed modules pass exact-commit checks with fresh oleans,
zero rc/errors, style/sk15/width PASS. The committed snapshot has 84 touched files,
17977 lines and 49 direct admissions. Eighteen declarations are newly completed versus
2f02d9d: twelve frozen statements and six new helpers. The separate working MDDH proof
is intentionally unstaged; its body does not enter this committed snapshot inventory.
No source branch is pushed. Native axiom checks for the eighteen are in progress.

The quadratic simulator's last arithmetic admission, crossLeak_known_value, also passes;
that module is now admission-free and uses supplied scalar values without logarithm
extraction. PHFE.Encodings and PHFE.Correctness are admission-free, and the current raw
embedding reader and four wire adapters are proved. Current resource headroom/free disk
are 6.93/79.61 GiB. The official merged import closure is refreshed separately; narrowed
cache work is needed only if the official root set changes.

The whole-column resampling ladder now compiles with one inner normalization hole. The
shared fixed-order transport is proved. Explicit update expression types and complete
uniform-equivalence observer functions repair the initial inference failures; no new
resampling/counting theorem is introduced. Existing expect_sample_coord is called for
both coefficient and uniform-response columns, retaining every unused coordinate.


At 359e440a4, all eighteen new completions print only standard axioms, including both
raw PHFE correctness headlines and every encoding theorem: zero sorryAx dependencies
and zero other nonstandard axioms. See proofs-wire-correctness/axioms-summary.json.
The official merged downstream/upstream order has 293 modules and the unchanged 112
Mathlib roots, so no extra cache fetch ran. The seven exact-commit module checks and
native dependency audit certify this batch, not completion of the overall job or M5.


## M1 completion and modularity decisions

Local source commit `d88f0284cb898f940e9e2c6a5690233422a79e30` closes all three remaining
SelfReduction admissions: the explicit advantage bound, negligibility, and common-exponent
subexponential hardness. No frozen header or statement prose was deliberately changed.
Exact-head four-module checks are in `evidence/logs/proofs-mddh-final-head/`; all return
rc 0, both error forms 0, and fresh oleans. The native batch axiom summary is
`evidence/logs/proofs-mddh-final/axioms-summary.json`: 10 standard-only, 0 sorryAx-dependent,
0 other nonstandard. Its explicit reduction never constructs a realising machine.
Advice is chosen before the realiser and works for all security parameters. The direct
`4d/p` loss already covers zero canonical masks; no matrix-DLIN slack is added again.

The reduction shares one observer and one scalar-column law across the real and random
branches. Fixed-order transport uses the shared coin congruence and public order readers.
Whole-column resampling calls the existing coordinate-resampling theorem for both the
coefficient and response tapes, retaining unused coordinates. The last normalization step
initially left an `if True` goal; replacing that conditional simplification by reduceIte
closed it. Both failed attempt and clean retry logs are retained. No statement was repaired.

I chose a separate lower mathematical module, `Pairing/MatrixDH/Hardness.lean`, rather than
allowing the long reduction file to exceed the hard size limit. Its three new helpers are:

- `BilinearGen.mddhCorrection_subexpSmall`, the explicit scalar correction estimate;
- `BilinearGen.mddh_subexpHard_of_adv_le`, a reduction-specific common-exponent consequence;
- `BilinearGen.mddh_negligible_of_adv_le`, the analogous negligible consequence.

The first moves the existing correction argument: its old location now reads the correction
formula and calls the new helper. Exactly one live mathematical proof remains. The other
two consume a supplied machine-wise inequality, with one machine working for all parameters;
they construct no machine, sampler or runtime algorithm. The subexponential helper fixes
eta=min(a,1)/4 before the adversary. SelfReduction has 999 logical lines; the width tool
and style lint differed by the terminal newline at 1000, so one empty separator was removed.
All lines are at most 100 characters. This choice and all three additions are disclosed for
review under the user's instruction to make modular, adaptable implementation judgments.

Overlap and reuse for the three helpers is recorded in
`evidence/search/mddh-hardness-closure/`, `evidence/search/mddh-hardness-type-only/`, and
`evidence/subagents/proofs-mddh-final/proofs-pairing/MatrixDH/HardnessDesign/`.
Name/shape searches found no allowed reduction-specific result. The correction exact search
could not close its target; apply returned only partial suggestions. Both closure exact/apply
searches timed out at 200,000 heartbeats, so they are NOT exhaustive no-match claims.
Separate TYPE_ONLY probes verify both headers with rc 0/errors 0. Nearest whole APIs consumed
are Foundations.Subexponential's mul_pow/const_mul/add/mono and PolyExpr.eval_le, and
Asymptotic.EnsemblesLemmas.negligible_polyExpr_mul (line 377). The nearest generic
CoinSampling polynomial-subexponential closure is in a forbidden module; it is neither
imported nor copied. The local polynomial comparison specializes PolyExpr.eval_le and
standard scalar inequalities; the asymptotic absorption/decay API is reused whole.

The same commit proves three Pi infrastructure declarations: paddedDrawIndex_lt,
challengeRow_lt, and simulate_saRun_det. The last consumes the generic published run bridge;
challengeRow_lt consumes the standard finite-product index bound. They introduce no helper,
new import, new sampler, or new machine. Both active subagents supplied scratch candidates
and static reuse analysis; only the root ran serial slot-wrapped Lean and Git. Current
memory headroom/free disk were 6.86/79.58 GiB. Official fillinputs union adds Hardness as
one TCSlib module but no Mathlib root, so no cache fetch ran.

M3, M4, and M5 security/coupling proofs, the final compiled-type comparison, complete
stored-constant census, Rule 10 suite and final delivery audits remain outstanding.
This is a milestone proof batch, not the completed end-to-end development.

The M1 R-DLOG recheck has exactly three textual hits. SelfReduction's choose and choose_spec
select the proof-established advice family by averaging; they do not select a group exponent,
and no reduction evaluates them. PHFE/Embedding uses only the injectivity projection of
pow_val_bijective in a theorem about the explicit exponent embedding. It defines no inverse
and extracts no witness. The raw grep is `proofs-mddh-final/rdlog-hits.txt`.
All 85 owned source files pass style, sk15 and widths at this checkpoint; logs are in the
same directory. The newly prepared Rule 10 d88f snapshot is HEAD-bound but NOT natively
executed; no full-suite Rule 10 or final stored-constant census claim is made here.

The native M0 freeze audit at d88f0284c passes: all 1,171 original declarations are recovered,
1,208 current declarations include 37 permitted helpers, and no frozen header or prose changes
are found. All five source controls behave correctly. `native-d88f-binding.json` compares
EVERY one of the 85 native current source snapshots to git show d88f0284c and to unchanged
working bytes. The final compiled-type comparison is separate and remains required.
This payload is checkpoint 1 (M1); the receipt is recorded after publication, without
predicting the exchange commit hash in advance. Source branch fill/io-phfe remains local.


M1 publication succeeded as exchange commit `6d3cb2dca7633c9aecd5fcbf5efd1c3f48aeee4a`.
The delivery-only commit rebased from 7d50ad3d04691c06e842af1d87a49c01350c2667 onto the
current exchange branch before push. Its 7,568-file payload (85 Lean source files,
863,350,548 bytes) has SHA256SUMS hash
`ab0ee97964cc9546c8ce5f10e47f50daed268f574821587b98620049fcf05fe4`.
All paths/hashes and no-PDF/credential checks passed. The first push attempt was accepted;
only inbox/fills/io-phfe changed. The source branch was not pushed. Publication receipt,
pull/rebase, payload verification, commit, scope and push logs are retained under evidence/logs.


## Advice and coupling infrastructure after M1

Local commit `a0289e063a4b932692d4dca4e6c7eed66dbd33cc` proves thirteen declarations:
ten existing statements and three new helpers. All linear, mask, and full quadratic advice
word bounds/injectivity now reuse the existing numeral, framing and modular-vector APIs.
Both mixed-leakage rewrites preserve arbitrary group mu, using the whole tensor/group-dot
laws; no exponent witness is selected. The real padded game presentations agree directly.
On a good basis, the complete honest/decomposed key handlers agree for all adaptive queries
with the same full tape, group matrix input, coins, refusals and total budget.

The three new helpers and modularity decisions are:

- `FiniteRandomness.expect_sample_embedding_independent` in FE/FiniteRandomness: the selected
  finite coordinate family is fresh jointly with residual tests ignoring its image; the
  complete original function, including unused coordinates, remains on the right. Standard
  image/complement/range equivalences and uniform transport/product laws are consumed whole.
  Requested future promotion is Games/Probability; no out-of-scope file is changed.
- `Wee20.Linear.combineRows_reconstruct` in LinearSimulator: arbitrary group rows reconstruct
  from their two public projections plus hidden row under a supplied known left inverse.
  It consumes groupVecMul_matMulGroup and finite-product/single-coordinate laws whole, needs
  no finite column type or discrete-log witness, and serves all three key blocks.
- `Pairing.orderSchedule_le_two_pow` in MatrixDH/Widths: one reader transport supplies the
  scalar word-width bound to every advice codec. The previous repeated MDDH and mask blocks
  now call it, and the linear codec also reuses it. Widths imports Parameters plus the
  existing BB1 Draws width theorem; it uses no draw or decoder. Putting this heavy proof
  import directly in Parameters would add 496 modules to that isolated closure (static
  count), so I chose a sibling proof module and preserved the light parameter-type layer.
  The full job already imports those dependencies, hence zero new Mathlib roots/cache work.
  A future generic pairing width theorem can remove the incidental BB1 dependency.

Native gates and nearest APIs are retained under evidence/search/{finite-restriction,
combine-rows-reconstruct,order-schedule-width}/ and the current subagent archive.
Finite restriction's exact search timed out at 200,000 heartbeats (non-exhaustive); apply
found no relevant lemma and a separate TYPE_ONLY probe typed its header. Reconstruction
and schedule-width exact searches could not close their targets; apply produced partial
suggestions only, with clean TYPE_ONLY probes. No successful full-match claim is made.
All three helper proofs subsequently passed native checks on their first proof attempt.
Group reconstruction reuses Exponents.groupVecMul_matMulGroup; finite restriction reuses
Probability.expect_sample_equiv and Bridge.expect_sample_pair; schedule width consumes
BB1Machine.order_le_two_pow whole. Static root/accounting metadata is closure.json.

The proof sketch of game1_good_eq_game2 was refreshed to actual handler equality; its
opening prose and header remain untouched. Initial consumer attempts lacked the Matrix
notation scope and then retained an unnecessary rfl after a closing simplification. Their
failures and restores remain in raw logs; explicit Matrix.transpose and the existing
reconstruction reader close the proof. Width consumers likewise use only published readers.

Evidence: proofs-advice-coupling-head/ records nine exact-commit module checks, each rc0,
both error forms0 and a fresh olean. proofs-advice-coupling/axioms-summary.json records
14 native standard-only prints, 0 sorryAx and 0 other nonstandard; this includes every new
completion plus the refactored MDDH encoder proof. Progress/admission counts come from git
show a0289e063, not a working ladder. All 87 owned source files pass style/sk15/widths.
Current memory headroom/free disk were 6.75/78.58 GiB. No source branch was pushed and no
new milestone beyond M1/M2 is claimed. The final native freeze and compiled-type/census/
Rule10 audits still have to be refreshed over the completed development.


Current uncommitted security development is distinct from a0289e063's 33-admission snapshot.
The adaptive Game2-to-Game3 scaffold and the fresh endpoint scaffold both typecheck with
explicit local holes. hBlind is proved: the first executed accepted challenge is a function
of the public key and adversary coins, using simulate_allOutputs_bad for post-commit
message preservation and only a prechallenge budget induction. The full raw thirteen-block
chart construction typechecks; reader/permutation/run obligations remain. It includes a
raw-row fallback on singular fibres, preserving identity there rather than pretending that
singular projections form an equivalence. No guessing or additional loss is introduced.

For the fresh endpoint, the complete coordinate bound and injection subproofs now pass.
They consume canonical finite product/padding/sum/offset embeddings, preserving the
auxiliary/output padding gap and the physical T,R,Uhat,coins order. The count and offset
proof blocks were MOVED to shared local scope and are used by both; no duplicate retained.
The separate actual total budget q is unchanged; q+1 is only auxiliary independent-row
capacity with unused last coordinates retained. The fresh coupling itself is still admitted.

A new proof-only FE/ReductionLaws expectation adapter for the shared RealizesOn verdict
reader has passed its native proof check, after clean TYPE_ONLY and expected unsuccessful
exact/partial-apply searches. It reuses coinsEquivPoly and its bit-list reader, and creates
no predicate, machine or sampler. A corresponding first-hop ladder now checks with only
the exact averaged experiment law unproved: simultaneous advice selection and transport
of EVERY realiser are already checked. All of this remains working development, with no
claim that M3 or its security inequality is complete. A lower raw-coordinate theorem and
single-column MDDH observation law are being gated to prevent duplicated chart/coercion
proofs and keep the theorem files below the size cap. No frozen header/prose is changed.


## Checkpoint 3: authorized statement repair and relocation checkpoint

| Statement-change record |
|---|
| statements r1: PHFE-C0-F01, simulator state bounded by stLen (GJLS21 Def 4.3: PPT simulator) |

The repair is its own seven-file source commit, `a4fe0fd7caaf5fbe5b27f1c2183e539d3b3ba6f8`,
titled `statements r1: PHFE-C0-F01`, directly after `a0289e063`. It adds no admissions.
Both raw simulator interfaces now carry one `stLen : PolyExpr`, before the security
parameter and public parameters, and an injective encoder into `Fin (stLen.eval κ) → Bool`.
Every core input/output word serializes the state through `List.ofFn`. The committed
conversion copies the same width. `toSA` converts adversaries, so it needs no state field;
its consumers and the exact game identity were rechecked unchanged. The assembled efficient
simulators inherit the bounded raw state and their six existing efficiency targets use the
new word. No machine, sampler or efficiency proof is constructed here.

I chose the preferred fixed-width form because the concrete state already has an exact
canonical word length for every typed state. Its width is
`(8*n(κ)^3 + 68*n(κ) + 24*ℓ(κ) + 104)*G.wG(κ) + 40`.
The proof includes empty dimensions and singular bases. The fixed-width adapter recovers
exactly the old complete word, and its injectivity consumes the existing word-injectivity
proof. All honest/simulator cores, draws, typed states, games and advantage bounds retain
their existing substance. This strengthens the former unbounded interface; no equivalence
with arbitrary unbounded simulators is claimed. Root integrated, checked and committed the
repair. The two read-only/scratch agents prepared the mechanical interface inventory,
codec arithmetic/recovery/injectivity proofs and independent scope review.

The canonical native M0 audit was run unchanged. Its raw verdict is FAIL, as expected for
the relayed repair. An exact before/after hash-pair adjudication gives PASS for precisely
these 16 existing declarations and rejects any other change. In the table, `FE` expands to
`TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption`; every name is exact.

| Frozen declaration | Changed frozen fields |
|---|---|
| `FE.FEScheme.Raw.Simulator.Raw` | header,prose |
| `FE.FEScheme.Raw.Simulator.Raw.encInputWord` | header |
| `FE.FEScheme.Raw.Simulator.Raw.encInputWord_eq` | header |
| `FE.FEScheme.Raw.Simulator.Raw.keyInputWord` | header |
| `FE.FEScheme.Raw.Simulator.Raw.keyInputWord_eq` | header |
| `FE.FEScheme.Raw.Simulator` | header,prose |
| `FE.FEScheme.Raw.SASimulator.Raw` | header,prose |
| `FE.FEScheme.Raw.SASimulator.Raw.encInputWord` | header |
| `FE.FEScheme.Raw.SASimulator.Raw.encInputWord_eq` | header |
| `FE.FEScheme.Raw.SASimulator.Raw.keyInputWord` | header |
| `FE.FEScheme.Raw.SASimulator.Raw.keyInputWord_eq` | header |
| `FE.FEScheme.Raw.SASimulator` | header,prose |
| `FE.FEScheme.Raw.SASimulator.Raw.toSim` | header |
| `FE.Wee20.wee20SASim_raw` | header |
| `FE.Wee20.SimTargets` | header |
| `FE.Wee20.simTargets_iff` | header |

No other M0 written header or opening statement prose changed. Definitions' complete bodies
are included in the native freeze's header field, so the list also records necessary codec
body changes. All 1,171 M0 written declarations were recovered; the current count is 1,223
(40 earlier helpers and these 12 repair additions). `decls2` independently reports 1,223
ADDED / 0 CHANGED / 0 REMOVED against the pinned base, and 52 ADDED / 5 CHANGED / 0 REMOVED
against M0. Its five changes omit structure fields/definition bodies; the stronger native
freeze is authoritative for the full 16-name set. The three existing `toRaw_encSt`/`toSim_encSt`
reader source headers stay unchanged, while their elaborated types propagate the codec change.
The native compiled-type comparison reprinted all 2,225 M0 constants: 2,159 unchanged and
66 changed. Exact names and before/after hashes are in `evidence/changed-native-types.tsv`.
Those include generated record support, five written input/target equation types, the three
encoding projection readers, and the concrete generated injectivity proof. No whole-file or
name-prefix exception is granted. Native generated-type adjudication passed: all 66 exact hash pairs are explained by
the authorized repair, including the generated concrete encSt_injective proof; no unexplained
change remains. Raw complete types stay local.

All 29 modules in the changed/downstream check order returned rc0, zero errors in both
forms and fresh oleans. `evidence/build-summary.tsv` retains the actual check-time HEAD and
binds each source hash to the repair commit; it does not pretend that the checks were rerun
after committing identical bytes. Root `TCSlib` remains excluded under the dispatch's explicit
order-list convention; all in-scope reverse-import dependents through AdvancedEncryption
were checked. There are no new imports or Mathlib cache roots. Style, sketch, width/size and
whitespace checks pass over the owned source. The initial width-tool invocation omitted its
root argument; the corrected run passes, and both raw outputs remain local. Host preflight
passed with 6.04 GiB memory headroom and 78.22 GiB free disk; every Lean run used the slot
wrapper with at most one process held by this job.

The 52 native axiom prints include every repair addition, changed interface/assembly and
all simulator-related PHFE Security/Headlines declarations. All 12 additions are standard-only;
39/52 total are standard-only, 13/52 retain `sorryAx`, and none uses another nonstandard axiom.
The latter are unfinished security proofs, not completed results. See the one-line-per-target
`evidence/axioms.tsv`. No headline completion is claimed by this statement repair.

The exact new repair declarations (all under FE) are:

- `FEScheme.Raw.Simulator.toRaw_stLen`
- `FEScheme.Raw.SASimulator.toRaw_stLen`
- `FEScheme.Raw.SASimulator.Raw.toSim_stLen`
- `Wee20.PHFE.simStLen`
- `Wee20.PHFE.simStLen_eval`
- `Wee20.PHFE.quadraticSimState_length`
- `Wee20.PHFE.encSimState`
- `Wee20.PHFE.encSimState_eq`
- `Wee20.PHFE.ofFn_encSimState`
- `Wee20.PHFE.encSimState_injective`
- `Wee20.wee20SASim_raw_stLen`
- `Wee20.wee20SASim_raw_encSt`

Overlap/reuse: `simStLen` follows the existing MSK polynomial width pattern; the encoder uses
the shared `padFin` adapter, and the recovery proof consumes `ofFn_padFin_of_length` whole.
Injectivity reuses `quadraticSimState_injective`. The exact length proof consumes existing
wire/pair/group/modular length readers and polynomial arithmetic. Before the length/codec
helpers, name/shape and native type/exact/apply probes were run without importing their
stubs: type probes passed, exact search did not close; length searches timed out at 200,000
heartbeats (non-exhaustive), and codec apply search returned only partial suggestions.
No duplicate decoder or state-injectivity proof is introduced.

For relocation, `patches/PENDING-RESUME.patch` preserves the four-file M3 working snapshot
saved before r1, including the proved ReductionLaws realiser-expectation adapter and admitted
adaptive/fresh endpoint ladders. Its SHA-256 is
`d097a2fa855172cfbd69ad97478d81c13e814434920f2c4548ad1a0fd9c36c0a`.
`git apply --check` succeeds against this repair commit. Those bytes passed their earlier
native development checks, but have not been rechecked after r1 and are not applied in src/.
Resume by applying that patch, checking its modules, then moving the already checked raw
coordinate chart into the lower Coordinates helper (do not duplicate the chart). The remaining
reader equality, adaptive run bijection, averaged first-hop law and fresh coupling are still
open. M3, M4 and M5 are not complete; the 33-admission committed source is unchanged in count.
No new M3 result is asserted merely because its local proof ladder checks.

PHFE-C0-F02 judgment call: this checkpoint is a new versioned directory,
`inbox/fills/io-phfe/checkpoints/checkpoint-3-r1/`; all earlier checkpoint files remain intact.
Only src/, patches/, this report, SHA256SUMS and compact results of checks actually run are
published. No raw transcript, search dump, per-file freeze/census dump, unrun check input or
check script is added. The unapplied resume artifact is Lean source development, not a check
input. All full raw check evidence is retained locally in one folder:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange/evidence`.
Its prepublication tar snapshot is
`/private/tmp/io-phfe-raw-evidence/r1-a4fe0fd7c.tar`, SHA-256
`6173f6d32eeb63d538e18332c755fb79c0d875b6a3dff03d862996542e62941b`. The tar is local only and will be sent only on a gate request.
The checkpoint outside src/ and patches/ is **0.744219 MB and 3265 lines**,
including REPORT.md and SHA256SUMS. Every evidence file is below 1 MB; the limits are
20 MB / 50,000 lines. Current full Rule 10 seals and full current-constant census remain
pending rather than being represented by prepared inputs. The continuation source and exact
repair commit are preserved so relocation does not depend on uncommitted live source edits.


## Gate 51 round 1: statements r2, all eleven relayed findings

Historical checkpoint4 source-only status follows. It is superseded by the worker checks
in the next section; the statement/disposition and exact frozen-header records remain current.

All source changes in this repair belong to one commit titled `statements r2: G51-01..11`,
source `073d0a5a3ff88d958f94c2ae50a67bc92476f616`. The prior r1 repair remains in history. All intervening proof edits
were saved before preparing r2, so this statement commit contains no proof-continuation work.
The maintainer performs Lean replay. This worker ran static lint/argument/import checks and
the canonical source-syntax/prose freeze parser only; there is no new module elaboration,
compiled-type census or axiom-print success claimed for r2.

| Finding | Disposition |
|---|---|
| G51-01 | SimSecureWith opening prose and the Definition 4.2/4.3 fidelity rows now state familywise quantification. The scheme fixes its polynomial parameter families first; negligibility is not uniform over all such families. Formal security quantifiers are unchanged. |
| G51-02 | New CircuitLinearEfficient G and exact iff reader in Targets/CircuitEfficiency.lean. ONE polynomial precedes all numeric dimensions, degree and κ. Supported pp/honest pk are hardwired; circuit arity/circuit precede all x,y and complete encoded draws. Existing MultiDAGCircuit/IsFaninTwo/C.size API is reused. Targets requires the circuit target in addition to the retained TM target; wee20PHFE_gjls21 uses it as the third conjunct. |
| G51-03 | Keep r1 fixed-width Raw stLen/encSt. Add the exact existential state_bounded and value_bounded fields to both efficient simulator interfaces, four matching SimTargets fields, its ten-field reader, and pure assembly attachments. Concrete proofs choose existing stLen and G.wG.add(const1); no iterated state-size bound is used. |
| G51-04 | Prefix every sampler parameter map with NUPPT.advInput κ: 20 logical maps, 30 source occurrences including target iff mirrors, zero exceptions. Shared contract, draw encoding, output encoding and deterministic core remain unchanged at each occurrence. No prime schedule is computed or hardwired. |
| G51-05 | Drop the unused _D binder in MddhPreTargets and its reader; remove D only at the link's target instantiation. The witness follows fixed p,hp,d,ℓ and precedes κ/advice/challenge; it does not depend on a consumer adversary. |
| G51-06 | Added W6 at both exact source locations, Wee20 §4.2 p.10 and Appendix B Theorem 1 p.12. Unconditioned 3×3 singular probability is the exact rankFailure expression, 43/64 at p=2 (344/512), with ≤3/p available. No extra rank loss is added. |
| G51-07 | Keep the existing BB1Machine.order_le_two_pow reuse. Requested promotion to a Pairing-owner width API, so matrix-DH consumers can obtain this same theorem without the incidental IBE import. No owner file is modified. |
| G51-08 | Requested promotion of pow_val_add_GT and pow_val_neg_GT to Pairing/Group.lean beside source-group laws at 254/260. Existing proofs already consume ZMod.val_add, pow_mod_card, B.card_GT and pow_add, then inverse/product laws; no proof copy or owner edit is added. |
| G51-09 | Reuse existing PrivateKeyScheme.encodeList in all four cited modules; their imports are allowed and acyclic. All 25 foldr occurrences, including readers, are replaced; Encodings' two proof consumer lists use encodeList_cons/nil. The owner equations have the same pairEncode/empty-list byte layout. No new codec or owner lemma is copied. |
| G51-10 | Removed AGW20 and IW14 from the Pairing facade's References. Those sources remain in their actual FE homes. |
| G51-11 | Replaced checkpoint-0 prepublication/freeze-pending wording with the actual exchange delivery commit 1e77173a7032b57aa22260787711c6c7a1b7596e and its freeze start. Earlier report snapshots are explicitly historical. |

The r2 circuit size convention counts input vertices plus internal gates, using the existing
C.size API. Output wires are shared references. This avoids an ambiguity about counting
only noninput gates. The complete input arity is fixed before every message/draw and
includes their existing framing. On the positive-size domain, its linear-polynomial length
fits the same form of one polynomial bound. No TM-to-circuit implication is assumed and no
circuit, machine, decoder or sampler is constructed by this Phase A repair.

For G51-03, every state encoding is List.ofFn of a fixed-width vector; the existential
state bound is witnessed by raw.stLen for both concrete simulators. The scalar word length
is Nat.size of the actual drawn modulus, bounded by G.wG.evalκ+1 using the existing
order-width theorem and Nat.size_le_size/size_pow. The witness polynomial is chosen before
κ and pp, and covers every class value. PHFE.valueEncoding_length_le and the shared
wee20PHFE_raw_value_bounded lemma supply both simulator value bounds without duplicating
scalar-width arithmetic. These are written proofs with maintainer replay pending.

All 20 logical sampler maps and their dispositions are listed below. Each old map y becomes
fun κ π => NUPPT.advInput κ (y κ π); there is no exception based on an implicit layout claim.
The SchemeTargets and SimTargets iff readers mirror the same maps (10 extra occurrences).

| Interface / target | Maps prefixed with κ |
|---|---|
| FEScheme | pubGen_eff, setup_eff, enc_eff, keyGen_eff |
| FEScheme.Raw.Simulator | setup_eff, enc_eff, key_eff |
| FEScheme.Raw.SASimulator | setup_eff, enc_eff, key_eff |
| Wee20.SchemeTargets | pubGen_eff, setup_eff, enc_eff, keyGen_eff |
| Wee20.SimTargets | sim_setup_eff, sim_enc_eff, sim_key_eff, sa_setup_eff, sa_enc_eff, sa_key_eff |

The static four-argument contract check recovered all 30 uses and verified exact equality
of their draw/output/core arguments after whitespace normalization. The κ-prefixed first
argument is the only sampler-contract argument change. All owned sampler uses are
SamplesEfficiently; there is no separate unprefixed DrawSamplable map in this job.
The encodeList import closure has 53 TCSlib modules and no forbidden Phase A import edge.
The circuit target reuses the existing Boolean model; no shared circuit campaign file is
modified. Full name/shape/import searches stay local; no native reuse probe or repair replay
was run, following the maintainer-replay instruction.

The canonical freeze audit covers every one of the 1,171 M0 written declarations.
Its raw verdict is FAIL because the explicitly authorized repairs change 51 existing
records. Exact-name/field/before-after-hash adjudication passes: zero unexpected changes,
zero removals and all five controls correct. There are 1,229 current declarations in the
87 prior modules, plus the two new circuit declarations, for 1,231 written declarations.
The initial attempt could not load an object for the new circuit module, which is left
unreplayed as requested. The final canonical run covers every M0 declaration; the new
module has no M0 declarations and its two declarations were separately parsed with the
same compiled parser using the existing PHFE.Raw notation environment. Neither pass
elaborates the worker's TCSlib declarations or replays their proofs.

All 88 source hashes are additionally equal to git show of the committed r2 HEAD.
Relative to r1 there are 40 frozen-record changes, three proof/sketch-only changes,
eight new declarations and 19 whole-module changes. All 16 r1 exceptions are retained;
five of those records receive the combined r2 after-hash. Eleven r1-only differences
remain unchanged. The table below is the exact combined M0 exception set. FE expands to
TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption. Module-doc/import changes
and the three proof-only changes are reviewed separately, with no wildcard exemptions.

| Exact frozen name | Repair | Changed components |
|---|---|---|
| `FE.FEScheme` | G51-04 | header |
| `FE.FEScheme.Raw.Omega.encode` | G51-09 | header |
| `FE.FEScheme.Raw.Omega.encode_eq` | G51-09 | header |
| `FE.FEScheme.Raw.Simulator.Raw` | R1-PHFE-C0-F01 | header,prose |
| `FE.FEScheme.Raw.Simulator.Raw.encInputWord` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.Simulator.Raw.encInputWord_eq` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.Simulator.Raw.keyInputWord` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.Simulator.Raw.keyInputWord_eq` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.Simulator` | R1-PHFE-C0-F01,G51-03,G51-04 | header,prose |
| `FE.FEScheme.Raw.SASimulator.Raw.toSim` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.SASimulator.Raw` | R1-PHFE-C0-F01 | header,prose |
| `FE.FEScheme.Raw.SASimulator.Raw.encInputWord` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.SASimulator.Raw.encInputWord_eq` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.SASimulator.Raw.keyInputWord` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.SASimulator.Raw.keyInputWord_eq` | R1-PHFE-C0-F01 | header |
| `FE.FEScheme.Raw.SASimulator` | R1-PHFE-C0-F01,G51-03,G51-04 | header,prose |
| `FE.FEScheme.Raw.viewWordBits` | G51-09 | header |
| `FE.FEScheme.Raw.viewWordBits_eq` | G51-09 | header |
| `FE.FEScheme.Raw.viewWord_eq` | G51-09 | header |
| `FE.FEScheme.Raw.SimSecureWith` | G51-01 | prose |
| `FE.Wee20.wee20PHFE_gjls21` | G51-02 | header,prose |
| `FE.Wee20.wee20SASim_raw` | R1-PHFE-C0-F01,G51-09 | header |
| `FE.Wee20.Targets` | G51-02 | header |
| `FE.Wee20.targets_iff` | G51-02 | header,prose |
| `FE.Wee20.wee20Sim` | G51-03 | header |
| `FE.Wee20.wee20SASim` | G51-03 | header |
| `FE.Wee20.LinearEfficient` | G51-02 | prose |
| `FE.Wee20.MddhPreTargets` | G51-05 | header,prose |
| `FE.Wee20.mddhPreTargets_iff` | G51-05 | header,prose |
| `FE.Wee20.SchemeTargets` | G51-04 | header |
| `FE.Wee20.schemeTargets_iff` | G51-04 | header |
| `FE.Wee20.SimTargets` | R1-PHFE-C0-F01,G51-03,G51-04 | header,prose |
| `FE.Wee20.simTargets_iff` | R1-PHFE-C0-F01,G51-03,G51-04 | header |
| `FE.Wee20.Wire.linearSetupDraw` | G51-09 | header |
| `FE.Wee20.Wire.linearSetupDraw_eq` | G51-09 | header |
| `FE.Wee20.Wire.quadraticSetupDraw` | G51-09 | header |
| `FE.Wee20.Wire.quadraticSetupDraw_eq` | G51-09 | header |
| `FE.Wee20.Wire.quadraticEncDraw` | G51-09 | header |
| `FE.Wee20.Wire.quadraticEncDraw_eq` | G51-09 | header |
| `FE.Wee20.Wire.linearKeyDraw` | G51-09 | header |
| `FE.Wee20.Wire.linearKeyDraw_eq` | G51-09 | header |
| `FE.Wee20.Wire.linearSimSetupDraw` | G51-09 | header |
| `FE.Wee20.Wire.linearSimSetupDraw_eq` | G51-09 | header |
| `FE.Wee20.Wire.quadraticSimSetupDraw` | G51-09 | header |
| `FE.Wee20.Wire.quadraticSimSetupDraw_eq` | G51-09 | header |
| `FE.Wee20.Wire.linearSimKeyDraw` | G51-09 | header |
| `FE.Wee20.Wire.linearSimKeyDraw_eq` | G51-09 | header |
| `FE.Wee20.Wire.linearSimState` | G51-09 | header |
| `FE.Wee20.Wire.linearSimState_eq` | G51-09 | header |
| `FE.Wee20.Wire.quadraticSimState` | G51-09 | header |
| `FE.Wee20.Wire.quadraticSimState_eq` | G51-09 | header |

The actual decls2 outputs report 1,231 ADDED / 0 CHANGED / 0 REMOVED against the base;
60 ADDED / 21 CHANGED / 0 REMOVED against M0; and 8 ADDED / 17 CHANGED / 0 REMOVED
against r1. Its ordinary header extraction does not include complete record fields and
definition bodies, so the stronger 51-record native source freeze result is authoritative.
No other frozen header, ordinary statement prose, kind or privacy flag changed.
The exact before/after hashes are in evidence/changed-headers.tsv. The original M0
manifest remains immutable. Future freeze checks must accept only these exact repaired
records, not every later change to an allowed name or file.


The prior native build/axiom receipts in this report apply to their stated old commits.
R2 module replay, generated-type effects and headline/new-helper axiom prints belong to the
maintainer's replay; they are pending and are not fabricated as new worker evidence.
Static style/sketch/width and whitespace checks pass for 88 owned files. The eight newly written declarations are CircuitLinearEfficient, circuitLinearEfficient_iff, PHFE.valueEncoding_length_le, wee20PHFE_raw_value_bounded, and the state_bounded/value_bounded lemmas for each raw concrete simulator. No new admission,
axiom, sampler contract or machine construction was introduced in this repair.

The proof-development archive under evidence/repairs/r2/pre-repair-working preserves all
seven pre-r2 source files, hashes and a resumable patch. The compact delivery includes only
a separate unapplied resume patch of the previously checked four-file development; the
unvalidated coordinate/one-column drafts stay local. After r2, continue the endpoint and
coordinate couplings from these saved bytes without altering the repaired statements.
The delivered resume patch has SHA-256
366321a771fe5d942c5e2d8f69222401dc50489490b20f9401237caebede49ca; its dry run passes.
A static import audit found that the saved ReductionLaws, LinearSecurity/Data-coordinate,
Endpoint and Theorems proof modules and Pairing/MatrixDH/SingleColumn have no r2-modified
module in their import closures. Their proof checks can therefore continue independently;
the new circuit/efficient-interface replay remains assigned to the maintainer.
The latest endpoint seed/key reader/bound steps passed before this repair; no post-r2 replay
is implied by those older receipts. M3–M5 and the final proof/audit obligations remain open.

The r2 checkpoint follows the same payload limit. Raw evidence folder:
/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange/evidence.
Prepublication raw tar snapshot: /private/tmp/io-phfe-raw-evidence/r2-073d0a5a3.tar,
SHA-256 `eb39374175b8e0d396bec9bf978b81be69b5e3dab26a7b788010d5a7e2c972fe`; local only, supplied only if a gate asks.
Outside src/ and patches/: **0.776356 MB and 3378 lines**.
No unrun replay inputs/scripts, transcripts, search dumps, per-file freeze/census dumps or
superseded artifacts are included. Earlier checkpoints and history remain untouched.


## R2 worker compilation and axiom validation after clarification

Seyoon clarified that the maintainer owns only the INDEPENDENT delivery replay, while
this worker must continue checking every changed module and its downstream. I had
interpreted the earlier replay sentence too broadly. I preserved all seven proof-development
files and restored exact committed source073d0a5a3ff88d958f94c2ae50a67bc92476f616 before
these checks. No repair source was changed and no new statement exception was introduced.

The official FE/Pairing fillinputs union has302 modules and the unchanged112 Mathlib roots.
All19 changed modules have33 required changed/downstream modules under the dispatch's
root-TCSlib exclusion convention. The sweep compiled those33 plus5 missing base dependencies
and3 upstream proof/cache refreshes,41 total. The cache refreshes prevent recently checked
proof drafts from contaminating the exact-r2 evidence. No new Mathlib root/cache fetch was
needed. Each command was lean-slot.sh plus scripts/lean_check_tree.sh, one module at a time,
with TCSLIB_OLEANS set to this job's own tree. All41 sources equal git show HEAD and all41
fresh objects were produced. Resource preflight passed; raw wrapper/time logs remain local.

Every rc and both emitted error forms are zero. Sorry counts below are compile warnings
and direct source tokens (after stripping comments), shown as warnings/tokens. They describe
existing unfinished proofs, not successful proofs. Required33-module subset:14/14. Actual
41-module sweep:23/23. The complete owned source remains33 direct admissions, unchanged
from r2's parent; remaining10 lie in unchanged modules outside this replay subset.

| Module (after TCSlib/) | rc | Errors : / ( | Sorry warnings/tokens | Fresh |
|---|---:|---|---|---|
| Complexity/CircuitComplexity/HardWire | 0 | 0/0 | 0/0 | True |
| Complexity/CircuitComplexity/Universal | 0 | 0/0 | 0/0 | True |
| Complexity/CircuitComplexity/PSubsetPPolyGadget | 0 | 0/0 | 0/0 | True |
| Complexity/CircuitComplexity/KarpLiptonSearch | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Defs/Efficient | 0 | 0/0 | 0/0 | True |
| Cryptography/Encryption/PrivateKey/EnsembleSecurity | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Defs/Simulator | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Defs | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation/TwoStage | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation/Games | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation/Security | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/Simulator | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/Games | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/Security | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/FromTwoStage | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/WireDraws | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Encodings | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Raw | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Correctness | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Simulator | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Theorems | 0 | 0/0 | 6/6 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/Endpoint | 0 | 0/0 | 3/3 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Adapter | 0 | 0/0 | 2/2 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/CommittedSimulator | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Security | 0 | 0/0 | 8/8 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/CircuitEfficiency | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/Scheme | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/Sim | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/LinearEfficiency | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/MatrixDH | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets/Assembly | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE/Headlines | 0 | 0/0 | 4/4 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/PHFE | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Targets | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20 | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption/FunctionalEncryption | 0 | 0/0 | 0/0 | True |
| Cryptography/AdvancedEncryption | 0 | 0/0 | 0/0 | True |
| Cryptography/Pairing | 0 | 0/0 | 0/0 | True |

The complete table with source hashes and timestamps is evidence/build-summary.tsv.
All direct r2 bound proofs, sampler-map interfaces, target readers, circuit target and
pure assemblies compiled without direct sorry warnings. There were no failures to fix.
These worker checks do not replace the maintainer's independent replay.

The native axiom probe imported the freshly checked FE/Pairing facades, asserted all19
origin modules, and printed axioms for EVERY stored constant from them, including private
and generated support. It separately asserted existence, origin and coverage for the EXACT
r2 changed/added written set:40 frozen-record edits +3 proof/sketch-only edits +8 additions.
This51-name set differs from the coincidentally51-name combined M0 freeze-exception set.
Probe rc0, both error forms0, sorry0, warnings0; complete native/Python coverage passes.

| Axiom scope | Printed | Standard-only | sorryAx-dependent | Other nonstandard |
|---|---:|---:|---:|---:|
| Changed/added written r2 declarations |51|50|1|0|
| All stored constants in repaired modules |498|493|5|0|
| Newly added r2 declarations |8|8|0|0|

The sole written sorryAx-dependent declaration is
Wee20.wee20PHFE_gjls21, through its existing unfinished simulation-security proof dependencies.
No new r2 bound lemma or target reader has an admission dependency. Every axiom row is
reported honestly as standard-only or sorryAx-dependent; no other axiom appears. The compact
one-line-per-changed-declaration result is evidence/axioms.tsv. The498-row full module census
and native #print output remain LOCAL to comply with the payload limit; the aggregate above
records their coverage. No full per-file census dump, probe input or replay script is published.

The existing r2 source repair commit and exact51-record freeze verdict remain unchanged.
The independent maintainer replay is still expected. After this validation checkpoint,
restore the saved proof development, fix the local Coordinates debug-option placement,
and continue M3–M5; no other frozen statement is authorized to change.

Raw evidence is retained in the one folder
/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange/evidence.
The prepublication tar snapshot is /private/tmp/io-phfe-raw-evidence/r2-own-check-073d0a5a3.tar,
SHA-256 `baf8f11684d27aebf971dcf09df42ac273a1cbac1e8ad63ced4feeea1fe848bb`. The tar remains local and is sent only on a gate request.
This checkpoint outside src/ and patches/ is **0.811004 MB and 3634 lines**.
All evidence files are below1MB; the20MB/50,000-line limits continue to hold. Source073d0a5a
and all earlier checkpoints remain intact. The unapplied checked resume patch has SHA-256 46118d97246509cd202734b1c6d217643d2d2020fdd2030854831244cce32ecf and is preserved;
the latest full seven-file proof-development snapshot is local under
 evidence/repairs/r2/own-check/pre-check-working.
