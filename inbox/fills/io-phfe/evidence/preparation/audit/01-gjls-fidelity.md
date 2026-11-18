# GJLS21 fidelity table: primary statement gate

Snapshot status: M0 statements, not proved security/correctness. Live worktree takes precedence
over older scratch code; the newly delivered PHFE Adapter/Security/Headlines drafts supplement
it. Paths below are relative to TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/
unless explicitly marked Pairing. Every source fact in this table was checked against the
verified local source extract and complete page images. GJLS printed page = PDF page minus 4.

## Definition 4.1: syntax (printed p19 = PDF23)

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

## Definition 4.2: correctness (printed p19 = PDF23)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| All polynomial parameter families, all messages, all represented functions. | Raw.Correct; PHFE.class_eval_eq; wee20PHFE_raw_correct. | Perfect equality for every honest draw is stronger than the source probability bound. Statements cover arbitrary wire words, including noncanonical residue aliases. |
| pp,setup,enc,key randomness in the prescribed order. | Raw.honestRun and its reader; raw setup/enc/keyGen laws. | Actual finite core-plus-draw laws are used; no simulated/padded endpoint is substituted for correctness. |
| Dec equals the functionality output except negligible error. | wee20PHFE_raw_correctExcept_zero; efficient wee20PHFE_correctExcept_zero. | Zero error, output in GT via injective embedValue. These substantive raw correctness laws are M0 obligations. Efficient transport is a pure assembly consequence. |
| The real class uses all field residues. | phfeClass_eval_encoded with p≤2^w; PHFE decoding and width readers. | Wire evaluation is total modulo p for all words. Encoding completeness uses the existing reachable-group width lemma, not an arbitrary-modulus promise. |

## Definition 4.3 and Remarks 4.3/4.5/4.6 (printed pp19–20 = PDF23–24)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| One simulator is chosen before every adversary. | Raw.SimSecure := ∃ Sim : Simulator S, S.SimSecureWith Sim.toRaw. | Efficient Simulator has setup_eff/enc_eff/key_eff. Raw With predicates name the one fixed simulator rather than asserting an efficient instance. |
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
| Many-key: all polynomial q. | SimSecureWith quantifies ∀ TwoStage ∀ q:PolyExpr. | One simulator independent of q. TwoStage.toSA uses q+1 TOTAL calls (one challenge plus q keys). |
| Subexponential variant. | SubexpSimSecureWith/SubexpSASimSecureWith and SubexpDLIN. | One positive exponent is chosen before adversary and q; shared SubexpSmall/SubexpHard APIs, not a local notion. |
| Derive this committed notion from the semi-adaptive bound. | SemiAdaptive/FromTwoStage: TwoStage.toSA, simAdv_eq_saSimAdv; PHFE.wee20PHFE_simAdv_le. | Applies the typed core to the actual converted adversary. No abstract SASimSecure→SimSecure theorem requiring an unbuilt machine. |
| Efficiency and reduction realizability are distinct. | Wee20RealizableSA/43 and MDDHRealizable vs Scheme/Sim/PG targets. | SA realizability ranges only over FE.toSAAdv q; committed only TwoStage.toSA q. It never quantifies over every uncomputable typed SAAdv. |

## Definition 4.6 (printed p22 = PDF26)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| One polynomial factor before all polynomial function parameters. | Targets/LinearEfficiency.LinearEfficient: ∃ one FinTM,∃q,∀numeric ℓ,n,d,κ,... | Stronger uniform formulation: one machine works across dimensions, with numeric ℓ,n encoded. q depends only on κ, not degree or dimensions. |
| Circuit size bounded by (|x|+|y|)poly(κ). | Literal positive-size target (ℓ+n)*q.evalκ. | Scalar bit width is absorbed into q. It is a Phase B target, **not a theorem that this machine exists**. |
| pp and keys range over honest support. | Target quantifies over all typed pp,pk and every complete draw. | Stronger all-typed-key form; no hidden support restriction weakens the target. |
| Source positive message-family domain. | Explicit guard 0<ℓ+n. | **Disclosed source-domain reading**: at ℓ=n=0 a literal zero-step target cannot emit even the constant nonempty ciphertext. Raw algorithms/correctness/security remain total at zero; only this multiplicative efficiency target has the guard. |
| Uniform input and public modulus. | PHFE.linearEncInput gives unary κ, numeric dimensions, pp,pk,x,y,whole draw. | Modulus is read from pp; no hardwired/evaluated p(κ). Degree is unused by encryption, so it need not be a header. |
| Concrete width evidence. | PHFE.ctLen_eval; wee20PHFE_ctLen_eval; mpk width readers. | CT is (6n+5)wG bits, excludes public x, independent of ℓ,d. MPK is (16+24n+8ℓ)wG+10 bits in the actual nested-pair codec. |

## Section 9 required class (printed pp57–58 = PDF61–62)

| Source clause | Lean counterpart | Reading / status |
|---|---|---|
| x,y in field vectors of a polynomial common dimension. | phfeClass ℓ n w d; specialize ℓ=n for the literal source form. | Separate dimensions are a parameter generalization, not a loss of the source class. |
| GT output [Σ_j,k f_jk(x)y_jy_k]_T. | phfeEval_sum; phfeClass_eval; PHFE.class_eval_eq and embedValue. | The exact private quadratic expression is preserved, including cross terms and coefficients; no change to linear private computation. |
| Each f_jk has constant public degree. | PolyTensor p ℓ (n*n) d and polyTensorEval, xhat=(x,1). | d is a fixed natural family parameter. Ordered padded tuples encode all public polynomials of degree≤d. This intentionally restricts Wee20's broader ABP/NC1 class to GJLS's required class. |
| Degree at most two may contain affine/constant private parts in applications. | BidegreeAtMost and pad_one completeness theorem. | Homogeneous private quadratic form after appending a constant-one private coordinate; actual completeness is ∃tensor for each bidegree-bounded MvPolynomial, not a tautological padding equality. |
| The class implements structured PRG evaluation. | pad_one and class embedding; external consumer is not built here. | §9 implementability observation is represented by a polynomial-class bridge; no IO/sPRG theorem is claimed in this unit. |
| Unbounded collusion means every polynomial number of keys. | many-key SimSecure/SA bound and q parameters. | Does not mean an infinite transcript or unbounded runtime. |
| Main source conclusion consumes linear efficiency plus many-key simulation. | PHFE/Headlines.wee20PHFE_gjls21. | Conjunction: CorrectExcept0, SimSecure, LinearEfficient, under Targets, machine-derived L2 realizability, fixed order and DLIN. Public hypotheses are explicit; Phase A does not construct the targets/machines. |

No new false/vacuous statement was identified in these source-to-header comparisons. All raw
correctness/security/probabilistic endpoint laws still require proofs after the statements gate.
