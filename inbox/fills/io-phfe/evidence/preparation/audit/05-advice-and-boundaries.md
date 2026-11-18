# Advice dimensions, exact reductions and static boundaries

This audit changes no live Lean source. The machine-readable snapshot is deliberately
PRE-FINAL while the root is elaborating. Do not mistake it for final-HEAD evidence. Root
requested no inventory regeneration until final HEAD; source hashes/positions in snapshot.tsv
therefore identify exactly the material originally scanned. Later repairs are noted below.

## Pi tape: complete offset audit

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

## Outer tape and reductions

| Item | Exact shape / audit result |
|---|---|
| Outer tape length | 3n1+3n2+4. A1 uses2n1; A2 next2n2; s1,s2 next4; uniform y1 nextn1; uniform y2 nextn2. Last exclusive coordinate is exactly total. |
| Fixed group M | Rows=2*n2+n1*2; columns=n1*n2. Top A1⊗I_n2, bottom I_n1⊗A2. Honest encryption only knows A1,A2 as GROUP data. |
| First MDDH | one response column, n1 base rows. A1=base^T, y1=response(:,0)*g^z1. Known A2,s2 yield scalar y2; crossLeakLeft uses group y1 with scalar y2. |
| Second MDDH | one response column, n2 base rows. A2=base^T, y2=response(:,0)*g^z2. Already-uniform scalar y1 is advice; crossLeakRight uses it with group y2. |
| Basis handling | Both use total Pi simulator even on singular H; no outer rank filter and no extra rank slack. |
| Typed derived adversary | toLinear has exactly original coins and total budget. replayLinear preserves actual reachable typed histories; malformed mismatched histories return false. No uncomputable group-word decoder. |
| Generic wire adapter | PHFE replay uses original x/y/f words and List.foldl; checks typed query and key-index agreement, encodes actual Option responses, retains original f in returned key. Mod-p aliases do not collapse in adversary transcripts. |

## Advice encodings and quantifier audit

| Family | Finite/inhabited / width | Quantifiers / permitted computation |
|---|---|---|
| L1 MddhAdvice | Fin(dκ+1) sentinel index; L:rows×3, S:2×d, U:rows×d over ZMod(pκ). Zero matrices plus sentinel inhabit d=0. | hp gives NeZero pκ locally; no extra assumption on p. Numeric κ,d,rows headers. Preprocessor forms LA0 and Lc using known scalar powers of canonical DLIN group points. |
| Pi Advice | Scalar vector of securityCount over ZMod(pκ), nonempty zero; finite via shared orderSchedule_neZero. | ∀typedA ∃ωκ BEFORE ∀D realiser and ∀κ. Advice cast uses ringEquivCongr, not a local scalar extraction map. |
| Pi word bound | 4κ+4l+4n+4z+4Q+2b+40 +securityCount*wG. | Pair-header arithmetic checked: enc has twice metadata length plus2 plus vector. Numeric bits≤value+1 gives exactly constant40. |
| MaskAdvice | Vector length3n1+3n2+4 over fixed pκ. | Used only as fixed known outer randomness in toLinear; no sampling inside derived adversary. |
| Mask word bound | 4κ+4n1+2n2+20 +maskCount*wG. | Header actual bound constant16; stated20 is safe. |
| Full outer Advice | MaskAdvice × Pi Advice; zero pair inhabits, hp gives finiteness. | Enc pairs the two component words; length bound2*maskAdviceLen+2+Linear.adviceLen. |
| Core outer bound | ∀typedA ∃mask φ ∃twoPiω ∃twoOuterω ∀fourD, four explicit RealizesOn premises→∀κ bound. | No assumption that every typed adversary is computable. Advice may depend on A, never on chosen realiser. |
| L2 corollaries | Wee20RealizableSA quantifies only FE.toSAAdv q; Wee20Realizable43 only TwoStage.toSA q. | Correctly avoids the false all-typed-machine-existence premise. Honest efficiency is separate. |
| Shared RealizesOn | coins equality AND output equality only at encκ(challenge) and r.length=layoutκ. | No malformed/raw input behavior is constrained. Advice is fixed inside R, never read back from D's own advice. |
| DLIN composition | ∃L1 advice after four MDDH machines, then ∀DLIN realisers. | Response-column factors1,l,1,1. Exact Pi rank loss+3*mddhSlack(p,1)+mddhSlack(p,l). No second matrix-presentation loss. |

The L1 real canonical A0 has rank failure p⁻²; augmented random matrix determinant is
ab(t−r−s), with failure1−(1−1/p)^3. The sum is3/p−2/p²+1/p³≤4/p per column. The named safe
slack is4d/p. A SINGLE chosen-column machine suffices, avoiding a nonuniformity problem from
summing an ever-growing arbitrary family of negligible advantages.

## Static boundary snapshot and repair tracking

The first scan covered67 Lean files,13,255 lines,1,143 explicit source declaration headers
and145 sorry occurrences. Admissions are expected at M0 but forbid a final PROOFS delivery.
This header count excludes generated declarations and is not StmtDump/census evidence.

| Static category | Initial snapshot | Current interpretation |
|---|---:|---|
| Prohibited direct imports (Programs,RAMSimulation,Games.Closeness,unapproved CoinSampling) | 0 | Contract is reused; Efficiency/Contract are the only allowed direct coin imports. |
| New RealizesOn/SamplesEfficiently/DrawSamplable/CoreComputable variant | 0 | Shared APIs reused. |
| New axiom/admit/native_decide code token | 0 | sorry exists only as M0 admissions. Axiom census still required after proofs. |
| Global simp attributes | 0 | Reader declarations carry no global simp. |
| PolyHandler/exists_handlerMachine code token | 0 | No PhaseB construction. |
| Bare exists-NUPPT.Computes efficiency | 0 | Honest fields use uniform PC/shared sampler contract. |
| PDF path in base-to-head changed paths | 0 | Source PDFs remain user-supplied originals, never copied. Delivery ZIP scan remains a root final step. |
| Extraction-sensitive token | 1 | PHFE.Data embedValue_injective used pow_val_bijective.injective in a PROOF, not an inverse algorithm. Root is moving the same declaration to proof-only PHFE.Embedding; disclose there. |
| >100-column lines | 2 | PHFE scratch Security lines290/307. FE agent reports final formatting now max99; no snapshot regeneration until final HEAD. |

### Open checks / findings before push

1. **Verified citation repair:** Wee20 Theorem1 is AppendixB p12, not p8. Two stale prose
   locations were sent to root (LinearSecurity.Fresh and QuadraticSecurity.Theorems). No
   statement/proof changed in this audit; root should repair before freezing prose.
2. **Exact?/apply? overlap probes remain pending root.** Static searches and disclosed
   near-copies do not certify this mandatory check. Likewise no Rule10 seals/controls,
   axioms, StmtDump, final widths or frozen-header test was run by this agent.
3. **Fresh endpoint bridges are substantive M0 obligations.** Do not claim source security
   merely from padded endpoint selectors/game0_real_accept. The actual Fresh/Endpoint
   definitions and nontrivial law equalities now exist, but their admitted proofs remain.
4. **Do not advertise literal all-size linear efficiency.** The positive-size guard is the
   authorized source-domain reading; raw zero-dimensional correctness/security stay total.
5. **Common subexponential exponent:** choose it before A,q from DLIN's common exponent,
   then use the explicit composed inequality and polynomial absorption. The FE agent has
   corrected proof sketches; per-dimension existential hardness alone is insufficient.

No additional false/vacuous mathematical statement was found in the reviewed game formulas,
quantifier orders, tape accesses, class domain, or efficiency targets. This is a static
statement review, not a proof of all admitted claims or a successful Lean/Rule10 run.
