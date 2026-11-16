# Gate 40 — pairing campaign statement audit

**HOLD. Counts: 0 blockers, 2 majors, 4 minors, 0 notes.**

The four target statements have sound mathematical routes, and T2–T4 suffice for the stated
BB1 security theorem with its existing hypotheses. The hold concerns an unfaithful generic
serialization interface and missing required Rule 10 evidence. No mathematical error was found
in the completed Joux/group/BB1 proofs. Their Rule 10 clearance remains qualified below.

| Audited item | Pin |
|---|---|
| Repository / draft PR | [Shilun-Allan-Li/tcslib #331](https://github.com/Shilun-Allan-Li/tcslib/pull/331) |
| Lean head | `110c2f9db810d243693b9a5e8976a5ad205f1bab` |
| Campaign records | `356321accdd29b9ec73391b1c7b211b7d4cabf0f` |
| Exchange | `870bed6ca6d79f43599ab2972f74834137672b2a` |
| PR merge base | `523d80d2d4dd8e4ed6799358831e5b3806c6187b` |
| Pack | `outbox/gates/40-pairings-statements-gate/` |

The live GitHub metadata confirmed the requested draft/head. This audit made no repository
changes, dispatches, reviews, or merges. The shared-facade conflict and the listed merged-tree
rebuilds are maintainer merge conditions, outside the audit verdict.

## Findings

All Lean paths below are relative to `TCSlib/Cryptography/` at the audited head.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G40-01 | **major** | `AdvancedEncryption/IdentityBased/Defs.lean:99–136,161–170,233–256` · `IBEScheme`, `Correct`, `sidImpl` | Arbitrary lossy encodings can make a plaintext-revealing, typed-correct scheme satisfy `SIDSecure`. | Exact countermodel below; no encoding inverse, injectivity, or compatibility law is present. | Add a faithful serialization contract on reachable, context-valid objects and instantiate it for BB1. Preserve Q5's deferral of efficiency. |
| G40-02 | **major** | `verification/round1/tools/seal.py`; `evidence-extracts/rule10/modules.txt` | The hand-list seals do not meet the campaign's required Rule 10 coverage for the other substantive modules. | The canonical suite covers three modules, including one declaration-free facade. The four other modules containing completed proofs have only hand-picked lists. | Run the term-collected, closure-complete owner seals and explicit-unfold scan on the missing substantive modules, with verified source binding and controls. |
| G40-03 | minor | `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean:61–71` · T4 sketch | The sampler parameters do not justify the claimed error from the stated width bound alone. | `statClose_sampleBelowL` requires `p < 2^n` and uses `Nat.size p` bits inside each block; neither a trial count nor a sufficient block width is specified here. | Give explicit parameters as below. No change to T4's statement is needed. |
| G40-04 | minor | `BonehBoyenMachine.lean:54–71`; `Pairing/Assumptions.lean:200–205`; `Pairing/Group.lean:84–85,146–150` | Some declaration-level source text is missing or inaccurate. | T4 has no declaration-level source tag; T1 attributes an implicit “stronger assumption” assertion absent from the excerpt; `bilinear_pow` quantifies over naturals, although the bundle docstring says it derives the integer formula. | Add T4's source tag; describe T1 solely as the independently derived folklore implication; distinguish the natural-exponent reader from the signed-exponent consequence of the homomorphism fields. |
| G40-05 | minor | `AdvancedEncryption/IdentityBased/BonehBoyen.lean:173–198,264–293` · `decrypt_encrypt`, `bb1_correct` | The two substantive BB1 correctness proofs have prose sketches but omit the policy's standard sketch marker. | Both docstrings already explain the actual proof. | Mark those existing paragraphs `**Proof sketch.**`. No mathematical rewrite is required. |
| G40-06 | minor | `briefs/pairings/README.md` current checkpoint; current identity/status summaries; PR description checks | Current status and seal coverage are not presented accurately enough. | The current checkpoint still names `ce9c3728` and “not pushed”; the PR's “12/12” is a probe count for three modules, not full campaign coverage. | Refresh current summaries to the pinned head/base and state the three-module coverage explicitly. Preserve genuinely historical decision-log and provenance entries. |

### G40-01: the typed IBE game can hide the entire ciphertext

This is a fidelity defect in the generic interface, separate from the approved absence of an
efficiency field. Q5 does not authorize losing the objects supplied to the adversary.

Consider the following instance, at every security parameter:

1. All five length polynomials are the constant `1`. The identity and message sets are
   one-bit strings. Parameters, master keys, and private keys are singletons. Ciphertexts
   are one-bit strings. Every message is in `MsgSpace`.
2. `setup` and `keyGen` return the unique values. Define

   $$
   \operatorname{enc}(\kappa,\ast,ID,m)=\operatorname{pure}(m),
   \qquad
   \operatorname{dec}(\kappa,\ast,c)=\operatorname{some}(c).
   $$

3. Set all three wire encodings, particularly `encCT`, to the constant zero bit:

   $$
   \operatorname{encCT}(\kappa,c)=0
   \quad\text{for both }c=0,1.
   $$

The interface permits this instance. Its typed correctness is immediate:

$$
\operatorname{dec}(\kappa,\ast,\operatorname{enc}(\kappa,\ast,ID,m))
=\operatorname{some}(m)
$$

where the deterministic `pure` computation is identified with its returned value.

In the encoded `sidGame`, couple the two experiments using the same adversary coins.
Induct on the remaining query budget. Before `Init` both return zero on the other oracles;
`Init` returns the same zero parameter encoding; `KeyGen` returns either the same bottom
or the same validity-bit/key encoding. A first challenge records zero in both games, and
every later challenge returns that recorded zero. Thus identical query histories yield
identical next answers and identical next histories. Return and timeout also agree. Consequently,
for every adversary, budget, and parameter,

$$
\operatorname{advantage}
  (\operatorname{sidGame}(A,q,0,\kappa),
   \operatorname{sidGame}(A,q,1,\kappa))=0.
$$

The instance satisfies `Correct` and `SIDSecure` with error function identically zero.
In BB04's typed experiment the adversary instead receives the ciphertext `m_b` itself.
Choosing messages `0,1` and returning that ciphertext gives distinguishing advantage `1`,
or guess advantage `1/2`. It is a constant-time plaintext encryption example, so honest
efficiency would not repair the discrepancy.

**Required repair.** Relate the wire views to the typed objects. One sufficient formulation
provides decoding left inverses on reachable public parameters and on keys/ciphertexts in
the context of those parameters. Another formulation makes the honest operations, including
correct decryption, factor through the advertised encodings. Do not demand global injectivity
on BB1's unrestricted dependent-pair types: its key and ciphertext encodings intentionally omit
the description, which is known from the parameters, and its public-parameter type also
contains unreachable descriptions of arbitrary length.

For BB1 the intended contextual contract is available: generated descriptions have their exact
advertised length, and each fixed-description group encoding is injective. Concatenation at the
advertised widths loses no component on those reachable objects. The missing point is a
published contract linking that fact to the generic interface and security claim. This finding
does not supply a counterexample to T1–T4 or to BB1's particular algebra.

### G40-02: necessary seal evidence is missing

The pinned `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` `3 requires seals collected from
elaborated terms, including matchers, rather than hand-picked names; its tooling section also
requires the statement/definition-body sweep, whole-file proof seal, controls, and explicit
unfold scan. This is a pre-existing acceptance requirement, not a newly imposed test.

The twelve canonical probes are genuine source-preserving probes of:

- `BonehBoyenMachine`;
- `BonehBoyenSecurity`;
- the `IdentityBased` facade.

I reconstructed every original source by removing the manifest's recorded insertions, verified
the insertion/probe/source hashes, and matched the results to the pinned source bytes.
The supplied summaries report successful install/EOF checks for all twelve probes.
That establishes the reported coverage, not coverage of the imported proofs.

`Group`, `Joux`, `Defs`, and `BonehBoyen` contain completed proofs but have only the round-1
hand-list probes. `Assumptions` and `Operations` also need the applicable declaration/body
coverage. The “unknown constant” messages in three round-1 logs really concern names outside
the relevant closure; I do not misclassify them as failed theorem proofs. However, ignoring those
messages does not turn an incomplete name list into the required collected seal.

In particular, the one negative `Correct` control verifies that control, not completeness of
the foreign-definition inventory or protection against instance-related reduction. Canonical
sealing a downstream import does not re-elaborate the imported theorem bodies.

I found no explicit forbidden foreign unfold in the completed proofs on source review.
The `simp [sidImpl]` and `simp [bb1SimKeyQ]` calls unfold definitions in their own files,
which is allowed. The major is the missing required evidence, not an allegation that one of
those proofs is mathematically unsound.

### G40-03: make the sampler route precise

The upper bound from injectivity is only

$$
2\le p\le 2^{G.wG.eval(\kappa)}.
$$

Reading the entire advertised width on each rejection trial can have very poor acceptance
when encodings are padded. For example, `p = 3` and `wG(κ) = κ+2` give acceptance
`3/2^(κ+2)` per such trial. Polynomially many such trials need not sample nearly uniformly.
Also, `p ≤ 2^wG` is insufficient for the strict premise of the cited sampler theorem;
the equality case `p=2, wG=1` is allowed.

A uniform repair using the existing lemma is to take

$$
n=\kappa+G.wG.eval(\kappa)+1
$$

and use `sampleBelowL p (Nat.size p) n n`, with fallback `0`, on `n²` fresh coin bits.
Then `0 < p < 2^n`, and the existing bound is

$$
(1/2)^n\le 2^{-\kappa}.
$$

Allocate independent blocks for at most `q(κ)+1` draws. The statistical error is at most
`(q(κ)+1)2^(-κ)`, as claimed. This also handles small-order and residue-collision instances:
the arithmetic implementation must return the field inverse of zero as zero.

## Definitions and source fidelity

| Surface | Audit conclusion |
|---|---|
| Bilinear bundle | Equal prime orders, a nonidentity source generator, a bimultiplicative pairing, nondegeneracy, and injective element encodings match BB04 `2.2. Prime order supplies cyclicity; the homomorphism fields also imply the signed-exponent law. G40-04 concerns the reader's advertised domain only. |
| Generator | Uniform `NUPPT` generation, exact polynomial description lengths, total description interpretation, and explicit exceptional-order hypotheses implement Q1. Group-operation efficiency is separated as ruled, rather than silently assumed in the abstract bundle. |
| BDH / DBDH | The public generator is uniform in `G∖{1}`; exponents are independent uniform residues; random `T` is uniform in the target group. Generator coins are sampled first, so there is no dependent-seed weighting distortion. Nested input pairing and exact encoded BDH success match D3. Absolute decision advantage is disclosed and harmless under complement closure. |
| IBE interface | Four typed algorithms, parameter-dependent messages, fixed polynomial wire widths, and the two-experiment quantifiers implement Q5/Q9. G40-01 is the additional, undisclosed loss of serialization fidelity. |
| Selective-ID handler | The first `Init` fixes the target; later `Init` queries repeat parameters. Pre-init and forbidden-key queries return bottom; permitted keys use fresh coins. The first valid challenge is recorded, all later challenge calls repeat it, and invalid pre-challenge messages are refused. The nine case readers and three handler readers describe the code accurately. |
| Setup order | Before the first `Init` every answer is independent of setup coins, and all lengths depend only on the security parameter. Conditioning on adversary coins and the pre-init history therefore leaves the setup distribution unchanged. Sampling setup early is distributionally valid, including adversaries that never initialize, query before initializing, or initialize repeatedly. |
| Identity/message conventions | Binary identities are injective modulo `p` on the good-order event. The range starting at zero and the weak threshold `2^ℓ≤p` are mathematically valid for this fixed-length embedding. Message validity depends only on the description, not the BB1 random parameters. The off-space `decodeT=1` branch is never used for a fresh accepted challenge. |
| BB1 | Setup, its sample order, `F`, private keys, encryption, decryption, and description mismatch handling agree with the ruled depth-one BB04 construction. Uniform `h,g₂∈G`, including the identity, is faithful to the excerpt. |
| Simulator | Parameters, inverse-difference keys, and `(M_b T,Z,Z^α₁)` match BB04's proof of Theorem 4.1 at depth one. The target is compared as a string before residue arithmetic. For distinct strings with equal residues, the simulator remains a defined, generally incorrect key; T2 charges the bad-order event and T4 must implement that same value. |
| Joux | This is the explicitly ruled abstract single-point variant, not a claim to formalize the paper's alternating Weil pairing on one point. Key indistinguishability under DBDH is correctly identified as a new formalization of the `5 security discussion, not a security theorem stated by Jou00. |

Bottom on `KeyGen` is distinguished by its validity bit. The challenge uses the explicitly
chosen all-zero wire convention, with no separate validity bit; no argument here assumes
that all-zero strings cannot encode honest ciphertexts. Recording the first valid challenge
is what prevents fresh encryption on repeated calls.

The nine declared source deviations and Q1–Q13/location rulings are otherwise respected.
The source excerpts are the fidelity material authorized by Q12; this audit did not independently
obtain or authenticate the original PDFs. Their reported PDF hashes are provenance claims,
whereas the excerpt bytes and repository bindings were independently checked.

## Truth and sufficiency of T1–T4

These are mathematical statement-audit conclusions, not completed Lean proofs of the four
admissions.

**T1 is true with its stated hypotheses.** Parse and re-pair the encoded input, run the BDH
solver, and compare its output with the target encoding. No group operation or decoding is
needed. The nested `pairEncode` format permits polynomial-time projections and reassembly.
On a real tuple acceptance equals solver success; on a random tuple injectivity gives acceptance
at most `1/p`. Thus

$$
\Pr[\operatorname{bdhGame}(A,\kappa)=1]
\le G.dbdhAdv(D,\kappa)+\mathbb E_r[1/p]
\le G.dbdhAdv(D,\kappa)+2^{-\kappa}+\delta(\kappa).
$$

This proves the intended asymptotic implication. The exponential-order hypothesis is sufficient;
it is not claimed to be the weakest possible order condition. `Ops` is unnecessary.

**T2 is true for every adversary, budget, bit, and parameter.** On good generator coins,
distinct identity strings have distinct residues. For each committed target, replacing uniform
`h` by `X^(-ID*)g^α₁` is a bijection in `α₁`. For a permitted key, all exponents below are in
the prime field, and BB04's change of variables gives

$$
\begin{aligned}
F(ID)&=g^{a(ID-ID^*)+\alpha_1},\\
Y^{-1/(ID-ID^*)}g^r&=g^{\,r-b'/(ID-ID^*)},\\
Y^{-\alpha_1/(ID-ID^*)}F(ID)^r
 &=g^{ab'}F(ID)^{\,r-b'/(ID-ID^*)}.
\end{aligned}
$$

The shift of `r` is a bijection separately at each adaptive query. At the challenge,
`F(ID*)=g^α₁` and the real target supplies exactly the BB1 encryption mask. Refusal and
repeat branches agree. Hence the output laws agree conditional on every good description;
the unconditional gap costs only `Pr_r[p<2^ℓ]`, not that probability times the query count.

The cited `ProbComp.expect_simulate_congr` has a **single common state type**. It does not
directly establish the advertised relation between `SidState` and `BB1SimState`.
`simulate_eq_of_abs` supplies structural state abstraction, but not arbitrary distributional
re-randomization. The fill should first reduce to a common augmented state using the existing
abstraction/eager-sampling APIs, or request a shared relational-expectation lemma in `Games`.
A generic relation lemma must not become a private BB1 host or an undisclosed copied induction.
This is proof infrastructure work, not a missing mathematical hypothesis of T2.

**T3 is true, exactly.** Conditional on the history immediately before the first valid
challenge, `T` is still independent and uniform: prior initialization, key answers, and
invalid challenge answers never read it. The adaptively chosen messages are then fixed.
Multiplication by either decoded message permutes the target group, so `M_bT` is uniform
for either bit. The recorded ciphertext and every subsequent answer have the same joint law.
Runs without a valid challenge are already bit-independent. This establishes zero advantage;
an unconditional permutation chosen before seeing the adaptive history is not required.

**T4 is true on the sketched machine route, with the sampling clarification in G40-03.**
`Ops` supplies every needed group operation and membership test, while `ArithmeticFP`
supplies the modular arithmetic. Explicit modular negation/subtraction must be implemented
with the natural-number arithmetic APIs; ordinary truncated subtraction alone is insufficient.
`xgcd` supports the field inverse, including the defined zero case. The reduction need not
decode abstract elements: it operates on their encoded products/powers and validates message
encodings. It does not need `pairStr`, `memG`, target-group inversion, or a lower-order hypothesis.

Use `exists_toCompOn_of_toComp` when adapting the no-extra-input adversary to the handler
theorem's `toCompOn` interface. The resulting distinguishers are `NUPPT`, as the statement
says; uniformity of an arbitrary nonuniform adversary is not promised. Polynomial input,
coin, state, and query bounds are available. Off-distribution inputs can be handled with the
same bounded algorithms. No hypothesis that identities are noncolliding is needed in T4.

**T2–T4 imply exactly the stated headline.** The nine edges of the game's chain have bounds

$$
\delta,\quad \sigma,\quad G.dbdhAdv(D_0,\kappa),\quad
\sigma,\quad 0,\quad \sigma,\quad
G.dbdhAdv(D_1,\kappa),\quad \sigma,\quad \delta.
$$

Their sum is

$$
2\delta(\kappa)+4\sigma(\kappa)
+G.dbdhAdv(D_0,\kappa)+G.dbdhAdv(D_1,\kappa).
$$

The two DBDH advantages are negligible by the assumption; the other terms are negligible by
`hN` and T4. The existing code uses the appropriate symmetric orientations and eight triangle
inequalities, then `linarith`. The four `σ` and two `δ` charges are correct. It uses no T1.
The hypotheses `H,O,hN,h` are explicit, sufficient, and authorized by the rulings; the paper's
efficient-group convention is not being silently added to the Lean theorem.

## Completed proofs, reuse, and policy

| Item | Audit result |
|---|---|
| Group facts | `exists_pow_eq` follows from prime cardinality; symmetry follows by expressing both inputs as powers of the generator. `pair_ne_one` correctly rules out a prime dividing the squared exponent without dividing it. `pow_val_bijective` uses exact prime order, residue injectivity, and equal cardinalities. Exponent reduction modulo the common order is valid in both groups. |
| Joux correctness | `pow_val_mul_mul` correctly reduces products of residues. Bilinearity then gives the common key; commutativity of the exponent product gives agreement of all parties. No nonidentity assumption is needed for this algebraic equality. |
| Joux experiment equality | After both game readers and `jouxKey_eq`, the final `rfl` only needs the local `jouxMsg` body. It is not evidence of reading the foreign `tupleStr` body. |
| Joux security | Advantage equality transfers the DBDH assumption through its published predicate reader. It proves precisely the declared eavesdropper goal. |
| `BB1.decrypt_encrypt` | The proof's three pairing equalities give the common mask and cancellation factor; commutativity and division cancel them. It agrees with BB04's displayed computation. |
| `bb1_correct` | The honest-run reader, scheme field equations, setup/key/encryption readers, and `AllOutputs` binds cover every draw. Message-space membership supplies an actual encoded target-group element; `decodeT_encT` and the algebraic theorem finish. The description-equality branch is the honest branch. |
| Handler case readers | The nine real-game cases, three `oracleImpl` cases, and nine simulator cases match the definitions. The same-file simplifications are legitimate. |
| `bb1_sidSecure` | Correct derivation from the three admitted BB1 steps, with exactly the error sum above. It remains admitted-dependent; it is not an admission-free security proof. |

Every public definition has an equation, predicate, case, or structure-field reader; the
`bb1Scheme` field equations are non-simp. No new `@[simp]` API exception was found.
The small Joux experiment equality and its security corollary do not need a new long proof
sketch; the corollary already explains the reduction in prose. G40-05 concerns the two
substantive BB1 correctness proofs.

The source comparison supports the proposed layering:

- `BilinearGen` is a justified abstract sibling of the concrete modular
  `ExpGroupGen`/`SafePrimeGen` interfaces. The existing DDH substrate has no bilinear
  target group or pairing contract to reuse.
- The new BDH/DBDH experiments have different distributions and inputs from DDH;
  they reuse `Games` advantages rather than duplicating their theory.
- The IBE game needs commitment, extraction, and challenge state absent from the
  public-key game. The common codec, bottom/answer conventions, simulation, and triangle
  inequalities are reused. No duplicate proved public theorem was identified.
- `oracleImpl` is a small adapter tied to this scheme's three named lengths and its
  `sidSpec`. It is not a new generic execution host that must move into `Games` now.
  A future generic finite-family handler constructor should be shared rather than copied.
- `Operations` correctly keeps arithmetic dependencies out of `Group`. Its
  `Candidates.Arithmetic` import is broader than the particular `listToNat` and FP
  declarations used; narrowing it to the defining lower layer is a reasonable cleanup,
  not a correctness or modularity hold.

The three fill units own disjoint target files. T2/T3 use scheme/simulator definitions without
requiring a T4 proof; T4 does not depend on T2/T3. `BonehBoyenSecurity` imports the machine
module for the proved-modulo headline, which is consistent with the split. Helper modules
beside each owner suffice; any newly needed shared generic simulation lemma should be
commissioned into the shared layer rather than changing another unit's file.

Layout, namespaces, precise imports, line widths, and facade/root exports satisfy the location
ruling. All four facades list their children. The largest new module is 553 lines; no changed
line exceeds 100 characters. No bare `import Mathlib` occurs.

## Verification and limits

The independent verifier included with this report reads the pack and Git objects; it does
not execute the pack's scripts or invoke Lean.

| Check | Independently verified result |
|---|---|
| Top-level `SHA256SUMS` | 13/13 matching files |
| `verification.zip` manifest | 98/98 matching members |
| Round-1 manifest | 41/41 matching files |
| Round-2 inner manifest | 411/411 matching files; external and internal manifests identical |
| Source closure | All 86 files match blob identities in the pinned Lean Git tree |
| Bundle | All 18 sections match their pinned Lean/records source bytes |
| PR diff | Exact match to Git objects with `--abbrev=9`; the repository's default abbreviation length otherwise changes only index lines |
| Canonical probe reconstruction | All 12 probe/source/insertion hashes verified; reconstructed sources match the head; three distinct modules |
| Supplied replay evidence | Closure summary: 20/20 successful; root summary: 278/278 successful; four target admissions in the new modules |
| Supplied axiom census | 320 declarations + 52 auxiliary constants; `sorryAx` appears only in T1–T4 and `bb1_sidSecure` |

The pre-pin copies of the plan and EVIDENCE inside `verification.zip` were not mistaken for
the records pin. I read the pinned versions; the differences are the disclosed appended
gate/filing entries. The current handoff's Rule 10 requirements were also checked at the
records pin.

No independent Lean elaboration was performed. Compilation and axiom results above describe
the supplied, hash-bound evidence that was inspected. The mathematical countermodel in G40-01
is not presented as a Lean-checked construction. The missing canonical coverage in G40-02
cannot be replaced by this source review.

To close the gate, resolve G40-01 and supply the missing Rule 10 evidence in G40-02.
The four minor documentation corrections should accompany the repaired statement submission.
The user retains dispatch and merge authority.

## Notation glossary

- `S`: the generic IBE scheme in the countermodel; `*`: the unique value of a singleton type.
- `κ`: security parameter; `ℓ`: identity-length polynomial; `q`: query budget or its polynomial;
  `n`: the explicit sampler block width/trial count in G40-03.
- `G`: the bilinear generator; `p`: the generated group's prime order; `G_T`: its target group.
- `A`: an adversary/BDH solver; `D,D₀,D₁`: the reduction distinguishers.
- `b`: challenge bit; `ID,ID*`: queried and committed identities, read as residues in exponent formulas;
  `m,M`: messages; `c`: a ciphertext in the countermodel.
- `g,X,Y,Z,T`: the public generator and DBDH tuple entries, with
  `X=g^a,Y=g^{b'},Z=g^c` in the BB1 discussion; the exponent `c` there is unrelated to
  the countermodel ciphertext.
- `α₁`: simulator setup exponent; `r`: a key-generation exponent, or generator coins where
  explicitly subscripted in a probability/expectation.
- `δ,σ`: exceptional-order and simulation error functions; `H,O`: the arithmetic and group-operation contracts.
- `pure` / `some`: a deterministic probabilistic return / a successful optional result;
  `advantage`: the absolute difference of the games' probabilities of returning one.
