# Semi-adaptive API drafts

Five unelaborated modules, 1,141 source lines in total, 129 source declarations,
four substantive M0 admissions, no tactic blocks. Every module is below 600 lines
and every line below 100 columns. No Lean/lake/build/Git command was run.
The lead must check and promote these drafts. Local static counts/hashes,
source-declaration inventory, admissions and searches are separate files here.

## Dependency order

Data -> Simulator -> Games -> Security -> FromTwoStage.

Data imports only the existing raw FE, BitCodec and the common optional-answer
module. Simulator is the sole new efficiency-definition module importing the
shared CoinSampling.Contract. Games uses the existing exact honest algorithms.
FromTwoStage imports the lead's Simulation.Games and depends on its new
viewWordBits / viewWord_eq_viewWordBits API; that layout is not copied here.

## Actual typed computation and wire representation

- saSpec is literally Games.bitSpec with two oracles. Challenge input width is
  pubLen+privLen; key input width is fnLen. Each output has one validity bit and
  its CT/SK payload. The codec is literally bitCodec at final output width 1.
- saChallengeQuery/SplitChallenge convert between a typed x,y pair and the
  fixed-width word using standard finite-sum operations. Key words are already
  typed function descriptions.
- saCTAnswer/saSKAnswer reuse FixedLengthScheme.decAnswer on typed Option CT/SK
  encodings. There is no copy of the validity-bit encoder.
- saCTPayload/saSKPayload only return fixed-width payload BITS. They never
  recover typed CT/SK objects, invert encodings, or compute a discrete log.
  The generic Raw interface does not supply typed CT/SK decoders.
- SAAdv has coins, budget, next. Its next depends on κ, typed pp/pk, one fixed
  List Bool coin tape, and QueryLog saSpec. It cannot evade its budget: run is
  derived by buildComp, with a proved cost-bound reader.
- budget counts TOTAL oracle calls, including challenge and rejected calls.
  NUPPT.toSAAdv q has budget q. TwoStage.toSA q has budget q+1.
- NUPPT.toSAAdv.next is the standard machine activation on its initial pp/pk
  word plus bitCodec.encodeLog. saReadMove only reads the returned one-bit
  verdict into Bool. The M0 toSAAdv_run theorem states exact equality with
  NUPPT.toCompOn using bitCodec followed by reading bit zero. No machine is built.

The wire-bit specification, with typed optional internal handlers, was explicitly
approved by the lead. It matches design-r3 and the IBE sidGame pattern. A literal
Option-valued oracle range would need an extra adapter and would not be the
required bitCodec interface.

## Simulator interface and rule 15

S.SASimulator.Raw has St κ pp and canonical injective encSt. SetupCore receives
one complete finite draw and returns MPK×St. EncCore receives st,x and one
complete finite draw, returning CT×St. KeyCore receives st,x,f,µ (µ:C.Out at the
drawn class parameter), and one complete finite draw, returning SK×St.
Every draw family depends on ALL its algorithm's nonrandom inputs. The enc
algorithm never receives y. Finite/nonempty draw fields support exact sample;
no UniformSampler or CoinSampler is instantiated.

The efficient S.SASimulator extends Raw with setup_eff/enc_eff/key_eff stated
through the shared SamplesEfficiently contract. Their parameter words include
encoded pp and the algorithm's complete permitted nonrandom input. Scalar µ
uses C.encValue, preserving the scalar rather than replacing it by GT data.
Each field chooses one uniform sampler/core before κ/all public parameters.
The code creates no VALUE of this efficient interface outside future assembly.

No abstract efficient SASimulator.toSim is claimed: the shared contract lacks a
generic parameter-word preprocessing closure sufficient to infer it here.
Concrete Wee20 SimTargets must state BOTH efficient raw simulation variants.
The defined conversion SASimulator.Raw.toSim is purely RAW, reusing the same
draws and cores with omega.publicInput and indexed function/scalar projections.
Its exact-law readers use the published raw algorithm equations, not foreign
unfolding. It constructs no sampler and no efficient Simulator value.

## Actual handlers and experiment

Real state is an optional SAChallenge(x,y). Ideal state is private Sim.St paired
with that optional challenger commitment; hidden y is not in the simulator state
and is never supplied to simulator encryption. The typed real/ideal challenge
handlers accept the first challenge, reject duplicates, and record x,y only in
challenger state. The typed key handlers reject before challenge. Later real
keys use honest KeyGen; ideal keys get exactly C.eval f x y, threading Sim.St.
saImpl converts these typed Option answers through the shared encoder.

saGame draws pp, real or ideal setup, and one independent full adversary tape;
then it uses Games.simulate on the actual bounded adversary computation and the
appropriate stateful handler. True means real, matching the root simGame flag.
saSimAdv is the common two-experiment advantage, not a guessing formulation.

## Two-stage embedding and exact game identity

TwoStage.firstCoins and secondCoins deterministically read disjoint blocks of
the input tape. They are tape layouts inside an adversary, not samplers or
assumption-reduction coin decoders. The first stage runs with [] as its
argument and does not see pp/pk. Commitment.decode is reused verbatim.
The next move asks the committed challenge, then q committed functions in
order. It collects only CT/SK payload bits and calls the second machine's
original distinguisherL on S.viewWordBits, with its disjoint second-stage tape.
List history/filterMap and buildComp are reused; no private recursion host is
introduced. Failure branches are total on arbitrary artificial histories;
actual game histories have all the expected successful answers.

The law identity is expect_simGame_eq_saGame for EVERY Bool->Real test. It is
not an equality of OracleComp syntax trees: independent sampling occurs in
different syntactic orders. The proof plan commutes independent first-stage
coins and reindexes the full tape, then unrolls the same challenge/key law.
The resulting simAdv_eq_saSimAdv is exact, with zero loss. There is deliberately
no abstract theorem SASimSecure -> SimSecure: realising the composed adversary
as one oracle machine is Phase B, as the dispatch requires.

## Security and the vacuity rule

SASimSecureWith names a raw simulator and quantifies only over NUPPT machines
A and polynomial TOTAL budgets q, using A.toSAAdv q. SASimSecure existentially
quantifies an EFFICIENT simulator before those machines/budgets. Subexp variants
use one positive common exponent, matching the parent's committed predicates.
They do not quantify realisability over arbitrary Lean next-move functions.
Raw core inequalities can still quantify over all typed SAAdv values separately.

## Four intended M0 proof obligations

1. NUPPT.toSAAdv_run: bitCodec/toCompOn run equality.
2. SubexpSASimSecureWith.saSimSecureWith: shared asymptotic implication.
3. expect_simGame_eq_saGame: exact law identity with the explicit raw conversion.
4. simAdv_eq_saSimAdv: exact advantage identity derived from equal laws.

Readers, raw conversion, algorithms, uniform field definitions and all handlers
have complete term bodies. This is still an unelaborated draft; a complete term
body is not being reported as a successful Lean check.

## Overlap and reuse

searches.log records the local searches. Existing Games.buildComp, bitCodec,
MachineCodec.encodeLog, NUPPT.toCompOn, runAt/runAtL/distinguisherL and their
readers are central and reused. No generic map-on-final-output buildComp API was
found, so the source-specific one-bit reading connection is the new run theorem.
FixedLengthScheme.decAnswer and its readers are reused, while decOpen is an
unrelated CPA/CCA phase predicate. List.filterMap supplies collection; simulation
and list traversal are not reimplemented. The nearest related source shapes
are IBE.sidImpl/sidGame and the parent's committed raw simulator/game APIs.
The separately drafted LinearSecurity.saGame handles group-matrix function
keys and has its own internal bundle, so it cannot replace generic FE games.

The probability proof route must reuse expect_sample_equiv,
expect_sample_comm/expect_expect_sample and simulate/buildComp case readers.
No probability lemma, Subexp API lemma, sampler contract or realisation
predicate is defined again. exact?/apply? and all elaboration remain for the lead.

## Source verification

The supplied five hashes were previously verified before reading. For this
subtask, complete Wee20 PDF/printed page 5 (§2.2) and GJLS21 PDF pages 23–24
(printed 19–20, Def4.3/Remarks4.3–4.6) were read and visually inspected after
rendering in place. AGW20 pp.11–12 had already been inspected in the PG review.
Scratch page PNGs/text are reading intermediates and should not be shipped as
payload by default. No PDF was copied. Scalar leakage is the ruled reading
already disclosed by the parent, and no weaker simulation notion is substituted.
