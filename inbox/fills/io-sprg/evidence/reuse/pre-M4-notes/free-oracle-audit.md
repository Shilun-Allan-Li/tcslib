# Free-oracle equality audit before M0 freeze

Status: read-only source audit, no Lean. Source binding in source-binding.json.
The two diagnosed false initial-chain equations were repaired by root in
1a941e8ff and renamed hyb_prg_accept_eq_chain_zero and
hyb_uniform_accept_eq_chain_zero. They now assert acceptance equality.

No other false ProbComp equality stub was found. The only remaining SORRIED
syntax-equality claims between ProbComp programs are Hybrids.hyb_real_eq_raw
and hyb_random_eq_raw. Both compare the SAME four sampling queries in the SAME
order: IdDraw, seed Draw, uniform Boolean comparison tail, A.Coins. All maps
and seed projections can be reassociated through the published map/bind laws.
The real game deliberately samples a comparison tail even though it does not
use it, and the hybrid does the same. No unused query is erased.

| Program equality family | Query structure and finding |
|---|---|
| BoolPRG.idSamp_eq/game_eq | Defining readers; unchanged sample tree, no query deletion. |
| SPRG.Raw.idSamp_eq/sdSamp_eq/game_eq | Defining readers; same tree. |
| LPNFamily.Raw.sampleLaw_eq | One draw followed by deterministic core on both sides. |
| Params.idSamp'_eq/sdSampFull_eq/sdSamp'_eq | Owner readers; same draw/core/map tree. |
| Params.jointLaw_eq | Same index+full-seed law on both sides. |
| Params.chainGame_eq/hyb_eq | Owner readers; exact displayed tree. |
| jlsSPRG_raw_idSamp | One identical IdDraw query/core, via raw field/instance readers. |
| jlsSPRG_raw_sdSamp | One identical seed Draw query and core.seed; mapping full output then seed is reassociation, not deletion. Raw Fintype instance equality is an elaboration concern, not a probability-law substitute. |
| hyb_real_eq_raw | Four queries on both sides; actual full-core output is projected through its map. True as syntax equality subject to instance/type transports. |
| hyb_random_eq_raw | Same four queries and identical uniform output; true for the same reason. |
| repaired initial-chain statements | Acceptance equality only; chain's fifth query u may be discarded with expect_const AFTER taking semantics. |

The static inventory lists all theorem headers mentioning the area's concrete
ProbComp-valued functions and an equality. Source inspection also checked all
ProbComp-valued definitions in BoolPRG, Defs, LPN, Samplers, Claim42 and Hybrids.
Scalar probability/expectation equalities and AllOutputs propositions do not
claim program syntax equality. All LPN/PRG hop conclusions use advantage
inequalities, so extra unused draws there are harmless.

Why the old equations were false: OracleComp is an inductive FREE monad
(OracleComp.lean:84), and sample always issues one query
(Probability.lean:85/93), even on a singleton type. Follow the first answer0
at every uniform query and count query nodes. Both old hybrids have count4,
while chainGame at i=0 has count5 because u is sampled but unused. This is a
mathematical distinguishing function on the syntax, so no equality proof can
erase that query. The semantic repairs preserve the security statement.

This audit is not a kernel validation of the remaining two equality proofs.
Root should build them from exact readers/monad laws; if the same draws are
re-enumerated by a genuinely different Fintype value, expectation equality
would be the appropriate alternative. Their current intended sampler readers
identify the actual draw instances, so no such mismatch is apparent here.
