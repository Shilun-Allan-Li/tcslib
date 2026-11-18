# SemiAdaptive.toSAAdv_run proof candidate

The frozen existing theorem header and entire docstring are preserved byte-for-byte.
The candidate contains one tactic block, no admissions and no new declaration.
No Lean, lake, Git, live edit or proof checker was run. Native validation remains
pending. All dependencies used here are existing public APIs, rather than the
pending layered-garbling proof chain.

## Execution argument

SAAdv.run_eq and toSAAdv_budget expose the typed bounded run with exactly q.eval
kappa calls, and NUPPT.toCompOn_eq exposes the machine computation at the same
budget. saCodec_eq identifies the stated bitCodec with the typed codec. The two
local let names only abbreviate these already exposed next functions. Their
expansion in change reduces local abbreviations and lambda applications, and
does not unfold any TCSlib definition.

The proof generalizes the remaining budget and shared initial history, then uses
the four published buildComp case readers. At every history, toSAAdv_next,
saReadMove_eq and NUPPT.runAt_eq show that both runs decode the same activation
with the same List.ofFn coins and same encoded history. Return moves differ only
by evaluation of the one-bit word at zero; query moves are identical. At zero
budget a query times out, and saCodec_eq, bitCodec_timeout and zeroBits_apply
identify the word timeout's bit with false. A positive-budget query appends the
same dependent log entry, so the induction hypothesis identifies continuations.

OracleComp.map_eq_bind, pure_bind and query_bind are the existing free-monad
homomorphism equations. The proof does not unfold bind/map/buildComp or rederive
these laws. It neither decodes a typed group element nor changes malformed-output
behavior; malformed words already have the same bitCodec.decodeMove result on
both sides. No extra call, coin-length condition or challenge/key-order hypothesis
is introduced.

## Reuse and potential validation points

No existing generic buildComp result-map theorem was found in the focused Games
search. Games/Bridges/Machines.buildComp_singleCodec is a close induction pattern,
but translates a one-oracle query-tree representation; it cannot instantiate to
this Fin 2 specification and final-output map. Games/Simulate.simulate_bind and
simulate_comp concern handler simulation; they do not compare the two bounded
next-move builders. Consequently the direct induction belongs in this already
existing source theorem. No new helper statement/proof or probe is proposed.

Root should check tactic inference for backward rewriting of NUPPT.runAt_eq in
hread and for the two generalized shared histories. The explicit next arguments
on buildComp case readers avoid higher-order inference ambiguity. There is no
known mathematical obstruction; all query, return and timeout branches are
present and the frozen statement appears sound.

Garbling status update received from root: backward_action and translation now
native PASS. Privacy remains pending root's next native check. These statuses
are unrelated to this execution bridge, which has no layered-garbling dependency.
