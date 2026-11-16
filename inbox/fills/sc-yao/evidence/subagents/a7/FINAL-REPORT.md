# a7 fixed simulator factory and concrete specialization

`FakeSimulatorFactory.exists_simulator` returns one fixed uniform SB, its prescribed
coin polynomial, and exact runAtL/idealB words on the supplied circuit and seed families.
It constructs the previously audited Data once in a generic context and consumes the
published constructor word equations. No semantic definitions, hosts, or probability
arguments are duplicated; Data and all prior helper sources remain unchanged.

ConcreteFactory specializes it to YaoCircuit.uniform, Y.circ, Y.outs, yaoSeed,
Y.inA/inB/outLen/sizeBound, yaoCoins, and the published raw tape readers. Its 51-line
proof chooses the machine before n, inputs or distinguisher. A length-preserving coin
bijection supplies the original numeric tape and the actual idealB equation.

## Verification

Factory normal02 and concrete factory-normal01 pass. Factory passes A/B strict/coe
whole-file seals. Concrete canonical A strict/coe both pass. Diagnostic B strict/coe
fail at (.add inA inB).eval versus inA.eval+inB.eval after PolyExpr.eval is sealed,
followed by three nonce/permutation simp cascades under the ill-typed circuit argument.
These are attributable to the explicitly exempt polynomial notation; canonical A has
zero errors. Full imported TCSlib definitions are sealed, generated abbrevs excluded,
-DmaxErrors=0 is used, and both error: and error(...) are counted. Original failed
constructor-specialization sources, every repair attempt, and every raw log are retained.
The full 17-owned-helper plus concrete stored trace checks 301 constants: all sorry
closures empty; axioms only propext, Classical.choice, Quot.sound. Style lint reports
0 findings for the 221-line new helper; every line is under 100 characters.

## Reuse and scope

Search in the existing HybridProof tree and pinned Mathlib for exists_data,
exists_simulator and existential NUPPT constructors found no matching actual-family
factory. Nearest relatives are FakeSimulator.Data.make, its two word equations,
simulator_uniform/coins/runAtL/idealB_eq and BobSimulator. They are consumed unchanged.
No new import outside the approved scope; the helper imports only FakeSimulator.
ConcreteFactory is evidence only and imports Yao; no helper can see Yao.

No commits, pushes, frozen source edits or delivery actions were made by this child.
No own process remains live after the completed factory-audit01 batch.
