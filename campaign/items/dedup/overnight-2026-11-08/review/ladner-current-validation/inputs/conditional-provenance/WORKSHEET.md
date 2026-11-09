# Ladner readiness revision: proved owner readers, six mathematical placeholders

This is a private compiling proposal and internal readiness worksheet, not a source landing, fill, dispatch or completed gate. The prior `/private/tmp/ab34-overnight-backlog` packet remains immutable. The revised prototype changes only the three expressly approved routine reader bodies, authoring text, and the cap reader's sketch. All 17 declaration headers and the four TCSlib imports plus Mathlib.Data.Nat.Log are exactly unchanged. No substantive mathematical target was filled.

## Authorization correction

PLAN(f)/HANDOFF§3 already authorize LD1–7, the planned `TCSlib/Complexity/Diagonalization/Ladner.lean` home, namespace Complexity, and the mandatory own-definition readings. The earlier worksheet's suggestion of a separate LD10 permission for that already planned layout/readers was too broad and is withdrawn. The necessary ladnerMachine_eq and SAT_H_eq readings do not create a new design gate by themselves. This revision follows the parent's explicit reassessment; it adds no new public host, theorem header, route or imported-module decision.

LD6 still has the accepted NPHard premise. NPHard is a weaker premise than NPComplete; using it gives a stronger theorem. The header is preserved. Copyright is TCSlib contributors, Authors: Codex; AB is the mathematical source, and Seyoon is not named as author of this prototype.

LD8 remains root-owned. Root has retrieved the official author index and Duke book mirror and is checking primary chapter text. This packet does not claim to finish that check or select exercise part letters. Its current approved fallback citations are [AB09, Theorem 3.3 and its proof].

## Exact source and environment

The source basis is the actual #233 merge 9b5dcf46408db681bcbc721930ef2203fa6bc47d. git rev-parse resolves it as a commit; all1003 tracked Lean paths/blobs match both the root-adopted map and the records worktree bytes at the recorded check. Whole MAC8's actual895 olean hashes independently match the complete root-adoption map, with no extra/missing/changed objects. This is a whole snapshot; no object splicing or compiled output was performed here. The checks are timestamped; these are not claims that other agents' branch refs stayed unchanged.

Every command sourced the campaign env. Every elaboration used the shared leanelab wrapper, one file at a time, local3/machine5, j4/nice10, no olean output. Shared lock access was approved; no alternate lock namespace was used. Full request/input/raw-output/exit receipts are in attempts. The wrapper and cited control/source files are copied in full under inputs; their hashes and relevant source-commit blobs are in bindings. Documentation may contain later root updates; the bindings distinguish current control bytes from the source-base blob. The Lean toolchain file is leanprover/lean4:v4.25.0.

## Proved routine readings

* padSAT_congr: a padding witness's prefix is strictly shorter than the entire word because of the false separator. Substitute the agreed exponent value at that prefix length. The separate first check passes with eight remaining warnings.
* ladnerH_eq: read the strong-recursion equation using public WellFounded.fix_eq; compare the local and global padding predicates below each queried length using padSAT_congr and Nat.log_lt_self. A candidate index implies n is nonzero, so logarithmic decrease is used only in that case. Nat.find_congr' transports the least index. The separate completed check passes with seven remaining warnings.
* ladnerH_le: use the equation; Nat.find_spec supplies the strict bound in the selected-index case, and the fallback is the cap itself. Its separate completed check passes with exactly six warnings and no errors.

Final main prototype SHA256: 56c999de7f9a86a9d67cf4de3e567381fc448d2f798435602a99d79783bb3a6a.

The only six sorried declarations are ladnerH_polyTime, SAT_H_mem_NP, ladnerH_bounded_of_mem_P, ladnerH_unbounded_of_not_mem_P, SAT_mem_P_of_padSAT_NPHard, and SAT_H_intermediate. The existential ladner merely packages SAT_H_intermediate and therefore also depends on sorryAx. It is not an independently proved Ladner theorem. Three earlier unsuccessful equation-reader attempts are retained with actual failing receipts rather than erased.

The actual selected axiom census covers all17 proposed declarations. The three newly proved readers have only subsets of the standard propext/Classical.choice/Quot.sound axioms; no sorryAx. Exactly the six mathematical targets plus their dependent ladner packaging have sorryAx. This is a selected proposal census, not a global library census or a truth claim for sorried statements.

A bounded native opacity probe passes after making SAT, expCode, FinTM.ComputesInTime and CodeTM.toFinTM locally irreducible and disabling the existing CodeTM.toFinTM_k simp row. All eight paired direct delta/equation controls pass unsealed and fail sealed, with eight actual errors at the intended sites. This proves the recorded four-head boundary is effective for this proposal; it is not a full future gate, an exhaustive import-simp census, or a projection-guard claim. Static inspection of the three reader proofs finds no explicit imported TCSlib definition or Core/Mathlib definition supplied to simp/rw/unfold; own ladnerH is unfolded, and foreign data/computation predicates are carried opaquely.

## LD9: concrete compiling conditional routes

The exact current-import main closure is115 TCSlib modules. These first two consumer probes use those same imports and pass with zero errors and zero sorries. They introduce examples in private scratch, not public library declarations.

1. Conditional-bounded-simulator.lean.txt composes UniformMachineCode.simulator_accepts/rejects with FinTM.exists_comp_on_image and the public computesFunInTime_iff reader. Given a preparation machine producing `pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z)`, its polynomial setup clock, an explicit polynomial bound on `d*(|code z|+|input z|+deadline z+1)^d`, and an explicit final polynomial envelope, it returns a machine computing the singleton bounded-acceptance Boolean in that final polynomial clock. It does not supply the preparation function/machine or those numerical inequalities for Ladner.

For the accepted Ladner queries the missing quantitative leaf has the exact form, for fixed simulator degree d:

    ∃ A e, ∀ n i (x : List Bool),
      i < Nat.log 2 (Nat.log 2 n) → x.length ≤ Nat.log 2 n →
      d * ((Nat.bits i).length + x.length + i * x.length ^ i + 1) ^ d
        ≤ A * (n + 1) ^ e

The public simulator is polynomial in the numeric deadline, not in its bit length. Replacing this leaf with a claim that binary clocks automatically make it FP would be wrong. The worksheet leaves this arithmetic and the query construction as fill obligations.

2. Conditional-linear-SAT-search.lean.txt uses mem_P_iff and exists_proj_decider 1 1. Given a P language V and the exact certificate equivalence

    ∀ x, x ∈ SAT ↔ ∃ u, u.length = x.length + 1 ∧ x ++ u ∈ V,

it returns a SAT decider with clock

    b * 2^(n+1) * (a * (n+(n+1)+1)^d + (n+(n+1)+1)^2).

This is an actual compiling single-exponential search host, not a guessed name or a new private machine. On short inputs, Nat.pow_log_le_add_one supplies the relevant existing all-n bound `2^(Nat.log 2 n) ≤ n+1`; composing the displayed search clock with short queries still needs the explicit budget and query preparation proof. No such Ladner-specific proof is claimed here.

The precise unresolved SAT premise is visible in current source. SAT.lean:201–209 proves the n+1 certificate equivalence privately as sat_verifier_equiv; SAT.lean:954–957 constructs SAT_mem_NP using C=c=1 and private satVerifier false. The public theorem statement is only SAT∈NP. Its existential certificate parameters cannot be recovered as exactly1,1 by using the theorem opaquely. A generic NP⊆EXP result allows c>1; `2^(C*(log n+1)^c)` would then not furnish the needed polynomial-in-n bound. The bounded literal-clock/public-header searches are preserved; they are not a global semantic absence proof.

A concrete owner-API option requiring a genuine new public statement/name ruling is to expose, in ClassNP/SAT.lean beside its existing verifier proof, this exact existential contract:

    ∃ V : Language Bool, V ∈ P ∧
      ∀ x : List Bool, x ∈ SAT ↔
        ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V

The already existing owner witness is satVerifier false, with existing satVerifier_of_poly false satVerdict_false_poly and sat_verifier_equiv. No theorem name, source change or new host was selected or implemented. Another route would have to provide an exact local checker and its quantitative proof inside the authorized Ladner module; merely renaming a generic host would not discharge it. This packet makes no claim that such a local route has been completed.

3. Conditional-memo-driver.lean.txt makes the permitted quantified-helper decomposition concrete. Given existing-FP step/init/out functions, constants a,k,B,b, a bound

    ∀ z i, i ≤ a*(z.length+1)^k →
      (step^[i] (init z)).length ≤ B*(z.length+1)^b,

and exact final readout equality to Nat.bits(ladnerH z.length), the existing BinArith.polyTimeComputable_iterate followed by the public composition API gives the target FP statement. This separate probe passes with the same six main-placeholder warnings and no new ones. It imports only the additional existing BinaryArith.Iterate module: total closure116, exactly one module beyond the main115. That import is not applied to the main proposal.

No concrete memo serialization, step, iteration count, output function, orbit invariant, or state-size bound was supplied. They can be named local fill obligations inside ladnerH_polyTime in the approved module, without designing a new generic machine host. The accepted H cap can inform their eventual bounds, but this record does not count a proposed table encoding or an unproved size estimate as a delivered route.

A further Rule10 interface review is needed if the eventual route must introduce/eliminate PolyTimeComputable by its machine witness, or read deterministic DecidesInTime pointwise. The bounded name searches did not identify general public readers for those two definitions. The successful probes avoid unfolding them: simulator output remains an explicit machine witness, search output remains DecidesInTime, and the memo transfer uses the public FP iterator/composition. An unrelated FormulaKit fragment/serialize iff search hit is specialized and admitted; it is not used. This is a precise interface issue to review, not evidence that a new universal machine is required.

## Remaining readiness limits

The three skeleton-time readers are resolved. LD9 remains open at the concrete preparation/numeric-budget, sharp public SAT certificate contract, and memo-state correctness/size premises above. LD8 primary-source fidelity, complete future pre-ship sanity/semantic review, exact final imported-definition boundary, facade/gate/replay work, and the six mathematical fills remain root-owned future work. No source PR, skeleton commit, external audit dispatch, new public API/import/home/route decision, canonical record mutation or snapshot mutation was performed by this agent.

Do not infer readiness from six sorry warnings alone. Carry forward n=0/1, caps around4/16, i=0 and empty inputs, exponent0 and0^0, malformed SAT words, the final-false split, least-index selection, and divergence versus ordinary unboundedness. These planned mathematical sanity checks were not silently filled tonight. Prior T31/F6/deepening work remains already landed and is not repeated here.
