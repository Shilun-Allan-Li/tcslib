# Gate 03g ([PS10] ch. 2–4, 3-colouring zero knowledge): external statement audit pack

**Status: draft.** The pinned head, the attestations and the bundle are filled in once the dedup
PR has landed (`PLAN.md`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`<HEAD, 40 hex, from git rev-parse>`. This pack covers the graph 3-colouring language and its encodings, the commitment-based protocol of §4.7 and its parties, the soundness and efficiency of the repeated protocol, the simulator and its analysis, and the headline zero-knowledge theorem for 3COL behind Thm 124.1.
- **This pack gates fills.** Its files hold **3 `sorry`s**, to be filled after this pack
  closes (user's ruling of 2026-11-05). A statement that cannot be proved as stated, or that is
  weaker than the source, must be found **now**.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03g-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.7 (book pp. 124–129).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also, for **every sorried
declaration**, say whether it is (a) true as stated and provable from the hypotheses it carries,
(b) true but weaker than the source, or (c) false or unprovable as stated. For (c), give a
counterexample or the missing hypothesis. Attempt at least **three adversarial instantiations**,
for example:
- a malicious verifier that asks an edge outside the graph;
- a graph encoding with no edges, or an ill-formed instance;
- a simulator that is efficient only because the number of repetitions is bounded by the advice.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/{Language, Machines, Parties, Protocol, ProtocolProofs, Simulator, SimulatorLemmas, SimulatorMachine, SimulatorNumeric}.lean` and the facade `ZeroKnowledge/ThreeColoring.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | pack 03e's files (interaction, ZK definitions, commitments, NP); `ZeroKnowledge/NP.lean` |
| Design record | `briefs/pass-shelat/DESIGN.md` (§2.15 the frozen ch. 4 signatures, with D8; §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Thm-124.1, Def-124.a, Claim-124.b–e, Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; graph isomorphism (pack 03k) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

To be filled at the pinned head:
- elaboration (a fresh replay of the closure);
- the axiom prints of this pack's headlines (`audits/pass-shelat/Checks.lean`);
- admissions: the 3 `sorry`s, listed by declaration;
- lint.

## Specific questions

1. **The language and relation** (`R3COL_witnessRelation`, sorried). Is the relation the
   source's: valid encodings, a proper colouring, a polynomially bounded witness? Is its
   polynomial-time verifier claim true?
2. **The protocol (Prot 127.5) and its repetition** (`colRep_efficientProverProof`, sorried).
   - Is the soundness error `(1 − 1/|E|)^{n|E|} ≤ e^{−n}` stated at the right number of
     repetitions?
   - Is the prover's efficiency stated given the witness?
3. **The simulator (Alg 128.7) and `col_zk`** (sorried).
   - Is ZK stated against every n.u.p.p.t. verifier with auxiliary input?
   - Is the truncation (D8's strict simulators) declared?
   - Does the error bound `|x| ε_B(√|x|) + e^{−n}` reduce to the commitment's hiding as the
     sketch claims?
4. **Run-3a's blocker P11-1** (3COL) was repaired. Check the repair.
5. **Thm 124.1** (form (A): ZK for every `(L, R_L)` with an explicit Levin reduction to 3COL).
   Is the headline's dependence on these three `sorry`s, and on the hypotheses of form (A),
   correctly declared?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. Add the column **Sorry verdict** (a / b / c, see the
brief) for sorried declarations. The pack closes at **0 blockers and 0 majors**.
