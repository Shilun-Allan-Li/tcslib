# Gate 03k ([PS10] ch. 2–4, graph isomorphism ZK and encodings): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/k/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the graph isomorphism and non-isomorphism protocols and their proofs (Prots 118.3, 120.6; Props 118.4, 120.7; Thm 122.3, ZK for GI), with their efficiency and soundness repetitions, the simulators, the string encodings of graphs and permutations, the commitment lemmas, and the NP lemmas.
- **This is a "rest" pack.** Its files mostly hold the proofs of headline theorems stated in
  earlier packs, so its trusted surface is their **auxiliary statements**, definitions and
  sketches. A wrong auxiliary statement can make a proof hold for the wrong reason, or hide a
  weaker result behind a headline.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03k-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.5–§4.7 (book pp. 116–127).

## Brief for the auditor

Pack 03a's brief applies (its pack is in the bundle), with this emphasis:
- check each **public definition** and each **public theorem statement** against its docstring;
- check each headline's proof sketch against the source's proof, and say where the formal route
  departs from it;
- flag auxiliary statements that are vacuous (unsatisfiable hypotheses), or stronger or weaker
  than their use in the headline needs.

Attempt at least **two adversarial instantiations**. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/{GraphIsomorphism, GraphIsomorphismZK}.lean`, `ZeroKnowledge/GraphIsomorphism/{Concrete, Efficiency, EfficiencyRep, EfficiencyRepGI, Proofs, Soundness, SoundnessRep, SoundnessRepGI}.lean`, `ZeroKnowledge/GraphIsomorphismZK/{Closeness, Simulator}.lean`, `ZeroKnowledge/{Encoding, EncodingMachines, EncodingPermutations, CommitmentLemmas, NPLemmas}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` |
| Context, not under audit | pack 03e's files (interaction, ZK definitions, commitments, NP) |
| Design record | `briefs/pass-shelat/DESIGN.md` |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Def-117.e, Def-118.a, Claim-118.b, Claim-118.c, Prot-118.3, Lems 119.a–d, Prop-118.4, Prot-120.6, Lems 120.a–d, Prop-120.7, Thm-122.3 (with .hv, .trunc), the GI simulator rows, Inf-4.1, Inf-4.2 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/k/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 358 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 23 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 23 use only the standard axioms, and
   0 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 17 files.

Pack-specific notes (as drafted): elaboration (a fresh replay of the closure); the axiom prints of
the headlines whose proofs live here; admissions (none in these files); lint.

## Specific questions

1. **GI and GNI protocols.** Are completeness and soundness stated with the source's error
   bounds, and the repetitions' error bounds?
2. **ZK for GI (Thm 122.3).** Are the honest-verifier and the truncated forms (D8) stated as
   declared? Is the simulator's success probability per attempt `1/2`, and is the truncation
   error stated?
3. **Encodings.** Are the graph and permutation encodings injective and polynomial-time, as
   their uses need (Inf-4.1, Inf-4.2)?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.
