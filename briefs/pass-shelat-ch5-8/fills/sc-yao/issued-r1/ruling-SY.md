# sc-yao · rulings SY-1 to SY-6 (Seyoon, 2026-11-15)

Seyoon made these rulings before dispatch. They are part of the issued package and take precedence over [the brief](brief.md)
wherever the two differ. The brief was written for the recommended options. Two rulings differ from those options:
**SY-2**, which waives the line cap, and **SY-6**, which makes the worker multi-agent.

## SY-1 · One hub import line in `Yao.lean`: approved
Exactly one line is pre-approved: `import TCSlib.Cryptography.SecureComputation.Yao.<Hub>`, placed after the
existing imports (after line 9 at the base). You choose `<Hub>`; report the name.
- All helpers live under `SecureComputation/Yao/<Hub>/`, with `Yao/<Hub>.lean` as their facade. With this layout the
  style lint treats `Yao.lean` as a facade that only needs to import the hub.
- **State the helpers generically.** They cannot see `Yao.lean`'s definitions (`YaoCircuit`, `yaoSeed`,
  `yaoHybrid`, and the rest). Pass Yao's specifics in as hypotheses. The two target bodies in `Yao.lean` then
  instantiate the helpers through `Yao.lean`'s own readers or `rfl`.
- No other import line changes in `Yao.lean`.

## SY-2 · Line budget: the cap is waived up to 1,200 lines
`Yao.lean` may grow to **at most 1,200 lines**, measured on the file as it stands after sc-garble lands. sc-garble's
landing has 970 lines, so sc-yao has up to +230 net. The maintainer records this as a size exception under the
standing size rule.
- Every other file stays under 1,000 lines.
- Keep growth in `Yao.lean` to the two bodies, their sketches, the `## Main results` bullet and the hub import;
  everything else goes in helpers.
- The two sketches must describe the delivered proof. Drop the obsolete sentence saying the joint lemma is "not yet
  stated in the library", which has been false since #311.

## SY-3 · Frozen-file readers: all the listed readers are pre-approved
- `DAGCircuit.isFaninTwo_iff`, **byte-identical** to sc-garble's (its delivery, lines 510–518), so that the two
  copies coincide when sc-garble lands. Put it in `Complexity/CircuitComplexity/DAGCircuit.lean` directly after
  `def IsFaninTwo`, exactly as the brief's *Frozen-file readers* block shows.
- `rfl` readers in `Uniform.lean`, each with a formula docstring and no attribute, placed beside its definition:
  `encodeList` (the nil and cons cases), `GateKind.encode` (one reader per constructor, three in all),
  `DAGGate.encode` and `DAGCircuit.encode`.
- Include the seal probe showing that each reader is needed: its `rfl` form fails under the seal and the reader
  passes.
- Any other frozen-file change still needs a scope request.

## SY-4 · Hosts: public generic contracts in helpers
Build the **poly-time circuit-description decoder** and the **poly-time garbled-evaluation (`runWith`) machine** as
public, generic contracts, each one machine with its time envelope, in sc-yao helper modules. Prove them under the
hosts-first rule. In the report, request their promotion, and give a draft host-registry row for each in the
format of `machine-library-design.md` §14. They are gated with the unit.

## SY-5 · Overlap with unmerged deliveries: disclosed general copies allowed
You may re-derive lemmas that exist only in the unmerged deliveries sc-garble (its helpers), #318 (`ObliviousTransfer/*`)
and sc-compose (`ComposeSecurity/*`). Each re-derivation must be stated generally and disclosed in `REPORT.md`
§ *Overlap and reuse*, with the unmerged relative's path and name. After both sides land, the maintainer re-points
them, proof only, and puts any that remain on the ledger. Copying a merged public lemma is still a finding.

## SY-6 · Worker: Codex on Seyoon's Mac, multi-agent
The worker is Codex on Seyoon's Mac: a lead with **up to 3 sub-agents**. The host addendum applies in full,
**including §4** (the sub-agent rules):
- every sub-agent has its own worktree and its own olean tree, with `.lake/packages` linked to the lead's;
- every Lean, Lake and `lean_check_tree.sh` command goes through the shared 3-slot cap;
- work is split by helper module, so that no two agents edit the same file;
- **only the lead edits `Yao.lean`, `Uniform.lean` and `DAGCircuit` files**, commits on `fill/sc-yao`, runs the
  final sweep and checks, and delivers;
- sub-agent logs go under `evidence/subagents/<name>/`, and `REPORT.md` records who proved what.
