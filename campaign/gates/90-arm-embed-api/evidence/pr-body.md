Additive API for abstract register machines (`SpaceComplexity/Machines`), needed by the general Savitch theorem's deepening machine. That machine runs the proved Savitch search as a block, twice, without restating any of its lemmas.

**What it adds** (no existing statement changes; nothing is removed):

- `Machines/ARM`: `arun_zero`, and the value semantics of each instruction as an equation, `astep_inc` … `astep_jeqSnd` (14). A machine defined outside this file can then be reasoned about step by step without unfolding `astep`.
- `Machines/Program`: `callSegs_congr`, which says two calls with the same mode and the same argument words have the same virtual input.
- `Machines/ARMProof`, embedding a machine as a block of a larger one:
  - `Ins.embed` relabels registers, deciders and labels, and turns an answer into a jump to an exit.
  - `RegExt` relates the block's registers to the larger machine's.
  - `preS_of_ins` and `preS_embed` give the syntactic preconditions.
  - `astep_embed` is one step of the embedded block.
  - `AHalt.embed`: a halting run of the block is a run of the larger machine to the exit.
- `Machines/ARMLoops`: `AHalt.embed_guardLe`, the same under the bounded-run guard `GuardLe`.
- `SavitchARM/Machine`: `A_noVal`, which says the Savitch machine has no input-format check, so it halts only by answering.

**Checks:**
- Each new proof reads other files' definitions only through stated lemmas. Sealed copies elaborate with every such definition made irreducible: 4 copies; 16 controls, which pass unsealed except two recursive delta goals and all fail sealed.
- All new declarations are on the standard axioms or fewer.
- The style lint is unchanged (0 FAIL); the policy linter reports 0 findings on the five files.
- The copy-text screen over a 13-file population finds no new pair.
- A sealed consumer probe transports `SavitchARM.outerU_run` into a host machine, with decider `2` rerouted, using only these lemmas.
- One name is shared: `BoolCircuit.AdjScan.astep_jeqFst` (`CircuitComplexity/LogspaceUniformScan`), a step lemma of one particular machine. That file opens `Complexity.LogProg`, and it still elaborates; the overload is resolved by argument type.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
