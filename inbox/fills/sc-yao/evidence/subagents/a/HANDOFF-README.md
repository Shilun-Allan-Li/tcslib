# sc-yao decoder/Alice proof handoff

Immutable source/evidence snapshot from agent `/root/decoder`.

Copy `src/` paths to the lead checkout, and merge `evidence/subagents/a/` into its evidence.
`ORDER.txt` lists the owned module order (CoinRead remains lead-owned and precedes CoinGarbling).
The lead must run all final checks on its merged branch.

The main integration theorem is `AliceProgram.message_poly`; see the full signature in
`AliceProgram.lean` and the report at `evidence/subagents/a/REPORT.md`.

All ten modules have checked whole declarations and no admissions. The decoder and generic
scanner each expose one clean finite machine with correctness/time/head envelope contracts.
No commit or delivery push was made by this sub-agent.
