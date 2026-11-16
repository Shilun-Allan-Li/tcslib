# Shortened complete simulator assembly skeleton

Evidence only. This retains exactly the original one local `hBob` admission and must not
be presented as the finished simulator theorem. The entire target signature, including
G1/G2, hGE, hE, hG and the placement of SA/SB before D, is unchanged byte for byte.
The hBob comment/statement/proof block is also unchanged byte for byte.

The canonical source is `probes/FullSimulators.lean`; normal03 passes with zero errors
and exactly the expected one sorry warning. The body is 100 lines including `:= by`,
down from a10's 117. The full source is 137 lines and max width is 93. The principal
change replaces the actual-Bob-bad-probability calculation and output switch with the
checked generic `BobStatistical.statClose_real_output_switch`, using the existing coin
equality, WHP bound, and correctness. Other changes remove redundant local aliases and
combine two short tactic sequences. No frozen or library source was edited.

`probes/AssemblyTrace.lean` walks the actual stored transitive dependency closure and
asserts the exact admission list. Its successful02 run finds 17662 dependencies, the
frozen `yaoSeed_good_whp` admission and this skeleton's one hBob admission, and no use
of the old `yaoHybrid_simulators` theorem. Failed audit01 used List.qsort on an Array
conversion; its source/raw two-error log are preserved. Both diagnostic error forms
are counted in SUMMARY.json. No new whole-file seals were requested for this admitted
scratch; final whole-Yao audits remain the lead's responsibility.

The original a10 v10 artifact and all16 checksummed files are preserved under original.
All own actual source versions, normal logs, trace logs, check runner and metrics are
preserved. Every check used the host slot wrapper/tag sc-yao-c and the c olean tree.
The immutable handoff includes the final completed source-matching probe oleans.
