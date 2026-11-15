# seq-zk-b normalized sequential simulator result

seq-zk-b proved all 10 public declarations in SequentialZK/SimulatorMachine.lean. The module
provides phasePrefix and exact zero/successor/typed-simulator readers; exact i*k message count;
per-message B bound; encoded i*k*(2B+2) bound; the generic polynomial-time phasePrefix_poly;
and the complete exists_phaseSimulator construction.

exists_phaseSimulator returns a uniform SQ with coins CV + Q*S.coins. Its exact S.simulate
reader produces View.encode of x,z,one global verifier tape, and the normalized Q-phase
prefix. The verifier tape is the first CV(|x|) bits; the remaining tape supplies independent
S.coins blocks phase by phase. Each auxiliary input is exactly phaseAux z rV i pre, each raw
phase output is validated/normalized, and the phase's remaining prover slots are empty.
The zero-phase prefix is exactly []; if k(|x|)=0, length_phasePrefix implies prefix=[] for
every phase count. Canonical view metadata and these empty-history outputs remain exact.

Source SHA256: 68e6ac677f383350ebd3c2dab383485c7a7b47ecee9bea47873f8ef14e254e93.
329 lines; maximum width 97; no sorry. simulator-check-03.log: exit 0 with no diagnostics,
2.85 seconds and maximum RSS 2252210176 bytes. The semantic layer check-01 passed; check-02
retains one fixed nested Function.comp application goal. Required error[:(] counts are saved
in simulator-static.json. All 10 public axiom prints are standard only: propext,
Classical.choice and Quot.sound; no sorryAx. Probe source and raw output are retained.
Final style lint across the six local helpers: 0 FAIL / 0 WARN.

The mathematical semantic recursion is public and implemented by instantiating the existing
ColMachines.polyTimeComputable_loopState' host with encoded-prefix state. It is not a new
control host. No machine transition table, private host, or generic loop copy was built.
The raw normalized prefix bound supplies the existing host's polynomial orbit envelope.
All source/proof overlaps and promotion requests are in simulator-overlap.md and the raw
searches log. Stable PhaseView source-copy provenance and its own compile output are retained.
No foreign source was edited; no foreign olean copied.

Every Lean command used seq-zk-b's own olean tree and tag through the default shared slot
wrapper, cap 3 host-wide. A normal wait for a host slot was logged; it was not E-RES.
No Lake command ran, no frozen-file edit/scope request was needed, and no commit was made.
The lead still owns merged checks, stored-constant axiom enumeration and whole-closure seals.
