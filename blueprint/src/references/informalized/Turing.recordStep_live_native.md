<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_live_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Live Native-Step Simulation

**Claim.** Under the stated seek-machine bound, live-state, width, and blank-tape hypotheses, the record-step machine simulates the native transition within the stated time and head-displacement bounds, avoids both verdict states before finishing, and ends with the prescribed updated snapshot and buffers.

**Proof.** Let $W=\mathrm{width}(|x|)$ and let $w$ be the fixed-width binary word for the input-head position of $c$. Its length is $W$. Split into the empty-input and nonempty-input cases.

1. If $|x|=0$, the width characterization `recordStep_width_one` makes the stored width flag true. The input head can only occupy the two boundary positions, so the blank-position characterization `recordStep_input_blank` gives $c$'s read symbol as absent. The empty-input simulation lemma `recordStep_empty_run` supplies the required run, with verdict avoidance and head bounds at radius $|w|+1$. The inequality $W+1\le (C+1)(W+1)$ permits enlarging this radius via `recordRun_mono`; its time bound $2W+3$ is below the claimed bound.

2. If $|x|>0$, `recordStep_width_one` makes the width flag false. The position-capacity bound `record_pos_lt` ensures the fixed-width representation has room for every input-head position. The preparation lemma `recordStep_prepare_native` determines whether the head is at the right boundary, records the native-right flag, and gives the corresponding position $q$ and a bounded preparation run. The digit evaluation theorem `record_digits_value` confirms that $w$ encodes $c$'s actual input-head position.

   Next, `recordStep_seek_read` uses the assumed seek-machine specification to reach and read the native input position, while preserving the required work-tape data. The restoration lemma `recordStep_restore_native` returns the simulated input head and restores the position data, with its own time and displacement bounds. Enlarge the preparation and read radii to $(C+1)(W+1)$ using `recordRun_mono`, then concatenate the three runs with `recordRun_trans`. Adding their time estimates and using $|w|=W$ yields the claimed global time bound. The resulting endpoint is the snapshot with the native input symbol and chosen boundary flag, the position buffer retained, and the second buffer empty.

**Key facts.** `Turing.recordStep_width_one`, `Turing.recordStep_input_blank`, `Turing.recordStep_empty_run`, `Turing.recordRun_mono`, `Turing.record_pos_lt`, `Turing.recordStep_prepare_native`, `Turing.record_digits_value`, `Turing.recordStep_seek_read`, `Turing.recordStep_restore_native`, `Turing.recordRun_trans`.
