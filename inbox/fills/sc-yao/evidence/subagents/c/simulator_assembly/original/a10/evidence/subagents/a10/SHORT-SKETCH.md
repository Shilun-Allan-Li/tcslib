**Proof sketch.** Fix the uniform copying simulator for Alice and fake garbler for Bob.
The frozen good-seed statement supplies one negligible bad-event bound before any inputs.
Outside that event, correctness gives both prescribed functionality outputs.
The copying-view coupling simulates Alice; the same event permits Bob's output switch.
The actual two-message view and ideal OT answers identify Bob's selected-key real view.
An exact permutation of the full coin tape identifies this view with stage zero.
The gate hybrid has two stages per gate, replacing rows under an inactive argument key.
Each neighbor reduces to the frozen joint multi-message encryption statement.
Coordinate swapping preserves the seed law, and reconstruction gives the exact challenge.
Finite worst-input and stage advice yields a negligible bound uniform over both inputs.
The last-stage payload is the fixed Bob simulator's canonical prescribed-output view.
Exact endpoint transport and the statistical bound give their negligible sum for both sides.
