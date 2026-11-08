<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.bad_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded rejection of malformed encodings

**Claim.** For either exactness flag, if the input has the form $z=\mathrm{dbl}(w)\mathbin{++}t$ and the tail is empty, a single bit, or begins with $10$, the machine reaches a halted configuration outputting $0$ within $2|w|+2$ steps.

**Proof.** First, $2|w|\le |z|$, so the machine can scan the $2|w|$ bits of the doubled word. The setup scan result says that after those steps it is in the scanning configuration for the phase and counter obtained by folding the scan update over $w$ (`setup_scan`). The initial configuration is exactly the required starting scan configuration (`init_eq`). Let $\phi$ and $r$ denote that resulting phase and counter.

Now split according to the tail. If it is empty, the next input symbol is blank, so the machine in state $\mathrm{rd1}(\phi)$ rejects in one step. The rejection transition halts and appends the output bit $0$ (`step_rej`); this takes $2|w|+1$ steps total. If the tail is a single bit $b$, the machine first reads $b$ and enters the corresponding second-read state (`step_rd1`); the following position is blank, so it rejects in the next step (`step_rej`). If the tail begins with $10$, it reads the first bit $1$ and enters the second-read state, then reads $0$. This pair is malformed for the pair-symbol decoder, so the transition rejects, again by `step_rej`. Each of the latter cases takes $2|w|+2$ steps. These times are within the claimed bound.

**Key facts.** `BoolCircuit.CircuitEval.setup_scan`, `BoolCircuit.CircuitEval.init_eq`, `BoolCircuit.CircuitEval.step_rej`, `BoolCircuit.CircuitEval.step_rd1`, `Turing.FinTM.inputSymbol_at`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
