<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_literal_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Serialized Literal

**Claim.** When a literal’s variable index lies within the assignment word, the verifier processes its serialized encoding in exactly $3v+7$ steps, updates the clause accumulator by testing whether the assignment bit at $v$ equals the literal’s polarity, and restores the work head to zero.

**Proof.** Write $v$ for the literal’s index and split the input prefix into the doubled clause marker, the doubled unary encoding of $v$, the doubled separator, and the doubled polarity bit. The pair-encoding decomposition (`Complexity.taut_pair_append`) and the doubling-length identity (`Complexity.taut_double_length`) identify these successive input positions. First, the two-step transition (`Complexity.taut_eval_double`) moves from clause evaluation to unary evaluation. The unary scan result (`Complexity.taut_unary_run`) consumes the $v$ unary symbols and moves the work head to position $v$. A further two-step transition enters polarity evaluation. Since $v<|u|$, the work tape at position $v$ contains the assignment bit $u[v]$ (`Turing.FinTM.bufferTape_nat`); reading the encoded polarity bit therefore updates the accumulator to $c\wedge[u[v]=b]$ and moves the head one position left, to $v-1$. The work-head rewind result (`Complexity.taut_work_rewind`) then takes $v+1$ steps to return the head to zero and resume clause evaluation with that updated accumulator. Concatenating these runs using `Turing.MultiTapeTM.runFrom_add` gives $2+2v+2+2+(v+1)=3v+7$ steps. The established prefix lengths yield the required final input position, while the work tape and output remain as claimed.

**Key facts.** `Complexity.taut_double_length`, `Complexity.taut_eval_double`, `Complexity.taut_pair_append`, `Complexity.taut_unary_run`, `Turing.FinTM.bufferTape_nat`, `Complexity.taut_work_rewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.universal_pair_length`.
