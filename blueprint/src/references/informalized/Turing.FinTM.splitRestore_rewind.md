<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitRestore_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Cleaned Configuration

**Claim.** For every $j\le |s|$, running the cleanup machine for $j+1$ steps from state $(1,\mathrm{false})$, with the first tape storing $s$, blank scratch tapes, and work heads at displacement $j-1$, reaches state $(2,\mathrm{false})$ with the input head and tape contents unchanged and all work heads at displacement $0$.

**Proof.** Proceed by induction on $j$. For $j=0$, the first work head starts at displacement $-1$, where the buffered tape is blank (`bufferTape_left`). The state-$1$ transition therefore moves that head one position right, to $0$, while leaving the input head, tape contents, and output unchanged and entering state $(2,\mathrm{false})$. The one-step run follows from the zero-time and successor-time identities for runs (`runFrom_zero`, `runFrom_succ_eq_step`), and a zero input-head movement fixes its position (`moveInputPos_zero`). For the successor case, suppose the assertion holds at $j$ and $j+1\le |s|$. The starting head displacement for the $j+1$ case is $j$. The cell there contains $s[j]=1$, since $j<|s|$; the buffered-tape identity at natural positions gives this read (`bufferTape_nat`). The state-$1$ transition sees that symbol and moves the work heads one position left, without changing the input position, tape contents, output, or state. Since $(j+1)-1=j$, this step takes the configuration to the induction case's starting configuration, with displacement $j-1$. The induction hypothesis then supplies the remaining $j+1$ steps to state $(2,\mathrm{false})$ with heads at $0$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
