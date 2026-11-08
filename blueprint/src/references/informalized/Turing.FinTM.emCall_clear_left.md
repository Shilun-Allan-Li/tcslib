<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_clear_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Leftward Scan

**Claim.** For each $0\le j<m$, after exactly $j+2$ steps the cleaner is in state $1$ at the left endpoint, with the data, interval marker, and origin marker unchanged.

**Proof.** Proceed by induction on $j$. For $j=0$, the interval marker is present at the starting head position $\ell$. In state $0$, the cleaner moves all heads one cell left and remains in state $0$; at $\ell-1$ the interval marker is blank, so its next step moves right and enters state $1$. These two steps restore the heads to $\ell$ and do not change any tape. For the successor case, the marker is true at $\ell+j+1$, because $j+1<m$. Thus one state-$0$ step moves the heads left from $\ell+j+1$ to $\ell+j$, without changing tape contents. The run decomposition `runFrom_succ_eq_step` turns the claimed run of length $(j+1)+2$ into this first step followed by a run of length $j+2$. The induction hypothesis applies to that remaining run, since $j<m$, and gives state $1$ at $\ell$ with the tapes unchanged. A zero input-head move leaves the input position fixed (`moveInputPos_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`.
