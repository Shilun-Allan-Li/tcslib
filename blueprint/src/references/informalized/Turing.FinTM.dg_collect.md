<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_collect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collection sweep span

**Claim.** A forward collection sweep reads the blocks at coordinates $a$ through $a+n-1$, leaves their read-marked encodings on the left stack in reverse order, and ends at frontier $z+1+nk$ in the specified read state after $1+nk$ steps, while the head stays within the stated interval.

**Proof.** First, the head is at the boundary frontier $z$. The hypothesis that every simulated work-tape head is at least $a$ implies that at coordinate $a$ no tape head lies at $a-1$; the read assignment there is therefore empty with all preceding-head flags false. One forward step turns the reversed-stack configuration into the ordinary sweep configuration at frontier $z+1$. The sweep-turn identity (`sweep_turn_right`) gives this transition, and the head lies between $z$ and $z+1$. Next, the simulator scans the $n$ rows, each containing $k$ tape cells. The read-sweep lemma (`dg_read`) says that after $nk$ steps it has accumulated the read-marked versions of those rows, reached the read information at coordinate $a+n$, and advanced the frontier by $nk$. The prefix-sweep bound (`dg_sweep_prefix`) keeps the head at frontier $z+1+u$ after each prefix of $u\le nk$ scan steps, so it remains between $z+1$ and $z+1+nk$. Joining the initial step and this scan by the span-composition lemma (`dgSpan_add`) gives $1+nk$ total steps. The initial step's interval $[z,z+1]$ is contained in $[z,z+1+nk]$, so the whole run has the required head bound.

**Key facts.** `Turing.FinTM.sweep_turn_right`, `Turing.FinTM.dgSpan_one`, `Turing.FinTM.dg_read`, `Turing.FinTM.tapeZone_length`, `Turing.FinTM.dg_sweep_prefix`, `Turing.FinTM.dgSpan_add`.
