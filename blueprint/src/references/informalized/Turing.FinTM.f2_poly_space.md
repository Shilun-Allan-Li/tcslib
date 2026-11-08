<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_poly_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary catalog space bound

**Claim.** For all natural numbers $d,C,t$ and Boolean words $x$, the unary catalog machine with parameters $d,C$ visits at most $5(d+1)(|x|+1)$ work-tape cells in total by time $t$.

**Proof.** Fix the machine and put $q=|x|+1$. First consider the configuration reached after $2q$ steps. The start lemma (`f2_catalogPoly_start`) identifies it as the prescribed loop configuration with every head at zero. From then on, induction on the number of additional steps, using preservation of the tape contents and stage-dependent head bounds (`f2_poly_step`), shows that every tape remains the fixed unary tape and the control-state invariant continues to hold. The initial segment is controlled separately: a head moves by at most one per step, so after $u\le 2q$ steps its position lies between $-u$ and $u$ (`f2_head_steps`). After time $2q$, the invariant and the stage-to-uniform-bounds implication (`f2_polyHeads_bounds`) put every head between $-1$ and $q$. Thus, at every time, each head lies in the integer interval $[-2q,2q]$. The set of positions visited by any one head is contained in that interval, whose cardinality is $4q+1\le5q$. Summing this bound over the $d+1$ tapes gives at most $5(d+1)q$ visited cells in total.

**Key facts.** `Turing.FinTM.f2_catalogPoly_start`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_poly_step`, `Turing.FinTM.f2_head_steps`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_polyHeads_bounds`.
