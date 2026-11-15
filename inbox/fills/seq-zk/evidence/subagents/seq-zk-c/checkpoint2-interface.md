# Proposed checkpoint 2 helper interface

No additional helper code has been written. The proposed declarations below stay in
`SequentialZK/Soundness.lean` and import no owned SequentialZK definitions.

## Fixed-tape, prefix-hardwired prover

```lean
@[simps (config := { isSimp := false }) coins next]
def prefixProver (P : Strategy) (y rP : List Bool)
    (prior : List (List Bool)) : Strategy where
  next x _ _ hist := P.next x y rP (prior ++ hist)
  coins := .const 0
```

The extra `y` parameter keeps the construction general; soundness instantiates `y=[]`.
This is a strategy wrapper, with no new recursion or machine host. Its field readers
will be used by foreign consumers. It ignores its own auxiliary input and tape.

## Real-phase execution after a fixed earlier prefix

```lean
theorem exec_phase (P V W : Strategy) (vFirst : Bool)
    (x y z rP rV rW : List Bool) (g k : ℕ)
    (hturn : ∀ t < k, moverIsV vFirst (g + t) = moverIsV vFirst t)
    (hV : ∀ t < k, moverIsV vFirst t = true →
      V.next x z rV (exec P V vFirst x y z rP rV (g + t)).2 =
        W.next x z rW
          ((exec P V vFirst x y z rP rV (g + t)).2.drop
            (exec P V vFirst x y z rP rV g).2.length))
    {t : ℕ} (ht : t ≤ k) :
    (exec P V vFirst x y z rP rV (g + t)).1 =
        (exec P V vFirst x y z rP rV g).1 ++
          (exec (prefixProver P y rP (exec P V vFirst x y z rP rV g).1)
            W vFirst x [] z [] rW t).1 ∧
      (exec P V vFirst x y z rP rV (g + t)).2 =
        (exec P V vFirst x y z rP rV g).2 ++
          (exec (prefixProver P y rP (exec P V vFirst x y z rP rV g).1)
            W vFirst x [] z [] rW t).2
```

Proof: induction on `t≤k`, reading only `exec_zero` and `exec_succ`. At a prover move,
rewrite the full prover history by the first induction equality and read prefixProver's
next-message equation. At a verifier move, use `hV`, rewrite the full received history
by the second induction equality, and drop the fixed prefix. List append associativity
then gives both history equalities.

For the repetition, the lead takes `g=2*k*j`, `W=π.V`, `rW=coinBlock c j rV`, and proves
`hturn` by periodicity. The published count/index readers and the owned seqVerifier
reader prove `hV`; the length of the preceding verifier history is exactly `j*k`.
The helper does not know any repetition construction.

## Bounded congruence for future-block nonanticipation

A separate optional theorem can show executions agree whenever the full verifier
replies agree on the actual reached histories up to a bound:

```lean
theorem exec_eq_of_verifier_next_eq (P V W : Strategy) (vFirst : Bool)
    (x y z rP rV rW : List Bool) (k : ℕ)
    (hV : ∀ t < k, moverIsV vFirst t = true →
      V.next x z rV (exec P V vFirst x y z rP rV t).2 =
        W.next x z rW (exec P V vFirst x y z rP rV t).2) :
    exec P V vFirst x y z rP rV k = exec P W vFirst x y z rP rW k
```

The lead could then use it to prove that a prefix of verifier coin blocks fixes all
messages before the next phase. This is the remaining nonanticipation bridge required
before calling `uprob_adaptive_all_le` on prefix-indexed phase events.

## Search and overlap disclosure

Searches found no generic execution-from-prefix theorem in Interaction or the seqRep
module. Public `LevinTransfer.exec_congr` at `ZeroKnowledge/NPLemmas.lean:88` proves
full execution congruence when both parties' next-message functions agree on *all*
histories. It is outside the supplied order closure, and it cannot directly prove the
proposed bounded actual-history congruence. Any new congruence will disclose this nearest
relative. The planned phase theorem generalizes the *proof pattern* of the owned
`seqRep_exec_phase`, while allowing an arbitrary cheating prover and a hardwired prefix;
it must not copy or unfold owned definitions from the helper.

## Implementation status

The first two interfaces above are now implemented and Lean-checked in NEW `SequentialZK/Phases.lean`, as approved by the lead. The optional bounded-congruence interface remains unimplemented. See phases-check-02.log and phases-results.jsonl.
