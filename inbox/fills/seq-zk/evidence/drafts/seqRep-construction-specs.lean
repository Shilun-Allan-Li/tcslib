-- Pending owned-module insertion after the checked helper contracts are integrated.
-- These complete reader-only bodies are not claimed as checked yet.

/-- The repeated verifier satisfies the padded-verifier equations on `x`, with
`q=Q.eval |x|` and `p=proverMoves π.verifierFirst (π.rounds.eval |x|)`.
[PS10, Theorem 175.1].

**Proof sketch.** Read the coin, round, mover and next-message fields of the construction.
The existing move-index and message-count readers give each remaining contract field.
The aggregate verdict is its published conjunction of phase tests. -/
theorem seqRep_verifierSpec (π : Protocol) (Q : PolyExpr) (x : List Bool) :
    PaddedVerifierSpec π (π.seqRep Q) x (Q.eval x.length)
      (proverMoves π.verifierFirst (π.rounds.eval x.length))
      (fun z r hist => π.seqVerdict (Q.eval x.length) x z r hist) := by
  refine { coinLen_eq := ?_, rounds_eq := seqRep_rounds_eval π Q x.length,
    first_eq := seqRep_verifierFirst π Q, next_eq := ?_, terminal_eq := ?_,
    index_eq := ?_, boundary_lengths := ?_, local_length := ?_, period := ?_ }
  · rw [Strategy.coinLen_eq, seqRep_V, seqVerifier_coins, PolyExpr.eval_mul,
      Strategy.coinLen_eq]
  · intro z r hist
    rw [seqRep_V, seqVerifier_next, verifierMoveIndex_eq]
  · intro z r hist
    exact seqVerdict_eq π (Q.eval x.length) x z r hist
  · intro P y z rP rV t hm
    simpa only [verifierMoveIndex_eq] using
      verifierMoveIndex_exec P (π.seqRep Q).V π.verifierFirst x y z rP rV t hm
  · intro P y z rP rV j _
    exact exec_boundary_lengths P (π.seqRep Q).V π.verifierFirst x y z rP rV
      (π.rounds.eval x.length) j
  · intro P y z rP rV
    rw [exec_snd_length, proverMoves_eq]
  · intro j t
    rw [show 2 * π.rounds.eval x.length * j + t =
      2 * (π.rounds.eval x.length * j) + t by ring]
    exact moverIsV_two_mul_add _ _ _

/-- The repeated prover satisfies the padded-prover equations on `x`, with
`q=Q.eval |x|` and `p=if π.verifierFirst then k/2 else (k+1)/2`, for
`k=π.rounds.eval |x|`. [PS10, Theorem 175.1].

**Proof sketch.** Read the prover's coin and reply equations. Recover actual move indices
using the existing prover index reader and obtain phase-boundary and local counts from
the published execution-length readers. The even phase length preserves the mover pattern.
-/
theorem seqRep_proverSpec (π : Protocol) (Q : PolyExpr) (x : List Bool) :
    SequentialZK.PaddedProverSpec π (π.seqRep Q) x (Q.eval x.length)
      (if π.verifierFirst then π.rounds.eval x.length / 2
        else (π.rounds.eval x.length + 1) / 2) := by
  refine { prover_coinLen := ?_, rounds_eval := seqRep_rounds_eval π Q x.length,
    first := seqRep_verifierFirst π Q, next := ?_, prover_index := ?_,
    boundary := ?_, original_count := ?_, real_le := ?_, period := ?_ }
  · rw [Strategy.coinLen_eq, seqRep_P, seqProver_coins, PolyExpr.eval_mul,
      Strategy.coinLen_eq]
  · intro y r hist
    rw [seqRep_P, seqProver_next, proverMoveIndex_eq]
  · intro V y z rP rV n hm
    simpa only [proverMoveIndex_eq] using
      proverMoveIndex_exec (π.seqRep Q).P V π.verifierFirst x y z rP rV n hm
  · intro V y z rP rV j
    exact exec_boundary_lengths (π.seqRep Q).P V π.verifierFirst x y z rP rV
      (π.rounds.eval x.length) j
  · intro V y z rP rV
    rw [exec_snd_length, countP_not_moverIsV]
  · cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  · intro j t
    rw [show 2 * π.rounds.eval x.length * j + t =
      2 * (π.rounds.eval x.length * j) + t by ring]
    exact moverIsV_two_mul_add _ _ _
