<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_columns_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Execution of the multiplication procedure

**Claim.** From the specified column-processing configuration, the fixed procedure halts with the truth value of the condition that the output length is admissible, the final carry vanishes, and all output bits from column $j$ onward match the required parities.

**Proof.** Let $N=|a|+|b|$. The proof uses strong induction on the number $N-j$ of columns remaining, while carrying along the register bounds and layout information. If $j=N$, the column state proceeds to the final-position check. The register addresses and the encoded-input length identify the result endpoint with the input length exactly when $|c|\le N$, and the final carry test checks $K_N=0` (`mult_finish`). This produces the required truth value in the terminal case.

For $j<N$, the procedure clears its working registers and runs the outer multiplication loop to accumulate the column sum in the carry register. The loop invariant preserves the relevant address and layout registers, and the row-to-column identity identifies the accumulated total with $C_j(a,b)$ (`mult_outer_loop`, `multRows_column`). The encoded-input address formula identifies the result bit being read with $c_j$ (`mult_addresses`), while the result reader obtains that bit and the parity routine compares it with the accumulated carry-plus-column value (`mult_result_read`, `mult_parity`).

If this comparison fails, the remaining-column condition is false by its one-step characterization, so the procedure halts negatively (`mult_remaining_step`). If it succeeds, the carry-halving and register updates advance the column and update the carry to $K_{j+1}$. The layouts and bounds persist, allowing the induction hypothesis to handle the remaining $N-(j+1)$ columns. The one-step characterization shows that the condition at column $j$ is precisely the conjunction of the successful parity test and the condition for the next column (`mult_remaining_step`). Chaining the preliminary reset, loop, read, parity, and next-column executions gives the required halt from the original configuration (`AReach.step`, `AReach.halt`).

**Key facts.** `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AReach.halt`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`, `Complexity.multCarry_le`, `Complexity.multColumn_le`, `Complexity.multRows_column`, `Complexity.mult_addresses`, `Complexity.mult_finish`, `Complexity.mult_next_column`, `Complexity.mult_outer_loop`, `Complexity.mult_parity`, `Complexity.mult_preconditions`, `Complexity.mult_remaining_step`, `Complexity.mult_result_read`, `Turing.length_pairEncode`.

**Caveat.** The argument follows the supplied proof structure, but several central execution facts are only stated as upstream lemmas, and the supplied statement of `mult_outer_loop` is truncated. The details of the loop's register-level behavior cannot be fully checked from the provided payload.
