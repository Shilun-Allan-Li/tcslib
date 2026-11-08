<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.Lupanov.any_comb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjunction of Combination Roots

**Claim.** For \(k\le n\), the disjunction of the values at all combination roots of the circuit constructed from \(f\) and \(k\), on input \(x\), equals \(f(x)\).

**Proof.** Let \(p_0\) and \(r_0\) be the heap-path indices of the first \(n-k\) and last \(k\) coordinates of \(x\), respectively, with the leading powers of two subtracted. The heap-path bounds (\texttt{BoolCircuit.Lupanov.heapPath_bounds}) ensure these are valid indices in the corresponding ranges. By the reconstruction identity (\texttt{BoolCircuit.Lupanov.assemble_heapPath}), assembling these indices recovers \(x\). The bit at position \(r_0\) in the encoded truth table \(\mathrm{code}(f,k,p_0)\) is therefore \(f(x)\): the bit-extraction identity for \(\mathrm{ofBits}\) (\texttt{BoolCircuit.Lupanov.testBit_ofBits}) reduces it to the table entry indexed by \(r_0\), and the range indexing selects \(f\) evaluated at the reconstructed input. Now the value formula for a combination root (\texttt{BoolCircuit.Lupanov.value_comb}) says its value at index \(n+o_C(n,k)+p\) is the conjunction of the test that the first heap path matches \(2^{n-k}+p\) and the truth-table bit for that \(p\). If any combination root is true, this first test forces \(p=p_0\); its second factor is then \(f(x)\), so \(f(x)\) is true. Conversely, choose \(p=p_0\), which is in range by the heap-path bounds. The first factor is true by definition of \(p_0\), and the second is \(f(x)\); hence if \(f(x)\) is true, this root is true. Thus the disjunction over all combination roots is equivalent to \(f(x)\), and the Boolean values are equal.

**Key facts.** `BoolCircuit.Lupanov.heapPath_bounds`, `BoolCircuit.Lupanov.assemble_heapPath`, `BoolCircuit.Lupanov.testBit_ofBits`, `BoolCircuit.Lupanov.value_comb`.
