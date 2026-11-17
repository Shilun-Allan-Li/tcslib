<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.PrefixByLength.goes_total -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Processing of a Pair Encoding

**Claim.** For either choice of the program parameter and every bit string $z$, the program reaches a halted state from its scan label, zero register, and input position zero, appending the specified prefix or suffix of the parsed second component. This holds for every output already printed, within $5(|z|+1)$ steps.

**Proof.** Split according to whether decoding $z$ succeeds. If it succeeds with components $u$ and $r$, the decoder characterization says $z$ is exactly the pair encoding of $u$ and $r$ (`Turing.eq_pairEncode_of_pairDecode`). The program’s established behavior on a valid pair encoding (`Complexity.PrefixByLength.goes_pair`) then gives a halted run that appends the first $|u|$ bits of $r$ when the parameter is true, or the suffix after those bits when false. These are precisely the outputs specified by `take` and `drop`.

If decoding fails, the failed-decoding characterization writes $z$ as $\operatorname{dbl}(u)$ followed by a tail of one of three forms: empty, a single bit, or a string beginning $10$ (`Turing.pairDecode_eq_none`). On the doubled prefix, the program consumes the paired encoding and increments its register once for each bit of $u$, returning to the scan label with register $|u|$ and input position $2|u|$; this is the behavior of `goes_doubled`. The listed tail forms are handled by `goes_bad_tail`: starting at the scan label with that register and position zero in the tail, the program halts without appending output. Prepending the doubled prefix shifts the input positions accordingly (`Goes.prepend_input`), and composing these two runs gives the required halted run (`Goes.trans`). Finally, in this failure case both decoded components default to empty, so the requested output is empty; the final state and the step bound agree with the claimed register assignment, position, and bound (`Goes.congr`).

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Complexity.PrefixByLength.goes_pair`, `Turing.pairDecode_eq_none`, `Complexity.PrefixByLength.goes_doubled`, `Complexity.PrefixByLength.goes_bad_tail`, `Complexity.CounterProg.Goes.prepend_input`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.congr`.
