<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_record_shape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialized Record Shape

**Claim.** The serialized record of an action is its eight fixed action bits, followed by the unary encoding of its optional successor state and a terminating zero.

**Proof.** Unpack the record into the five encoded fields: input-head movement, work-tape write action, work-tape movement, output, and successor state. For each of the first four fields, its explicit bit encoding is exactly the corresponding pair of values of the fixed action-bit function; this follows by checking the finitely many possibilities for that field. Thus their concatenation is the list of the eight fixed action bits. If the successor is absent, its encoding is the single terminating zero and the unary successor length is zero. If the successor is $q$, its encoding is a leading one followed by $q$ ones and a zero, giving $q+1$ ones and the terminator. In either case the remaining portion is the stated unary block followed by zero.
