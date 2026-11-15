# seq-zk-a static searches

No Lean or Lake command has run; package/bootstrap availability is pending.

- `rg -n 'normaliz|decode|View|StatZK|ZK_iff|simulate_eq|exists_hybrid_gap|exists_withAdvice' TCSlib/Cryptography/ZeroKnowledge TCSlib/Cryptography/Foundations/Probability.lean TCSlib/Complexity/Randomized/NonUniform.lean TCSlib/Complexity/Randomized/Closure.lean`
- `rg -n 'StatZK.*↔|StatZK.*iff|theorem .*StatZK|: StatZK|    StatZK' TCSlib/Cryptography`
- `rg -n 'encodeMsgs.*length|length_encodeMsgs|encodeMsgs.*inject|pairSndD_encodeMsgs|decodeMsgs' TCSlib`
- `rg -n 'decWords|encWords|takeWords|words.*poly|polyTimeComputable.*(Words|words)' TCSlib/Complexity/ClassP/BinaryArith/Words.lean TCSlib/Complexity/ClassP/BinaryArith/Loops.lean`

No public constructor/eliminator for StatZK was found. Its Defs.lean lemmas `mono`, `zk`, `hvzk` preserve the protocol or eliminate to weaker notions; `PerfectZK.statZK` and `PerfectZKAbort.statZK` have stronger unavailable premises. `perfectZK_zeroRounds` only handles zero-round protocols. The target StatZK.seqRep cannot use itself. The attached proposed reader patch is not applied to the frozen source.

## Nearest overlap relatives

- BinaryArith/Words.lean:49 `BinArith.encWords`: same nested pairing encoding as Strategy.encodeMsgs, represented as flatMap.
- BinaryArith/Words.lean:116 `BinArith.decWords_encWords`: generic decoder inversion.
- BinaryArith/Words.lean:81 `BinArith.length_encWords_le`: generic encoded length bound.
- ZeroKnowledge/ThreeColoring/Machines.lean:911 `encodeMsgs_eq_flatMap`: exact bridge to the flatMap representation; public but graph-dependent import.
- ZeroKnowledge/CommitmentLemmas.lean:241 `length_encodeMsgs_le`: existing public encoded length bound for Strategy.encodeMsgs.
- SecureComputation/Yao.lean:350 `decodeMsgs_encodeMsgs`: decoder inversion for Strategy.encodeMsgs; its provider is outside the supplied closure.
- ZeroKnowledge/Defs.lean:168 `ZK_iff`: the proposed StatZK_iff is its statistical analogue and a new reader beside its definition.
