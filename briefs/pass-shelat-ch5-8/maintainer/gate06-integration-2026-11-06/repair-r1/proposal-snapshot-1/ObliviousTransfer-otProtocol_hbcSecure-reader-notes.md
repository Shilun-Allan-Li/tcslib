# ObliviousTransfer: HBC constructor reader proposal

One unapplied existing term-proof repair for `otProtocol_hbcSecure` in `TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean` (frozen source 654–657).

- Frozen Git context: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
- Frozen source SHA256: `8486698f1624b8bca32baffbc53f7c3f754de6919df367e4245e48d9a3c28e09`.
- Prior output-correctness patch SHA256: `b1faa50f47fa7207dd67ba0246d6820ab95a4316ab854e2b0d0139408fa6d959`.
- Input after composing that patch only in memory: `54744eb63b40489fcd4a700f8f7089b5d167c857fc40fd3157eee558acfdcac1`.
- Combined proposed full source SHA256: `8c9e33bcb6a7593df098efdc543900259d56068c68cba2ce212705384c2e92d3`.
- This separate patch SHA256: `0ab1d177dbc3d2d6b4f4506e238b17d90641f219cbead694059a0466eadd8771`.

The previous proposal was reconstructed and compared byte-for-byte with its saved patch. The current mutable library source was not used as the patch base or edited.

## Root and repair

The valid V3 seal 031 reports original source 656 (probe 706): the tuple cannot construct sealed `HBCSecure (otProtocol T H) otFunctionality`. Apply the reverse direction of the existing public `hbcSecure_iff` before the exact same efficiency proof, simulator witnesses, and simulator-bound proof.

`SecureComputation/Defs.lean:184` publishes:

```lean
hbcSecure_iff (π : Protocol) (F : Functionality) :
  HBCSecure π F ↔
    F.PolyTime π ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
        distAdv (F.realA π n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv (F.realB π n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n
```

The existing `otProtocol_polyTime` conclusion is exactly the first clause. After inserting the unchanged `otSimA T` and `otSimB T hH` witnesses, the existing `otProtocol_simulators T H hH henc hT hEHC` conclusion is exactly the second clause. These types match syntactically through the public contract; no reduction of the functionality, games, efficiency predicate, simulator constructions, or collection hardness predicate is needed. No additional latent foreign-definition read was found in this term proof. No owner reader, helper, transport, or tactic block is added.

## Preserved assumptions and validation limits

The header, including `hT : T.OneWay` and `hEHC : EnhancedHardCore T h`, is byte-identical. The canonical evaluator specification `henc` and evaluator cost `hH` are passed to the same theorem applications as before; the local decodable-input `hspec` consequence in correctness remains untouched. No bare hard-core route or premise erasure is introduced. All algorithms, data definitions, simulator witnesses, security statements, proof sketches, and admissions are preserved.

The diff changes only this one term proof and preserves every source byte outside it relative to the in-memory intermediate input. Tactic-block and admission counts are unchanged. The source's admitted efficiency and simulator theorems remain admitted.

Only this patch and these notes were saved under ignored Gate06 repairs. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process occurred. The composed source remains an uncompiled proposal requiring root's native check.

**Ready to run**
