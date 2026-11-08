# Additional current proof candidate

## PolyTimeBlockLoop.lean::polyTimeComputable_isNil

Exact captured source lines156–165:

```lean
theorem polyTimeComputable_isNil :
    PolyTimeComputable (fun w => [decide (w = [])]) := by
  have henc : PolyTimeComputable (fun w => pairEncode [] w) :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  have h := polyTimeComputable_lenLe.comp henc
  convert h using 1
  funext w
  simp only [Function.comp, pairFstD_pairEncode, pairSndD_pairEncode, List.length_nil,
    Nat.le_zero, List.length_eq_zero_iff]
```

## Hardness.lean::clA5Le_native

Exact captured source lines6879–6888:

```lean
private lemma clA5Le_native {f g : List Bool → ℕ}
    (hf : PolyTimeComputable (fun x => List.replicate (f x) true))
    (hg : PolyTimeComputable (fun x => List.replicate (g x) true)) :
    PolyTimeComputable (fun x => [decide (f x ≤ g x)]) := by
  have h := polyTimeComputable_lenLe.comp (hg.pairEncode hf)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
```

Both use the existing public `polyTimeComputable_lenLe` computation contract.
One supplies the empty word/original word to decide emptiness, the other supplies
two computed unary words to decide their numeric comparison. The 167-character target span contains89 matched characters of reader application/refolding scaffold.
The underlying comparison machine and time proof are already shared. No replacement
private comparison implementation, new public fact or API design is introduced.
This bounded source classification is not gate closure or a global debt exemption.
