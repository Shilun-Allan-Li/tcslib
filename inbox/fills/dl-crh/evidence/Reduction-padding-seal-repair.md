# Static repair proposal for the sealed padding-word equality

Status: static proposal; kernel and seal verification remain with root. No Lean
process was run and no Lean source was changed for this note.

## Exact failing obligation

Both final2 Reduction seals fail inside `collisionPost_split` at source line
242 (instrumented line 352), in the `hword` proof. Raw evidence is retained in:

- `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_A_DlCrh_final_A_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`;
- `evidence/logs/rule10/final2/seals-final/evidence_probes_Rule10_final2_seals_final_B_DlCrh_final_B_TCSlib_Cryptography_Hashing_FromDiscreteLog_Reduction.001.log`.

The original `simpa only` normalizes a dependent bit-vector length inside
`List.ofFn` and leaves a function of the form

```lean
fun j => padFin ((List.replicate n true).length + 1 +
  ((List.replicate n true).length + 1)) raw (Fin.cast ... j)
```

where the goal has `padFin ((n + 1) + (n + 1)) raw`. With foreign `padFin`
irreducible, the cast-bearing term cannot close by reducing the padding body.
This is an implicit definitional dependence exposed by the seals, even though
the explicit-list scan names only public equations at this location.

## Existing public reader is sufficient

`TCSlib/Cryptography/Asymptotic/CollectionsLemmas.lean` publishes exactly:

```lean
theorem ofFn_padFin_eq_padStr (p : PolyExpr) (u w : List Bool) :
    List.ofFn (padFin (p.eval u.length) w) = padStr p u w
```

There is no missing foreign reader and no need for a new helper or provider
edit. The padding length can be normalized as a separate natural-number
equality using only the local `width`/`u` lets and the published polynomial
evaluation equations.

## Proposed local proof

Replace only the `hword` proof by the following block:

```lean
  have hword : List.ofFn (padFin ((n + 1) + (n + 1)) raw) = padStr width u raw := by
    have hwidth : width.eval u.length = (n + 1) + (n + 1) := by
      simp only [width, u, List.length_replicate, PolyExpr.eval_add,
        PolyExpr.eval_var, PolyExpr.eval_const]
    have hcongr : List.ofFn (padFin (width.eval u.length) raw) =
        List.ofFn (padFin ((n + 1) + (n + 1)) raw) :=
      congrArg (fun k : ℕ => List.ofFn (padFin k raw)) hwidth
    exact hcongr.symm.trans (ofFn_padFin_eq_padStr width u raw)
```

The important step is `congrArg` on the entire list-valued function
`ℕ → List Bool`. Its result type no longer depends on the natural argument.
The local equality transports the whole encoded padding value, and the
published reader is then applied at its original exact width. This avoids
rewriting a natural dimension inside the dependent `List.ofFn` arguments and
requires no access to the body of `padFin`.

Directly rewriting the target by `← hwidth` may also elaborate, but the
nondependent congruence proof states the intended transport explicitly and
avoids the same dependent-rewrite mechanism responsible for the failed
`simpa`. The proof uses no foreign definition in a simplifier list and leaves
the mathematical statement, reduction behavior, and other proof blocks intact.

After the edit, the root worker must kernel-check the helper and consumers,
rerun both seals against a fresh source-bound snapshot, and update final
scan/axiom/sweep provenance as required. The final2 raw failures and the manual
explicit-list review remain evidence for their unchanged final2 snapshot;
neither should be overwritten to claim that the revised source was checked.
