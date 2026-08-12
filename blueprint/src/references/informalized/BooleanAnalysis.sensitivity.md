<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: sensitivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Sensitivity of a function at a point

**Definition.** For `f : BooleanFunc n` and `x : BoolCube n`,

```
sensitivity f x = (Finset.univ.filter (fun i : Fin n => f x ≠ f (flipBit x i))).card
```

a natural number: the number of coordinates `i` whose single-bit flip changes
the value of `f` at `x`. `flipBit x i` is `x` with bit `i` negated. A plain
`noncomputable def` with no proof content — `noncomputable` because the filter
predicate decides equality of reals, so the `Finset.filter` needs classical
decidability.

**Remark.** This is the pointwise, combinatorial cousin of `influence`: where
`influence i f` averages `(f x - f (flipBit x i))² / 4` over the whole cube,
`sensitivity` counts sensitive coordinates at a *single* `x` and discards the
magnitude of the change.

**Used in.** Only `maxSensitivity` (same file, line 915), which takes the
supremum of `sensitivity f` over all inputs. The relation between sensitivity
and influence that this section's heading ("Sensitivity and block sensitivity")
anticipates is not formalized — no lemma in the repository connects
`sensitivity` to `influence`, and block sensitivity is not defined at all.
