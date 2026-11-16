# Canonical A versus diagnostic B instrumentation

Both variants reconstruct exactly the same current Yao source. Their only instrumentation
change below switches the `PolyExpr.eval` notation exemption off. No proof source differs.

```diff
--- evidence/seals/final-frozen-files/final/Yao_A_strict.lean
+++ evidence/seals/final-frozen-files/final/Yao_B_strict.lean
@@ -35,7 +35,7 @@
             | .proj .. => true
             | .const n _ => env.isProjectionFn n
             | _ => false
-          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
+          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
             (false && coe && projection)
           if isNotation || (status == .reducible && !matcher) then
             excluded := excluded + 1
```

```diff
--- evidence/seals/final-frozen-files/final/Yao_A_coe.lean
+++ evidence/seals/final-frozen-files/final/Yao_B_coe.lean
@@ -35,7 +35,7 @@
             | .proj .. => true
             | .const n _ => env.isProjectionFn n
             | _ => false
-          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
+          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
             (true && coe && projection)
           if isNotation || (status == .reducible && !matcher) then
             excluded := excluded + 1
```
