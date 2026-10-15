# Declaration freeze comparison

- Action.mapWorkSymbols: unchanged statement and body: True
- Cfg.mapWorkSymbols: unchanged statement and body: True
- MultiTapeTM.mapWorkSymbols: unchanged statement and body: True
- MultiTapeTM.mapWorkSymbols_runFrom: unchanged statement and body: True
- decFixed: unchanged statement and body: True
- decrementTM: unchanged statement and body: True
- decrementTM_run_succ_ofCfg: unchanged statement and body: True
- decrementTM_run_underflow_ofCfg: unchanged statement and body: True
- counterWord: unchanged statement and body: True
- counterOverhead: unchanged statement and body: True
- counterWord_length: unchanged statement and body: True
- counterWord_value: unchanged statement and body: True
- counterOverhead_le_of_le: unchanged statement and body: True
- counterOverhead_le: unchanged statement and body: True
- CounterLoopState: unchanged statement and body: True
- counterLoopStateFintype: unchanged statement and body: True
- counterLoopRedirect: unchanged statement and body: True
- counterLoopDecExit: unchanged statement and body: True
- counterLoopTM: unchanged statement and body: True
## counterLoopCfg — type-only: True

```diff
--- base
+++ after
@@ -1,3 +1,3 @@
-def counterLoopCfg {k : ℕ} {S : Type} {x : List Bool}
-    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
-    (ct : ℤ → Option Bool) (cp : ℤ) : Cfg (k + 1) Bool (CounterLoopState S) x+def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol}
+    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
+    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x
```

## counterLoopOrbit — type-only: True

```diff
--- base
+++ after
@@ -1,2 +1,2 @@
-def counterLoopOrbit {k : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM k Bool S)
-    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) : Cfg k Bool S x+def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
+    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x
```

- counter_cfg_eq: frozen statement, authorized body swap; statement identical: True
- counterLoopTM_run_done: frozen statement, authorized body swap; statement identical: True
- counterLoopTM_run_escape: frozen statement, authorized body swap; statement identical: True
## counterLoop_time_le — type-only: True

```diff
--- base
+++ after
@@ -1,5 +1,5 @@
-theorem counterLoop_time_le {k : ℕ} {S : Type} {x : List Bool}
-    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
+theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol}
+    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
     (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
     (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
     ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
```

- expandTM: unchanged statement and body: True
- expandTM_run_ofCfg: frozen statement, authorized body swap; statement identical: True
- lastEmb: new public declaration; authorized: True
- counterLoopTMVia: new public declaration; authorized: True
- counterLoopTMVia_run_done: new public declaration; authorized: True
- counterLoopTMVia_run_escape: new public declaration; authorized: True
- counterLoopTMVia: exact new brief text: True
- counterLoopTMVia_run_escape: exact new brief text: True
- counterLoopTMVia_run_done: exact new brief text: True
- lastEmb: exact new brief text: True

Surviving ordered declaration sequence identical: True

## Private ledger

Base 24; after 23.

- rewritten: counter_buffer_complement
- removed: counter_last_unselected
- rewritten: counterSpan
- rewritten: counter_span_append
- rewritten: counterPatch
- removed: counter_patch_initial
- rewritten: counter_patch_twice
- rewritten: counter_patch_frame
- rewritten: counter_debit
- rewritten: counter_body
- removed: counter_orbit_succ
- rewritten: counter_rounds
- added: counter_layout
- added: counter_refl_agree

Raw symbol-transport/decrement/arithmetic block identical except authorized complement body: True

Added imports: ['TCSlib.Complexity.TuringMachine.SymbolLift']
Removed imports: []
Final size: 1697 lines; 87771 bytes.

Failures: []
