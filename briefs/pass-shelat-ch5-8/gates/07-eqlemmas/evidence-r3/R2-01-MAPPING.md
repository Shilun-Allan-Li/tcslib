# R2-01: padded permutation-collection consumer — example → source line → log line

Head: `eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee` (olean tree from the replay in `replay-head.log`).
Files in `probes/`. Each file is elaborated outside `HardCoreCollection.lean`, importing it.

**Seal** (`R201PassSealed.lean`/`R201ControlSealed.lean` line 8; list in `probes/seal-list.txt`): 42 constants made
`local irreducible`: `PermCollection.glPad`, `Collection.glPad`, every plain TCSlib definition reached from their
elaborated types and values (transitively), the matchers reached (`Collection.glPad.match_1/_3`,
`Turing.pairDecode.match_1`, `Turing.Action.apply.match_1`, `Turing.MultiTapeTM.step.match_1`), and in addition
`PermCollection.glPad_domEquiv`. Not sealed: `PolyExpr.eval` (and its matcher), `glNeed` (not reached);
reducible/abbrev, projection and instance constants (`R201Collect.log` lists every reached constant with its kind).
The `*Open.lean` copies are identical without the seal line (lines shifted up by one).

| Example | Claim | Sealed file:line | Sealed log | Open file:line | Open log |
|---|---|---|---|---|---|
| P1 | domain: `P.glPad_domEquiv m henc i : (P.glPad m henc).D i ≃ D_i × {0,1}^L` | PassSealed:17 | `R201PassSealed.log` l.1 `rc=0`, no diagnostic | PassOpen:16 | `R201PassOpen.log` l.1 `rc=0` |
| P2 | domain round trip `e⁻¹ (e z) = z` | PassSealed:21 | same | PassOpen:20 | same |
| P3 | conjugated permutation `perm' = e⁻¹ ∘ (perm_i × id) ∘ e` (`glPad_perm`) | PassSealed:26 | same | PassOpen:25 | same |
| P4 | application: `e (perm' z) = (perm_i (e z).1, (e z).2)` (from `glPad_perm`) | PassSealed:32 | same | PassOpen:31 | same |
| P5 | application: `perm' (e⁻¹ (x, r)) = e⁻¹ (perm_i x, r)` | PassSealed:39 | same | PassOpen:38 | same |
| P6 | application: `perm'⁻¹ (e⁻¹ (x, r)) = e⁻¹ (perm_i⁻¹ x, r)` | PassSealed:46 | same | PassOpen:45 | same |
| P7 | field: `f' i z = encD' i (perm' i z)` (`f_perm` of `P.glPad m henc`) | PassSealed:55 | same | PassOpen:54 | same |
| C1 (↔ P1/P2) | old reading: `z.1 : D_i` for `z : (P.glPad m henc).D i` | ControlSealed:17 | `R201ControlSealed.log` l.1 (17:46, invalid field notation) | ControlOpen:16 | `R201ControlOpen.log` l.1 `rc=0` |
| C2 (↔ P1/P2) | old reading: `(x, r) : (P.glPad m henc).D i` | ControlSealed:20 | l.5 (20:89, type mismatch) | ControlOpen:19 | same |
| C3 (↔ P4) | old reading: `perm' z = (perm_i × id) z` by `rfl` | ControlSealed:24 | l.11 (25:68, application type mismatch) | ControlOpen:23 | same |
| C4 (↔ P3) | old reading: the P3 equation by `rfl` | ControlSealed:29 | l.19 (31:2, type mismatch) | ControlOpen:28 | same |
| C5 (↔ `glPad_domEquiv_apply`) | `e z = z`, the `_apply` statement itself | ControlSealed:35 | l.27 (35:67, type mismatch) | ControlOpen:34 | same |

Sealed control file: 5 errors, one per control (log lines 1, 5, 11, 19, 27). Open control file: `rc=0`, no error.
Pass files: `rc=0`, no diagnostic, sealed and open.

`glPad_domEquiv_apply` (`e z = z`) is a statement about the definition: it is well typed only by reading
`(P.glPad m henc).D i` as the product, so a sealed consumer cannot state it (C5). The consumer interface for
the domain and application is `glPad_domEquiv` with the `Equiv` lemmas (P1, P2) and `glPad_perm` (P3–P6);
no equation had to be added.
