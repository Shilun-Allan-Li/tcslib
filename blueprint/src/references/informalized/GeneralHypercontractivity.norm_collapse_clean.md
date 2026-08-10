<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: norm_collapse_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Norm collapse, division form

**Claim.** For `1 ≤ p` and `f : BooleanFunc (n + 1)`,
`expect (fun x' => (|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2)`
equals `expect (fun x => |f x| ^ p)`. This is `norm_collapse_rpow` with the
two-point average written as `(a + b) / 2` instead of `(1/2) * (a + b)`, and with
the equation oriented so the `n`-cube side rewrites to the `(n+1)`-cube side.

**Proof.** A restatement, in two lines:
`convert norm_collapse_rpow p (by linarith) f |> Eq.symm using 2`, then
`exact funext fun x' => by ring` to reconcile `(a + b) / 2` with `(1/2) * (a + b)`
under the `expect`.

**Remark.** `hp : 1 ≤ p` is only used to supply `0 < p` to `norm_collapse_rpow`
by `linarith`, and that hypothesis is itself unused there.

**Used in.** `two_func_hyp_succ`, at the very last step: the two `expect`s of
two-point averages produced by the induction hypothesis are identified with the
full `L^p` and `L^q` norms of `f` and `g` on the `(n+1)`-cube.
