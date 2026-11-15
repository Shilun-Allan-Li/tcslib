from pathlib import Path

root = Path('/Users/seyoonr/.codex/worktrees/derand/tcslib-exchange')
source = (root / 'TCSlib/Complexity/Randomized/Build/IterateFind.lean').read_text()
old = source[source.index('theorem polyTimeComputable_find'):source.index('\nend Complexity.IterateFind')]
body = old[old.index(' := by') + 6:]
body = body.replace('ModuleHost.clean_install dupWord_poly',
                    'ModuleHost.clean_install (polyTimeComputable_id.pairEncode hinit)')
bits_start = body.index('  have hbits :')
bits_end = body.index('  let M :', bits_start)
body = body[:bits_start] + body[bits_end:]
body = body.replace('pairEncode x x', 'pairEncode x (init x)')
body = body.replace('by omega)\n    have hp := hpow x.length',
                    'by omega)\n    have hp := hpow x.length')
body = body.replace('  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R.eval x.length)) T := by\n'
                    '    intro x\n    apply (hF x).mono',
                    '  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T := by\n'
                    '    apply (FinTM.computesFunInTime_iff _ _ _).2\n'
                    '    intro x\n'
                    '    apply ((FinTM.computesFunInTime_iff _ _ _).1 hF x).mono')
body = body.replace('    (fun n => R.eval n) T hFuel\n'
                    '    (fun x => inv_init P x (by simpa using horbit x 0 (Nat.zero_le _)))',
                    '    R T hFuel (fun x => ⟨init x, rfl, hbound x⟩)')
finish = body.index('  obtain ⟨CP, cP, hCP⟩')
body = body[:finish] + '  exact ⟨L, c, A, D, hL⟩\n'
header = '''/-- A guarded search with arbitrary numerical fuel `R` and initial state `init` has a
finite machine computing the first accepted payload (or `[]` on exhaustion) within
`c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)` steps, for constants
`c, A, D`. The step `g`, acceptance word `[acc s]`, payload `out s`, and initial state are
polynomial-time computable; `|init x| ≤ P.eval |x|`. A fuel machine computes
`Nat.bits (R |x|)` within `aF * (|x| + 1) ^ dF`. The displayed common per-round budget
`T n = A * (2 * n + 2 + P.eval n + 5) ^ D` is polynomial; no polynomial bound on `R`
is assumed. [AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4]

**Proof sketch.** Reuse the invariant and guarded-step modules of
`polyTimeComputable_find`, installing `⟨x, init x⟩` at startup. The size guard preserves
the invariant under every step, including steps after the search terminates. Install the
verdict and step modules, emit the payload, and compose their clean calls through the
same five-module host. A common polynomial budget pays for startup, each round, and the
given binary fuel machine. The result-bearing loop combinator then supplies the stated
bound directly, without using the polynomial-fuel normal form `final_bound`. -/
theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    {init : List Bool → List Bool} (hinit : PolyTimeComputable init)
    (R : ℕ → ℕ) (P : PolyExpr)
    (hbound : ∀ x : List Bool, (init x).length ≤ P.eval x.length)
    (F : FinTM Bool) (aF dF : ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length))
      (fun n => aF * (n + 1) ^ dF)) :
    ∃ (M : FinTM Bool) (c A D : ℕ),
      M.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x (init x))))) with
          | some i => out (pairSndD ((step g P x)^[i] (pairEncode x (init x))))
          | none => [])
        (fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)) := by
'''
Path('/private/tmp/derand-worker/harvest.lean.txt').write_text(header + body)
print('Harvest draft lines:', len((header + body).splitlines()))
