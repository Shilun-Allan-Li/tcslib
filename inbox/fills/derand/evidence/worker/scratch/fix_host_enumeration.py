from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean'
text = path.read_text()
start = text.index('  have hresult :')
end = text.index('  let Q : PolyExpr', start)
text = text[:start] + '''  have hcomputed (x : List Bool) : M.ComputesInTime x
      [decide (2 ^ w x.length <
        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
          pairEncode x (List.ofFn u) ∈ V).card)]
      (c₀ * (A * (2 * x.length + 2 + P.eval x.length + 5) ^ D + 1) *
        (2 ^ w x.length + 2)) := by
    have hx := (FinTM.computesFunInTime_iff _ _ _).mp hM x
    simpa only [hfind, horbit x (2 ^ w x.length) le_rfl, pairSndD_pairEncode,
      payload_state, count_all] using hx
''' + text[end:]
text = text.replace('  apply ((FinTM.computesFunInTime_iff _ _ _).mp hM x).mono',
                    '  apply (hcomputed x).mono')
path.write_text(text)
