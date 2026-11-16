from pathlib import Path
base = Path('evidence/subagents/a/versions')
scanner = (base / 'chunk-scanner-02.lean').read_text()
scanner = scanner.replace('theorem phase_eq : Phase = (Bool × Bool × Bool) := rfl',
                          'theorem phase_eq : Phase = Bool × Bool × Bool := rfl')
scanner = scanner.replace('simp only [emit_eq, readPhase_eq, decide_eq_true_eq, Function.comp_apply]',
                          'simp only [emit_eq, readPhase_eq, decide_eq_true_eq]')
scanner = scanner.replace('List.headD_nil, List.drop_nil, scan_nil',
                          'List.headD_nil, List.drop_nil, if_pos rfl, List.nil_append, scan_nil')
(base / 'chunk-scanner-01.reconstructed.lean').write_text(scanner)
s = (base / 'garbling-02.lean').read_text()
a = s.index('/-- A selector over at most two argument positions')
b = s.index('/-- For a gate with at most two arguments', a)
s = s[:a] + s[b:]
a = s.index('/-- The encoded argument-key list is polynomial-time')
s = s[:a] + 'end TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling\n'
a = s.index('  rw [argKeys_eq]\n', s.index('theorem argKeys_small'))
b = s.index('\nend TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling', a)
s = s[:a] + '''  rw [argKeys_eq]
  generalize hargs : (C.gates[i]).args = args at a hfan ⊢
  cases args with
  | nil =>
    simp only [List.ofFn_zero, List.map_nil, BinArith.encWords_nil]
    rfl
  | cons u args =>
    cases args with
    | nil =>
      simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
        BinArith.encWords_cons, BinArith.encWords_nil]
      rfl
    | cons v args =>
      cases args with
      | nil =>
        simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
          BinArith.encWords_cons, BinArith.encWords_nil]
        rfl
      | cons w args => simp only [List.length_cons] at hfan; omega
''' + s[b:]
a = s.index("  -- Compute each kind's output")
b = s.index('  have h := polyTimeComputable_ite hkAnd', a)
s = s[:a] + '''  -- Compute each kind's output from at most two assignment bits.
  have hAnd := polyTimeComputable_ite hzero (polyTimeComputable_const [true])
    (polyTimeComputable_ite hone h₀ (polyTimeComputable_and h₀ h₁))
  have hOr := polyTimeComputable_ite hzero (polyTimeComputable_const [false])
    (polyTimeComputable_ite hone h₀ (polyTimeComputable_or h₀ h₁))
''' + s[b:]
s = s.replace('cases k <;>\n          simp [gateOut_eq_eval, DAGGate.eval_eq, List.range_succ]',
              'cases k <;> rw [gateOut_eq_eval, DAGGate.eval_eq] <;> rfl')
s = s.replace('  simp only [Function.comp_apply]\n  rw [spEncFun_eq', '  rw [spEncFun_eq')
s = s.replace('simp only [nestedWordEnc_eq, decide_eq_true_eq, Function.comp_apply]',
              'simp only [nestedWordEnc_eq, decide_eq_true_eq]')
s = s.replace('zero and one argument tests', 'zero-/one-argument tests')
(base / 'garbling-01.reconstructed.lean').write_text(s)
for name in ['chunk-scanner-01.reconstructed.lean', 'garbling-01.reconstructed.lean']:
    rows = (base / name).read_text().splitlines()
    print(name, len(rows))
    lines = [143,157,234] if name.startswith('chunk') else [50,90,215,218,223,229,246,289]
    for i in lines:
        print(f'{i}: {rows[i-1]}')
