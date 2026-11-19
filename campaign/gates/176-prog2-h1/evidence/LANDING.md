| Mirror | In-place name | File | Statement/body comparison |
|---|---|---|---|
| `XStmt` | `Light.Stmt` | `TCSlib/Programs/Light/Syntax.lean` | MATCH; MATCH |
| `XProgram` | `Light.Program` | `TCSlib/Programs/Light/Syntax.lean` | MATCH; MATCH |
| `XLimits` | `Light.Limits` | `TCSlib/Programs/Light/Syntax.lean` | MATCH (in-place limits plus input); input field, inherited limits integrated in place |
| `inBitVal` | `Light.inBitVal` | `TCSlib/Programs/Light/Syntax.lean` | MATCH; MATCH |
| `inBitVal_eq` | `Light.inBitVal_eq` | `TCSlib/Programs/Light/Syntax.lean` | MATCH; n/a (theorem proof) |
| `XExec` | `Light.Exec` | `TCSlib/Programs/Light/Syntax.lean` | MATCH; MATCH |
| `XExec.append` | `Light.Exec.append` | `TCSlib/Programs/Light/Logic.lean` | MATCH; n/a (theorem proof) |
| `XStmt.assigns` | `Light.Stmt.assigns` | `TCSlib/Programs/Light/Assigns.lean` | MATCH; MATCH |
| `XExec.loc_eq_of_notMem_assigns` | `Light.Exec.loc_eq_of_notMem_assigns` | `TCSlib/Programs/Light/Assigns.lean` | MATCH; n/a (theorem proof) |
| `XExec.bounded` | `Light.Exec.bounded` | `TCSlib/Programs/Light/RunsStayInLimits.lean` | MATCH; n/a (theorem proof) |
| `XExec.mem_outside` | `Light.Exec.mem_outside` | `TCSlib/Programs/Light/RunsStayInLimits.lean` | MATCH; n/a (theorem proof) |
| `XExec.coins_length_le` | `Light.Exec.coins_length_le` | `TCSlib/Programs/Light/IO/Exec.lean` | MATCH; n/a (theorem proof) |
| `XExec.output_length_le` | `Light.Exec.output_length_le` | `TCSlib/Programs/Light/IO/Exec.lean` | MATCH; n/a (theorem proof) |
| `XExec.det` | `Light.Exec.det` | `TCSlib/Programs/Light/IO/Exec.lean` | MATCH; n/a (theorem proof) |
| `XExec.inBit_inv` | `Light.Exec.inBit_inv` | `TCSlib/Programs/Light/IO/Exec.lean` | MATCH; n/a (theorem proof) |
| `XExec.emit_inv` | `Light.Exec.emit_inv` | `TCSlib/Programs/Light/IO/Exec.lean` | MATCH; n/a (theorem proof) |
| `XExec.coin_inv` | `Light.Exec.coin_inv` | `TCSlib/Programs/Light/IO/Exec.lean` | MATCH; n/a (theorem proof) |
| `XExec.half_inv` | `Light.Exec.half_inv` | `TCSlib/Programs/Light/IO/Exec.lean` | MATCH; n/a (theorem proof) |
| `XEnds` | `Light.Ends` | `TCSlib/Programs/Light/Logic.lean` | MATCH; MATCH |
| `EndsIO` | `Light.EndsIO` | `TCSlib/Programs/Light/IO.lean` | MATCH; MATCH |
| `xEnds_iff` | `Light.ends_iff` | `TCSlib/Programs/Light/Logic.lean` | MATCH; n/a (theorem proof) |
| `endsIO_iff` | `Light.endsIO_iff` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.toXEnds` | `Light.EndsIO.toEnds` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.mono` | `Light.EndsIO.mono` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.skip` | `Light.EndsIO.skip` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.set` | `Light.EndsIO.set` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.store` | `Light.EndsIO.store` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.seq` | `Light.EndsIO.seq` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.ite` | `Light.EndsIO.ite` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.whileStep` | `Light.EndsIO.whileStep` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.whileDone` | `Light.EndsIO.whileDone` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.call` | `Light.EndsIO.call` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.inBit` | `Light.EndsIO.inBit` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.emit` | `Light.EndsIO.emit` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.coin` | `Light.EndsIO.coin` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.half` | `Light.EndsIO.half` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XEnds.coin` | `Light.Ends.coin` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `MeetsIO` | `Light.MeetsIO` | `TCSlib/Programs/Light/IO.lean` | MATCH; MATCH |
| `EndsIO.callLast` | `Light.EndsIO.callLast` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `meetsIO_iff` | `Light.meetsIO_iff` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XMeets` | `Light.Meets` | `TCSlib/Programs/Light/Calls.lean` | MATCH; MATCH |
| `xMeets_iff` | `Light.meets_iff` | `TCSlib/Programs/Light/Calls.lean` | MATCH; n/a (theorem proof) |
| `XStmt.shift` | `Light.Stmt.shift` | `TCSlib/Programs/Light/Renumber.lean` | MATCH; MATCH |
| `XProgram.behind` | `Light.Program.behind` | `TCSlib/Programs/Light/Renumber.lean` | MATCH; MATCH |
| `XExec.shift` | `Light.Exec.shift` | `TCSlib/Programs/Light/Renumber.lean` | MATCH; n/a (theorem proof) |
| `XStmt.silent` | `Light.Stmt.silent` | `TCSlib/Programs/Light/IO.lean` | MATCH; MATCH |
| `XStmt.calls` | `Light.Stmt.calls` | `TCSlib/Programs/Light/IO.lean` | MATCH; MATCH |
| `XStmt.silent_seq` | `Light.Stmt.silent_seq` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.silent_ite` | `Light.Stmt.silent_ite` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.silent_while` | `Light.Stmt.silent_while` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.silent_emit` | `Light.Stmt.silent_emit` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.silent_coin` | `Light.Stmt.silent_coin` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.calls_call` | `Light.Stmt.calls_call` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.silent_leaf` | `Light.Stmt.silent_leaf` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.calls_seq` | `Light.Stmt.calls_seq` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.calls_ite` | `Light.Stmt.calls_ite` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.calls_while` | `Light.Stmt.calls_while` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.calls_leaf` | `Light.Stmt.calls_leaf` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XProgram.SilentSet` | `Light.Program.SilentSet` | `TCSlib/Programs/Light/IO.lean` | MATCH; MATCH |
| `XProgram.silentSet_iff` | `Light.Program.silentSet_iff` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XExec.traces_nil` | `Light.Exec.traces_nil` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XProgram.SilentSet.append` | `Light.Program.SilentSet.append` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.silent_shift` | `Light.Stmt.silent_shift` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.calls_shift` | `Light.Stmt.calls_shift` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XProgram.SilentSet.behind` | `Light.Program.SilentSet.behind` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.ofXEnds` | `Light.EndsIO.ofEnds` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `MeetsIO.ofXMeets` | `Light.MeetsIO.ofMeets` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `EndsIO.take_iff` | `Light.EndsIO.take_iff` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `XStmt.size` | `Light.Stmt.size` | `TCSlib/Programs/Light/Compiler/StatementCode.lean` | MATCH; MATCH |
| `XStmt.width` | `Light.Stmt.width` | `TCSlib/Programs/Light/Compiler/StatementCode.lean` | MATCH; MATCH |
| `XStmt.width_inBit_le_iff` | `Light.Stmt.width_inBit_le_iff` | `TCSlib/Programs/Light/Compiler/StatementCode.lean` | MATCH; n/a (theorem proof) |
| `XStmt.width_emit_le_iff` | `Light.Stmt.width_emit_le_iff` | `TCSlib/Programs/Light/Compiler/StatementCode.lean` | MATCH; n/a (theorem proof) |
| `XStmt.width_coin_le_iff` | `Light.Stmt.width_coin_le_iff` | `TCSlib/Programs/Light/Compiler/StatementCode.lean` | MATCH; n/a (theorem proof) |
| `XStmt.width_half_le_iff` | `Light.Stmt.width_half_le_iff` | `TCSlib/Programs/Light/Compiler/StatementCode.lean` | MATCH; n/a (theorem proof) |
| `inBitVal_boundary` | `Light.inBitVal_boundary` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `half_boundary` | `Light.half_boundary` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `check_two_coins` | `Light.check_two_coins` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `check_det_length` | `Light.check_det_length` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
| `check_bounded_needs_word` | `Light.check_bounded_needs_word` | `TCSlib/Programs/Light/IO.lean` | MATCH; n/a (theorem proof) |
