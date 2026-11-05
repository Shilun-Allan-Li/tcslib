# S3b: Yao in the OT-hybrid model, and the composition theorem (design, 2026-11-05)

**Rulings (user, 2026-11-05).** Q-5 option 1: Yao (Prot 162.6) is stated with an ideal OT, Thm
163.7 in that model; [Gol04] §7.3's composition theorem is stated separately, and the real
protocol follows. Efficiency: `HBCSecure` requires polynomial-time parties (`Efficient`
strategies and polynomially bounded honest messages), in the definition.

## Pieces (prong B, `cryptography/pass-shelat-ch5-8-prong-b`)

| File | Content | Author |
|---|---|---|
| `SecureComputation/Defs.lean` | `Functionality.PolyTime`; `HBCSecure` requires it | maintainer, `e6bc92ed` |
| `SecureComputation/Hybrid.lean` | `HybridProtocol G` (ideal calls first), hybrid samplers, `PolyTime`, `HBCSecure` | maintainer, `1cf007d1` |
| `SecureComputation/Compose.lean` | `HybridProtocol.compose ρ`, its phase lemmas, `hbcSecure_compose` ([Gol04, Thm 7.3.3]) | worker |
| `SecureComputation/Yao.lean` | uniform circuits, `yaoFunctionality`, string-level garbling, `yaoHybrid`, Thm 163.7 in the OT-hybrid model | worker |
| (then) the real Yao | `(yaoHybrid …).compose (otProtocol T H)` is secure: a corollary by term | maintainer |

## The hybrid model: ideal calls first

[Gol04]'s oracle-aided protocols interleave calls and messages. Yao needs only calls whose
inputs are fixed before any message: Alice's OT inputs are her wire keys (from her coins), Bob's
his input bits. So `HybridProtocol G` = `calls(n)` ideal calls, inputs computed from
`(1^n, input, coins in main)`, then a D8 protocol `main` on private inputs `⟨input, answers⟩`.
A party's view in `main` then holds its input, coins, answers and received messages.

`PolyTime` bounds `main`'s messages for **any** answers of the right lengths: the composition
feeds `main` the sub-protocol's outputs, which equal the ideal answers only computationally.

## The composed protocol (layout fixed in the worker's brief)

- Alice moves first. `calls(n)` slots of `2·R_ρ` moves each (`R_ρ = ρ.rounds(n)`): ρ's move `p`
  of run `j` occupies the pair `R_ρ·j + p`, at its even position if Alice makes it and its odd
  one if Bob does; the other position of the pair is an empty filler. This keeps D8's strict
  alternation without parity arithmetic on `PolyExpr`s.
- Then `main`: one leading empty Alice message if `main.verifierFirst`, then `main`'s moves.
  No trailing filler: under D8 the last mover's last message is its output, so a trailing filler
  would leak an output to the other party.
- Coins: `main`'s tape, then one ρ tape per run. Run `j` is played on the call inputs of the
  hybrid; each party's answer is its ρ output read at `G`'s output length (`padFin`).

## Yao (string level; choices fixed in the worker's brief)

- **Circuits:** `main`'s `DAGCircuit` with an output list, fan-in two, polynomial size, and
  uniform (a polynomial-time map `1^n ↦` the circuit's encoding). Uniformity is needed for
  Alice's strategy to be efficient; the source's "canonical circuit representation of `f`".
- **The functionality:** both parties get `C_n(x, y)` at the output vertices.
- **Keys** `n`-bit; the rows encrypted with `nestedSpecial E₁ E₂ n` (Alg 157.2, nested).
- **Row order: a random XOR-shift of the assignment** (declared deviation). The source shuffles
  each table uniformly; a table of four rows has 24 orders, which a fixed number of coin bits
  cannot sample exactly. A uniform shift by `λ ∈ {0,1}^{fan-in}` makes the opened row's position
  uniform and independent of the inputs, which is what the simulation uses (the
  point-and-permute idea of Beaver, Micali and Rogaway, 1990).
- **Output decoding:** Alice's message carries each output vertex's key pair `(k⁰, k¹)`; Bob
  decodes by comparison. The source does not say how Bob reads the output (S3b note, item 2).
- **OT calls:** `inB(n) · n` bit OTs, call `(i, t)` transferring bit `t` of wire `inA + i`'s
  keys with Bob's choice `y_i`.
- **Messages:** Alice sends the garbled tables, her input keys and the decoding pairs; Bob
  evaluates, decodes and sends `f(x, y)`; both output it (Bob as last mover).
