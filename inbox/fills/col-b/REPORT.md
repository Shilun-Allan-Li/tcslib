# Fill col-b (the `col_zk` ladder): REPORT (checkpoint 5, in progress)

- Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (issue commit, head of PR #210). Local branch `fill/col-b`, never pushed.
- Ran as an **internal worker** under the environment note `issue/internal-env.md` (no preflight, no cache step,
  pre-built olean tree). Machine at start: `nproc` 4, 16 GB RAM (about 15 GB available).

## Ladder status (checkpoint 1)

| Step | Lemma | Status |
|---|---|---|
| 1 | `statClose_sampleColorPair` | filled (note: missing from the checkpoint-1 and -2 sources by an editing slip; restored in commit `7a592167`) |
| 4 | `exists_colSimRed_fixCoins`, `colSimRed_fixed_eq` | filled |
| 5 | `ColZK.hidingView`, `ColZK.polyTimeComputable_hidingView`, `ColZK.exists_colHidingRed`, `ColZK.distAdv_distinguisherL_reparam` (`ColZKMachine.lean`) | machine filled; the identification in `Simulator.lean` is **blocked (E-API)**: no published equation of `msgAt` (Protocol.lean) or `edgeIdxOfMsg` (Language.lean) |
| 2 | `statClose_colRealView` | filled |
| 3 | `statClose_colSim_colSimTrunc` | filled |
| 6 | `exists_colZK_edgeless` | filled |
| 7 | `col_zk` | **partial**: the whole assembly is proved as the private `colZK_zk_of_eqs`, conditional on the two missing equations (E-API); `col_zk` keeps its `sorry`; frontier: `col_zk hC := colZK_zk_of_eqs msgAt_eq edgeIdxOfMsg_eq hC` |

### E-API (found at checkpoint 2)

- `msgAt` (`ThreeColoring/Protocol.lean`): the planted attempt reads the challenge through `msgAt cv i`;
  a machine can only compute `pairFstD (pairSndD^[i] cv)`. Needed: `msgAt_eq : msgAt w i = pairFstD (pairSndD^[i] w)`
  (or, equivalently for the identification, `multiCom_eq` in `Commitment.lean`:
  `multiCom Com v r = Strategy.encodeMsgs (List.ofFn fun i => Com (pairEncode (List.ofFn (v i)) (List.ofFn (r i))))`).
- `edgeIdxOfMsg` (`ThreeColoring/Language.lean`): the planted attempt's restart test is `edgeIdxOfMsg m reply = e₀`;
  a machine computes `reply.length % m`. Needed: `edgeIdxOfMsg_eq : edgeIdxOfMsg m w = w.length % m`.

Evidence: `evidence/check-cp1-Simulator.log`, `evidence/lint-before.log`.
