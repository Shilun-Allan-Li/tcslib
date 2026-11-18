theorem SubexpSimSecureWith.simSecureWith {Sim : Simulator.Raw S}
    (h : S.SubexpSimSecureWith Sim) : S.SimSecureWith Sim :=
  Exists.elim ((S.subexpSimSecureWith_iff Sim).1 h) fun _ hc =>
    (S.simSecureWith_iff Sim).2 fun A q =>
      SubexpSmall.negligible (hc.2 A q) hc.1
