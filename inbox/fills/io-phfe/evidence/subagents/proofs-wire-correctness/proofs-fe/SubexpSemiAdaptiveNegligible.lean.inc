theorem SubexpSASimSecureWith.saSimSecureWith {Sim : SASimulator.Raw S}
    (h : S.SubexpSASimSecureWith Sim) : S.SASimSecureWith Sim :=
  Exists.elim ((S.subexpSASimSecureWith_iff Sim).1 h) fun _ hc =>
    (S.saSimSecureWith_iff Sim).2 fun A q =>
      SubexpSmall.negligible (hc.2 A q) hc.1
