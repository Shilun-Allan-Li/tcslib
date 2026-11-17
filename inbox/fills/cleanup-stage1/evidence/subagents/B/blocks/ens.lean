
/-- **The tuple encoding is a concatenation of blocks**: the nested-pair encoding of a list of
words is the concatenation of the self-delimiting blocks `⟨c, []⟩`,
`encodeList l = l.flatMap fun c => pairEncode c []`.
Framework glue, no textbook counterpart. -/
protected theorem encodeList_eq_flatMap (l : List (List Bool)) :
    encodeList l = l.flatMap fun c => pairEncode c [] := by
  induction l with
  | nil => rw [encodeList_nil, List.flatMap_nil]
  | cons c cs ih =>
    rw [encodeList_cons, List.flatMap_cons, ih]
    simp only [pairEncode_eq, List.append_nil, List.append_assoc]
