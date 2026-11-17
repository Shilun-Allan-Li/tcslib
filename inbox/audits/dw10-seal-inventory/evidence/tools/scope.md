Checkpoint 1 (brief: "the bootstrap, all collectors, and the seals and scan of every owner that holds an input item"):
- done for all 434 owners: the bootstrap (613 modules), the five collectors, the owner check, the item location, the
  explicit-unfold scan, the generated-equation extraction and the reader index;
- seals (all four variants, deduplicated) done for the 96 owners that hold an input item (the 91 owners with
  `ledger_items_at_base` > 0 and the 5 owners of `named-findings.tsv`, 96 together), plus every further owner the four workers finished
  before the snapshot; `seals.tsv` marks every other owner-variant `NOT_RUN`;
- `inventory.tsv` gives every one of the 1,779 input rows a status (608 HANDED-OFF from the records); classes are the tool's
  first assessment (`tools/reconcile.py`), to be reviewed for the final; NEW rows are listed for the sealed owners and the scan
  (all owners) only, so NEW seal rows are incomplete at this checkpoint;
- the controls (20 harnesses, strict and coe, with their unsealed pretest) are running; their table comes with the final;
- remaining for the final: the seals of the other owners, the controls, the classification review, the tree restore check and
  the complete evidence.
