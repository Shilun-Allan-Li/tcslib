# Delayed selector bounds

Two scratch lemmas elaborate on the verified campaign snapshot at
967bc00f00637312676f438c7f61b14219fa943b with standard axioms.

* A globally correct index gives a bound at every stage. Either the
  logarithmic cap already gives the bound, or the index is a candidate
  for the minimum.
* One finite failing word for each index gives eventual divergence.
  For indices below a chosen bound, take the maximum witness length
  and choose a stage where both the query window and cap are large
  enough. The minimum can then select none of those indices.

The decidability and timing premises connecting these statements to
polynomial-time language recognition remain fill work.
