# Source check for the separation statement

Primary reproduction: Sanjeev Arora, Princeton COS 487, Fall 2010, Assignment 5,
Problem 2, identified as Arora–Barak Exercise 3.2. It asks:

> Show that SPACE(n) ≠ NP.

The same problem cautions that the containment direction is unknown. This supports the
frozen inequality statement and its docstring's refusal to claim either noninclusion direction.
[Official Princeton handout](https://www.cs.princeton.edu/courses/archive/fall10/cos487/hw5.pdf).

Retrieval limit: a direct PDF open returned HTTP 403 in this review. The web search index
returned the text of the official PDF, including Problem 2's identifier and the excerpt above.
This is an indexed-text check, not a claim that the PDF was downloaded or visually inspected.

The formal theorem keeps its already-gated positive normalization `SPACE (n + 1) ≠ NP`.
The existing docstring explains that the library's visited-cell convention makes literal
`SPACE(n)` its zero-work-tape class. This proof-body change does not alter that deviation or
redefine either class; its four defining-context files are in the source population.
