# Reproducible experiments

The experiment layer deliberately uses independent verification routes.

- `greedy_uniformity.py`: exact first-vertex recursion using `fractions.Fraction`; independent exhaustive permutation counting; independent brute-force enumeration of maximal independent sets; the mixed-spider closed formula.
- `tests/test_greedy_uniformity.py`: consistency tests and known census checks.

Checks:
1. nonisomorphic-tree counts on n=1..11;
2. exact rational bias census on all 436 trees;
3. brute-force permutation law = first-vertex recursion on every nonisomorphic tree through 7 vertices (25 trees);
4. mixed-spider formula = recursion for 1<=k<=4, 1<=l<=3 (12 cases).

No large permutation search is needed or intended.
