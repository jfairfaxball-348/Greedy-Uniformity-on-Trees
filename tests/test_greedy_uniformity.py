from fractions import Fraction
import math
import networkx as nx

from experiments.greedy_uniformity import (
    bias,
    brute_force_distribution,
    census,
    family_bias_formula,
    tuned_family_expectation_formula,
    mixed_spider,
    mixed_spider_distribution_by_type,
    mixed_spider_formula,
    recursive_distribution,
)


def test_bruteforce_matches_recursion_through_7():
    for n in range(1, 8):
        trees = [nx.empty_graph(1)] if n == 1 else list(nx.generators.nonisomorphic_trees(n))
        for T in trees:
            assert brute_force_distribution(T) == recursive_distribution(T)


def test_tree_census_through_11():
    rows, total, uniform, counts = census(11)
    assert counts == {1:1, 2:1, 3:1, 4:2, 5:3, 6:6, 7:11, 8:23, 9:47, 10:106, 11:235}
    assert total == 436
    assert uniform == [(1, 0), (2, 0)]
    mins = {n: m for n, _, m in rows}
    assert mins == {
        1: None,
        2: None,
        3: Fraction(1,6),
        4: Fraction(1,12),
        5: Fraction(1,15),
        6: Fraction(1,10),
        7: Fraction(1,30),
        8: Fraction(17,480),
        9: Fraction(16,315),
        10: Fraction(25,576),
        11: Fraction(29,1260),
    }


def test_mixed_spider_formula_12_cases():
    for k in range(1, 5):
        for l in range(1, 4):
            pc, type_probs, mult = mixed_spider_distribution_by_type(k, l)
            fpc, fq = mixed_spider_formula(k, l)
            assert pc == fpc
            for j in range(k+1):
                assert type_probs[j] == {fq[j]}
                assert mult[j] == math.comb(k, j)
            assert bias(mixed_spider(k, l)) == family_bias_formula(k, l)


def test_tuned_family_expectation_identity():
    for k in range(1, 13):
        l = 2**k - k
        b = family_bias_formula(k, l)
        assert tuned_family_expectation_formula(k) == b
        assert b > 0
