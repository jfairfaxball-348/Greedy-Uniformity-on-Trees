"""Targeted Stage-3 checks for the local proof certificates.

These are not proof. They test the exact local cases that arose in the proof,
rather than extending the blind tree census.
"""

from __future__ import annotations

from fractions import Fraction

import networkx as nx

from experiments.greedy_uniformity import maximal_independent_sets, recursive_distribution


def mis_count(G: nx.Graph) -> int:
    return len(maximal_independent_sets(G))


def greedy_marginal(distribution, v) -> Fraction:
    return sum(p for I, p in distribution.items() if v in I)


def uniform_marginal(maximal_sets, v) -> Fraction:
    return Fraction(sum(v in I for I in maximal_sets), len(maximal_sets))


def diameter_end_structure(T: nx.Graph):
    lengths = dict(nx.all_pairs_shortest_path_length(T))
    d = max(lengths[u][v] for u in T for v in T)
    x, far = next((u, v) for u in T for v in T if lengths[u][v] == d)
    path = nx.shortest_path(T, x, far)
    y = path[1]
    leaves = [w for w in T.neighbors(y) if T.degree(w) == 1]
    nonleaves = [w for w in T.neighbors(y) if T.degree(w) > 1]
    return d, x, y, leaves, nonleaves


def verify_stage3_local_certificates(max_n: int = 11):
    summary = {
        "trees": 0,
        "stars": 0,
        "multi_leaf": 0,
        "single_leaf": 0,
        "paired_sets": 0,
    }

    for n in range(3, max_n + 1):
        for T0 in nx.generators.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T0, ordering="sorted")
            d, x, y, leaves, nonleaves = diameter_end_structure(T)
            distribution = recursive_distribution(T)
            maximal_sets = maximal_independent_sets(T)
            summary["trees"] += 1

            assert len(nonleaves) <= 1
            assert greedy_marginal(distribution, y) != uniform_marginal(maximal_sets, y)

            if d == 2:
                summary["stars"] += 1
                assert not nonleaves
                assert len(leaves) >= 2
                continue

            assert len(nonleaves) == 1
            z = nonleaves[0]

            if len(leaves) >= 2:
                summary["multi_leaf"] += 1
                R = T.copy()
                R.remove_nodes_from(set(leaves) | {y})
                F = R.copy()
                F.remove_node(z)
                a = mis_count(F) if len(F) else 1
                b = mis_count(R)
                assert b <= 2 * a
                assert greedy_marginal(distribution, y) < Fraction(1, 3)
                assert Fraction(a, a + b) >= Fraction(1, 3)
                continue

            summary["single_leaf"] += 1
            assert leaves == [x]
            F = T.copy()
            F.remove_nodes_from({x, y, z})
            for A in maximal_independent_sets(F):
                dominates_z = any(w in A for w in T.neighbors(z) if w != y)
                I_y = frozenset(set(A) | {y})
                if dominates_z:
                    I_x = frozenset(set(A) | {x})
                    assert distribution[I_y] > distribution[I_x]
                else:
                    I_x = frozenset(set(A) | {x, z})
                    assert distribution[I_x] > distribution[I_y]
                summary["paired_sets"] += 1

    return summary


if __name__ == "__main__":
    print(verify_stage3_local_certificates(11))
