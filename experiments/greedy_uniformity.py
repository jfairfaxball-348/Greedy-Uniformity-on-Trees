from __future__ import annotations

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
import math

import networkx as nx


def greedy_output(G: nx.Graph, order):
    chosen = set()
    for v in order:
        if all(u not in chosen for u in G.neighbors(v)):
            chosen.add(v)
    return frozenset(chosen)


def brute_force_distribution(G: nx.Graph):
    nodes = tuple(G.nodes())
    counts = Counter(greedy_output(G, p) for p in permutations(nodes))
    den = math.factorial(len(nodes))
    return {I: Fraction(c, den) for I, c in counts.items()}


def _adj_tuple(G: nx.Graph):
    nodes = tuple(sorted(G.nodes()))
    idx = {v: i for i, v in enumerate(nodes)}
    masks = []
    for v in nodes:
        m = 0
        for u in G.neighbors(v):
            m |= 1 << idx[u]
        masks.append(m)
    return tuple(masks)


@lru_cache(maxsize=None)
def _recursive_distribution_masks(adj: tuple[int, ...], active: int):
    if active == 0:
        return {0: Fraction(1)}
    n = active.bit_count()
    out = {}
    x = active
    while x:
        bit = x & -x
        v = bit.bit_length() - 1
        remaining = active & ~bit & ~adj[v]
        sub = _recursive_distribution_masks(adj, remaining)
        for mask, p in sub.items():
            out[mask | bit] = out.get(mask | bit, Fraction(0)) + Fraction(1, n) * p
        x ^= bit
    return out


def recursive_distribution(G: nx.Graph):
    H = nx.convert_node_labels_to_integers(G, ordering="sorted")
    adj = _adj_tuple(H)
    active = (1 << len(adj)) - 1
    d = _recursive_distribution_masks(adj, active)
    return {
        frozenset(i for i in range(len(adj)) if mask >> i & 1): p
        for mask, p in d.items()
    }


def maximal_independent_sets(G: nx.Graph):
    nodes = tuple(G.nodes())
    n = len(nodes)
    out = []
    for mask in range(1 << n):
        S = {nodes[i] for i in range(n) if mask >> i & 1}
        if any(u in S and v in S for u, v in G.edges()):
            continue
        if all(
            v in S or any(u in S for u in G.neighbors(v))
            for v in nodes
        ):
            out.append(frozenset(S))
    return out


def bias(G: nx.Graph, distribution=None):
    if distribution is None:
        distribution = recursive_distribution(G)
    mis = maximal_independent_sets(G)
    u = Fraction(1, len(mis))
    return sum(abs(distribution.get(I, Fraction(0)) - u) for I in mis) / 2


def mixed_spider(k: int, l: int):
    if k < 1 or l < 1:
        raise ValueError("k,l must be >=1")
    G = nx.Graph()
    c = 0
    nxt = 1
    G.add_node(c)
    for _ in range(k):
        u, v = nxt, nxt + 1
        nxt += 2
        G.add_edge(c, u)
        G.add_edge(u, v)
    for _ in range(l):
        G.add_edge(c, nxt)
        nxt += 1
    return G


def mixed_spider_formula(k: int, l: int):
    N = 2**k
    pc = sum(Fraction(math.comb(k, j), l + 2*j + 1) for j in range(k+1)) / N
    q = {
        j: Fraction(l + 2*j, N * (l + 2*j + 1))
        for j in range(k+1)
    }
    return pc, q


def mixed_spider_distribution_by_type(k: int, l: int):
    d = recursive_distribution(mixed_spider(k, l))
    inner = {1 + 2*i for i in range(k)}
    center_prob = Fraction(0)
    type_probs = {j: set() for j in range(k+1)}
    multiplicities = Counter()
    for I, p in d.items():
        if 0 in I:
            center_prob += p
        else:
            j = len(I & inner)
            type_probs[j].add(p)
            multiplicities[j] += 1
    return center_prob, type_probs, multiplicities


def family_bias_formula(k: int, l: int):
    N = 2**k
    pc, q = mixed_spider_formula(k, l)
    target = Fraction(1, N + 1)
    total = abs(pc - target)
    for j in range(k+1):
        total += math.comb(k, j) * abs(q[j] - target)
    return total / 2


def tuned_family_expectation_formula(k: int):
    """Exact Stage-3 expectation identity for l = 2^k - k."""
    if k < 1:
        raise ValueError("k must be >=1")
    N = 2**k
    A = N + 1
    first = Fraction(0)
    second = Fraction(0)
    for j in range(k + 1):
        w = 2*j - k
        weight = Fraction(math.comb(k, j), N)
        first += weight * Fraction(w*w, A*A*(A + w))
        second += weight * Fraction(abs(w), A*(A + w))
    return (first + second) / 2


def census(max_n=11):
    rows = []
    total = 0
    uniform = []
    counts = {}
    for n in range(1, max_n+1):
        trees = [nx.empty_graph(1)] if n == 1 else list(nx.generators.nonisomorphic_trees(n))
        counts[n] = len(trees)
        total += len(trees)
        vals = []
        for i, T in enumerate(trees):
            b = bias(T)
            vals.append(b)
            if b == 0:
                uniform.append((n, i))
        pos = [x for x in vals if x > 0]
        rows.append((n, len(trees), min(pos) if pos else None))
    return rows, total, uniform, counts


if __name__ == "__main__":
    expected_counts = {1:1, 2:1, 3:1, 4:2, 5:3, 6:6, 7:11, 8:23, 9:47, 10:106, 11:235}
    rows, total, uniform, counts = census(11)
    print("tree_counts=", counts)
    print("counts_match_expected=", counts == expected_counts)
    print("total=", total)
    print("uniform_cases=", uniform)
    print("min_positive_bias=", {n: str(m) if m is not None else None for n, _, m in rows})

    checked = 0
    for n in range(1, 8):
        trees = [nx.empty_graph(1)] if n == 1 else list(nx.generators.nonisomorphic_trees(n))
        for T in trees:
            assert brute_force_distribution(T) == recursive_distribution(T)
            checked += 1
    print("bruteforce_recursion_tree_cases=", checked)

    family_checked = []
    for k in range(1, 5):
        for l in range(1, 4):
            pc, type_probs, mult = mixed_spider_distribution_by_type(k, l)
            fpc, fq = mixed_spider_formula(k, l)
            assert pc == fpc
            for j in range(k+1):
                assert type_probs[j] == {fq[j]}
                assert mult[j] == math.comb(k, j)
            assert bias(mixed_spider(k, l)) == family_bias_formula(k, l)
            family_checked.append((k, l))
    print("family_formula_cases=", family_checked)

    for k in [2, 3, 4, 6, 10]:
        l = 2**k - k
        b = family_bias_formula(k, l)
        print("family", k, l, 2**k+k+1, str(b), float(b))
