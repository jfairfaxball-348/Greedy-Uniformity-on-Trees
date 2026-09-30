module

public import Mathlib

public section

/-!
# Greedy Uniformity on Trees — frozen A+B statement package

This is the Palomar Challenge surface for the frozen theorem package. It states
the two final Theorem A declarations and the seven final Theorem B checkpoints.
All project-specific notions appearing in those statements are defined here
directly, against Mathlib only. The Solution module imports the already verified
repository proof development.

The random greedy process scans a uniformly random permutation of the finite
vertex set, accepting a vertex precisely when no previously accepted neighbour
blocks it. The resulting maximal independent set is compared with the uniform
law on all maximal independent sets.

The novelty classification remains **plausibly new with bounded uncertainty**.
No claim of worldwide priority, global optimality, matching lower bounds, an
all-n extremal theorem, or any result beyond the declarations below is made.
-/

open scoped BigOperators

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite set is independent when it contains no adjacent pair. -/
def IsIndependent (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ ⦃u⦄, u ∈ I → ∀ ⦃v⦄, v ∈ I → ¬ G.Adj u v

/-- Maximal independence on an induced vertex set, expressed by independence and domination. -/
def IsMaximalIndependentOn (G : SimpleGraph V) (S I : Finset V) : Prop :=
  I ⊆ S ∧ IsIndependent G I ∧
    ∀ ⦃w⦄, w ∈ S → w ∉ I → ∃ u ∈ I, G.Adj u w

/-- A maximal independent set of the whole finite graph. -/
def IsMaximalIndependent (G : SimpleGraph V) (I : Finset V) : Prop :=
  IsMaximalIndependentOn G Finset.univ I

/-- The finite set of all maximal independent sets of a finite graph. -/
noncomputable def maximalIndependentSets (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (IsMaximalIndependent G)

/-- One deterministic step of the greedy scan. -/
def greedyStep (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) (v : V) : Finset V :=
  if ∃ u ∈ I, G.Adj u v then I else insert v I

/-- Greedy scan from an already selected accumulator. -/
def greedyScan (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V → List V → Finset V
  | I, [] => I
  | I, v :: l => greedyScan G (greedyStep G I v) l

/-- Greedy output for a concrete scan list. -/
def greedyList (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V) : Finset V :=
  greedyScan G ∅ l

/-- The finite sample space of all vertex scan orders. -/
noncomputable def vertexOrders : Finset (List V) := by
  classical
  exact (Finset.univ.toList.permutations).toFinset

/-- Actual deterministic greedy output associated to a scan order. -/
noncomputable def greedyOutput (G : SimpleGraph V) (l : List V) : Finset V := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  exact greedyList G l

/-- The exact permutation fibre of a target greedy output. -/
noncomputable def fibre (G : SimpleGraph V) (I : Finset V) : Finset (List V) := by
  classical
  exact vertexOrders.filter fun l => greedyOutput G l = I

/-- Cardinality of the exact permutation fibre of a target output. -/
noncomputable def fibreCount (G : SimpleGraph V) (I : Finset V) : ℕ :=
  (fibre G I).card

/-- Exact rational greedy output probability of a target set. -/
noncomputable def greedyProb (G : SimpleGraph V) (I : Finset V) : ℚ :=
  (fibreCount G I : ℚ) / ((vertexOrders (V := V)).card : ℚ)

/-- Exact rational uniform probability on maximal independent sets. -/
noncomputable def uniformProb (G : SimpleGraph V) (I : Finset V) : ℚ := by
  classical
  exact if IsMaximalIndependent G I then
    1 / ((maximalIndependentSets G).card : ℚ)
  else 0

/-- Equality of the complete greedy output law with the uniform law on maximal independent sets. -/
def GreedyLawEqUniform (G : SimpleGraph V) : Prop :=
  ∀ I : Finset V, greedyProb G I = uniformProb G I

/-- Total-variation distance from the uniform maximal-independent-set law. -/
noncomputable def bias (G : SimpleGraph V) : ℚ :=
  (1 / 2 : ℚ) *
    ∑ I ∈ maximalIndependentSets G,
      |greedyProb G I - 1 / ((maximalIndependentSets G).card : ℚ)|

/-- The graph-isomorphism formulation of the two exceptional finite trees. -/
def IsK1OrK2 (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g (⊤ : SimpleGraph (Fin 1))) ∨
    Nonempty (G ≃g (⊤ : SimpleGraph (Fin 2)))

/-- Frozen Theorem A: on a finite nonempty tree, the greedy law is uniform iff the tree is K1 or K2. -/
theorem tree_greedyLawEqUniform_iff_isK1OrK2
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree) :
    GreedyLawEqUniform G ↔ IsK1OrK2 G := by
  sorry

/-- Frozen Theorem A, equivalent zero-bias form. -/
theorem tree_bias_eq_zero_iff_isK1OrK2
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree) :
    bias G = 0 ↔ IsK1OrK2 G := by
  sorry

/-- Vertices of the mixed spider T_{k,l}: one centre, k length-two arms, and l direct leaves. -/
inductive MixedSpiderVertex (k l : ℕ)
  | center
  | inner (i : Fin k)
  | outer (i : Fin k)
  | leaf (r : Fin l)
  deriving DecidableEq, Fintype

/-- Oriented generating relation for the mixed spider; SimpleGraph.fromRel symmetrizes it. -/
def mixedSpiderRel {k l : ℕ} :
    MixedSpiderVertex k l → MixedSpiderVertex k l → Prop
  | .center, .inner _ => True
  | .inner i, .outer j => i = j
  | .center, .leaf _ => True
  | _, _ => False

/-- The mixed spider T_{k,l}. -/
def mixedSpider (k l : ℕ) : SimpleGraph (MixedSpiderVertex k l) :=
  SimpleGraph.fromRel mixedSpiderRel

open MixedSpiderVertex

/-- The unique centre-containing maximal independent-set candidate. -/
noncomputable def mixedSpiderCenterSet (k l : ℕ) :
    Finset (MixedSpiderVertex k l) := by
  classical
  exact Finset.univ.filter fun v =>
    match v with
    | .center => True
    | .outer _ => True
    | _ => False

/-- The non-centre candidate determined by the arm subset S. -/
noncomputable def mixedSpiderNoncenterSet
    {k l : ℕ} (S : Finset (Fin k)) : Finset (MixedSpiderVertex k l) := by
  classical
  exact Finset.univ.filter fun v =>
    match v with
    | .center => False
    | .inner i => i ∈ S
    | .outer i => i ∉ S
    | .leaf _ => True

/-- N=2^k, the number of non-centre arm patterns. -/
def mixedSpiderN (k : ℕ) : ℕ := 2 ^ k

/-- Denominator l+2j+1 in the exact mixed-spider law. -/
def mixedSpiderDenom (l j : ℕ) : ℕ := l + 2 * j + 1

/-- Exact probability formula for the centre-containing maximal independent set. -/
noncomputable def mixedSpiderCenterFormula (k l : ℕ) : ℚ :=
  (1 / (mixedSpiderN k : ℚ)) *
    ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℚ) / (mixedSpiderDenom l j : ℚ)

/-- Exact probability formula for a non-centre set with j inner vertices. -/
noncomputable def mixedSpiderNoncenterFormula (k l j : ℕ) : ℚ :=
  (1 / (mixedSpiderN k : ℚ)) *
    (1 - 1 / (mixedSpiderDenom l j : ℚ))

/-- Frozen B1: T_{k,l}, for l>0, has exactly 2^k+1 maximal independent sets. -/
theorem mixedSpider_maximalIndependentSets_card
    {k l : ℕ} (hl : 0 < l) :
    (maximalIndependentSets (mixedSpider k l)).card = 2 ^ k + 1 := by
  sorry

/-- Frozen B2 centre formula. -/
theorem greedyProb_mixedSpiderCenter
    {k l : ℕ} :
    greedyProb (mixedSpider k l) (mixedSpiderCenterSet k l) =
      mixedSpiderCenterFormula k l := by
  sorry

/-- Frozen B2 non-centre formula. -/
theorem greedyProb_mixedSpiderNoncenter
    {k l : ℕ} (hl : 0 < l) (S : Finset (Fin k)) :
    greedyProb (mixedSpider k l)
        (mixedSpiderNoncenterSet (l := l) S) =
      mixedSpiderNoncenterFormula k l S.card := by
  sorry

/-- Tuned leaf count l=2^k-k. -/
def mixedSpiderTunedL (k : ℕ) : ℕ := 2 ^ k - k

/-- A=2^k+1 in the tuned expectation formula. -/
def mixedSpiderA (k : ℕ) : ℚ := (2 ^ k : ℚ) + 1

/-- W=2j-k in the tuned binomial expectation. -/
def mixedSpiderW (k j : ℕ) : ℚ := 2 * (j : ℚ) - (k : ℚ)

/-- Finite exact expectation under J distributed as Bin(k,1/2). -/
noncomputable def binomialAverageQ (k : ℕ) (f : ℕ → ℚ) : ℚ :=
  (1 / (2 ^ k : ℚ)) *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * f j

/-- Exact tuned expression used in Frozen B3. -/
noncomputable def mixedSpiderTunedExpectation (k : ℕ) : ℚ :=
  (1 / 2 : ℚ) *
    (binomialAverageQ k
        (fun j =>
          mixedSpiderW k j ^ 2 /
            (mixedSpiderA k ^ 2 *
              (mixedSpiderA k + mixedSpiderW k j))) +
      binomialAverageQ k
        (fun j =>
          |mixedSpiderW k j| /
            (mixedSpiderA k *
              (mixedSpiderA k + mixedSpiderW k j))))

/-- Frozen B3 exact expectation identity. -/
theorem bias_mixedSpider_tuned_eq_expectation
    {k : ℕ} (hk : 0 < k) :
    bias (mixedSpider k (mixedSpiderTunedL k)) =
      mixedSpiderTunedExpectation k := by
  sorry

/-- Frozen B3 positive-bias assertion. -/
theorem bias_mixedSpider_tuned_pos
    {k : ℕ} (hk : 0 < k) :
    0 < bias (mixedSpider k (mixedSpiderTunedL k)) := by
  sorry

/-- Frozen B3 asymptotic conclusion b(T_k)=O(sqrt(k)/4^k). -/
theorem bias_mixedSpider_tuned_isBigO :
    (fun k : ℕ =>
      ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ)) =O[Filter.atTop]
      (fun k : ℕ => Real.sqrt (k : ℝ) / (4 ^ k : ℝ)) := by
  sorry

/-- Number of vertices in the tuned mixed-spider family. -/
def mixedSpiderTunedOrder (k : ℕ) : ℕ :=
  2 ^ k + k + 1

/-- Frozen B3 order-scale reformulation along n_k=2^k+k+1. -/
theorem bias_mixedSpider_tuned_isBigO_sqrt_log_order_div_order_sq :
    (fun k : ℕ =>
      ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ)) =O[Filter.atTop]
      (fun k : ℕ =>
        Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
          (mixedSpiderTunedOrder k : ℝ) ^ 2) := by
  sorry

end GreedyUniformity
