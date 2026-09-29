import Mathlib

open scoped BigOperators

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite set is independent when it contains no adjacent pair. -/
def IsIndependent (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ ⦃u⦄, u ∈ I → ∀ ⦃v⦄, v ∈ I → ¬ G.Adj u v

/-- Maximal independent set on an induced vertex set `S`, expressed by independence plus domination. -/
def IsMaximalIndependentOn (G : SimpleGraph V) (S I : Finset V) : Prop :=
  I ⊆ S ∧ IsIndependent G I ∧
    ∀ ⦃w⦄, w ∈ S → w ∉ I → ∃ u ∈ I, G.Adj u w

/-- Maximal independent set of the whole finite graph. -/
def IsMaximalIndependent (G : SimpleGraph V) (I : Finset V) : Prop :=
  IsMaximalIndependentOn G Finset.univ I

noncomputable def maximalIndependentSets (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (IsMaximalIndependent G)

/-- One deterministic greedy scan step. -/
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

/-- A list is a complete vertex order precisely when it permutes the full vertex list. -/
def IsVertexOrder (l : List V) : Prop :=
  l.Perm Finset.univ.toList

/-- Actual deterministic greedy output associated to a scan order. -/
noncomputable def greedyOutput (G : SimpleGraph V) (l : List V) : Finset V := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  exact greedyList G l

/-- `u` appears strictly before `v` in a list. -/
def Precedes (l : List V) (u v : V) : Prop :=
  ∃ a b c : List V, l = a ++ u :: b ++ v :: c

/-- Exact finite priority certificate for a maximal independent set. -/
def PriorityCertificate (G : SimpleGraph V) (I : Finset V) (l : List V) : Prop :=
  IsVertexOrder l ∧ IsMaximalIndependent G I ∧
    ∀ ⦃w⦄, w ∉ I → ∃ u ∈ I, G.Adj u w ∧ Precedes l u w

/-- The exact permutation fibre of a target greedy output. -/
noncomputable def fibre (G : SimpleGraph V) (I : Finset V) : Finset (List V) := by
  classical
  exact vertexOrders.filter fun l => greedyOutput G l = I

noncomputable def fibreCount (G : SimpleGraph V) (I : Finset V) : ℕ :=
  (fibre G I).card

/-- Exact-uniformity in the finite permutation-fibre formulation. -/
def UniformFibres (G : SimpleGraph V) : Prop :=
  ∀ ⦃I J : Finset V⦄,
    IsMaximalIndependent G I →
    IsMaximalIndependent G J →
    fibreCount G I = fibreCount G J

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

end GreedyUniformity
