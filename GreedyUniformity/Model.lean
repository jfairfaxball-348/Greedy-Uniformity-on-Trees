import Mathlib

open scoped BigOperators

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite set is independent when it contains no adjacent pair. -/
def IsIndependent (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ ⦃u⦄, u ∈ I → ∀ ⦃v⦄, v ∈ I → ¬ G.Adj u v

/-- Maximal independent set on an induced vertex set `S`. -/
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
noncomputable def greedyStep (G : SimpleGraph V) (I : Finset V) (v : V) : Finset V := by
  classical
  exact if ∃ u ∈ I, G.Adj u v then I else insert v I

/-- Canonical enumeration used only to turn a permutation into a scan order. -/
noncomputable def baseEquiv : V ≃ Fin (Fintype.card V) :=
  Fintype.equivFin V

/-- Rank of a vertex in the scan order attached to `π`. -/
noncomputable def rank (π : Equiv.Perm V) (v : V) : Fin (Fintype.card V) :=
  baseEquiv (V := V) (π.symm v)

def Precedes (π : Equiv.Perm V) (u v : V) : Prop :=
  rank π u < rank π v

/-- Vertex appearing at a specified rank in `π`. -/
noncomputable def vertexAt (π : Equiv.Perm V) (i : Fin (Fintype.card V)) : V :=
  π ((baseEquiv (V := V)).symm i)

/--
The first `n` steps of the one-pass greedy scan.  Vertices are scanned in
the order encoded by `π`; once selected, vertices are never removed.
-/
noncomputable def greedyPrefix (G : SimpleGraph V) (π : Equiv.Perm V) :
    ℕ → Finset V
  | 0 => ∅
  | n + 1 =>
      if h : n < Fintype.card V then
        greedyStep G (greedyPrefix G π n) (vertexAt π ⟨n, h⟩)
      else
        greedyPrefix G π n

/-- Deterministic greedy maximal-independent-set output of a permutation. -/
noncomputable def greedyOutput (G : SimpleGraph V) (π : Equiv.Perm V) : Finset V :=
  greedyPrefix G π (Fintype.card V)

/--
Exact finite priority certificate: a maximal independent set is the output
iff every outside vertex has an earlier selected neighbour.
-/
def PriorityCertificate (G : SimpleGraph V) (I : Finset V) (π : Equiv.Perm V) : Prop :=
  IsMaximalIndependent G I ∧
    ∀ ⦃w⦄, w ∉ I → ∃ u ∈ I, G.Adj u w ∧ Precedes π u w

/-- The literal permutation fibre of a terminal set. -/
noncomputable def fibre (G : SimpleGraph V) (I : Finset V) :
    Finset (Equiv.Perm V) := by
  classical
  exact Finset.univ.filter (fun π => greedyOutput G π = I)

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
  (fibreCount G I : ℚ) / Nat.factorial (Fintype.card V)

/-- Exact rational uniform probability on maximal independent sets. -/
noncomputable def uniformProb (G : SimpleGraph V) (I : Finset V) : ℚ := by
  classical
  exact if IsMaximalIndependent G I then
    1 / ((maximalIndependentSets G).card : ℚ)
  else 0

/-- Pointwise equality of the greedy terminal law and the uniform MIS law. -/
def GreedyLawEqUniform (G : SimpleGraph V) : Prop :=
  ∀ I : Finset V, greedyProb G I = uniformProb G I

end GreedyUniformity
