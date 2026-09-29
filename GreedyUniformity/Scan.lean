import GreedyUniformity.Model

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

@[simp]
theorem rank_vertexAt (π : Equiv.Perm V) (i : Fin (Fintype.card V)) :
    rank π (vertexAt π i) = i := by
  simp [rank, vertexAt, baseEquiv]

@[simp]
theorem vertexAt_rank (π : Equiv.Perm V) (v : V) :
    vertexAt π (rank π v) = v := by
  simp [rank, vertexAt, baseEquiv]

theorem rank_injective (π : Equiv.Perm V) :
    Function.Injective (rank π) := by
  intro a b h
  have := congrArg (vertexAt π) h
  simpa using this

theorem subset_greedyStep (I : Finset V) (v : V) :
    I ⊆ greedyStep G I v := by
  classical
  simp only [greedyStep]
  split
  · exact fun _ h => h
  · exact Finset.subset_insert v I

theorem greedyStep_eq_self_of_neighbor {I : Finset V} {v : V}
    (h : ∃ u ∈ I, G.Adj u v) :
    greedyStep G I v = I := by
  classical
  simp [greedyStep, h]

theorem greedyStep_eq_insert_of_no_neighbor {I : Finset V} {v : V}
    (h : ¬ ∃ u ∈ I, G.Adj u v) :
    greedyStep G I v = insert v I := by
  classical
  simp [greedyStep, h]

theorem mem_greedyStep_iff {I : Finset V} {v w : V} :
    w ∈ greedyStep G I v ↔
      w ∈ I ∨ (w = v ∧ ¬ ∃ u ∈ I, G.Adj u v) := by
  classical
  by_cases h : ∃ u ∈ I, G.Adj u v
  · simp [greedyStep, h]
  · simp [greedyStep, h, eq_comm]

theorem greedyPrefix_step (π : Equiv.Perm V) {n : ℕ}
    (hn : n < Fintype.card V) :
    greedyPrefix G π (n + 1) =
      greedyStep G (greedyPrefix G π n) (vertexAt π ⟨n, hn⟩) := by
  simp [greedyPrefix, hn]

end GreedyUniformity
