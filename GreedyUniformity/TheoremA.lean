module

public import GreedyUniformity.TreeA

public section

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- On at most two vertices, every maximal-independent-set fibre has the same size. -/
theorem uniformFibres_of_card_le_two
    (G : SimpleGraph V) (hcard : Fintype.card V ≤ 2) :
    UniformFibres G := by
  classical
  have horders : (vertexOrders (V := V)).card ≤ 2 := by
    rw [vertexOrders_card]
    have hcases :
        Fintype.card V = 0 ∨ Fintype.card V = 1 ∨ Fintype.card V = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · simp [h0]
    · simp [h1]
    · simp [h2]
  intro I J hI hJ
  by_cases hIJ : I = J
  · simpa [hIJ]
  have hposI := fibreCount_pos_of_maximal G hI
  have hposJ := fibreCount_pos_of_maximal G hJ
  have hdis : Disjoint (fibre G I) (fibre G J) := by
    rw [Finset.disjoint_left]
    intro l hlI hlJ
    have houtI := (fibre_mem_iff G I l).1 hlI |>.2
    have houtJ := (fibre_mem_iff G J l).1 hlJ |>.2
    exact hIJ (houtI.symm.trans houtJ)
  have hunion :
      fibre G I ∪ fibre G J ⊆ vertexOrders (V := V) := by
    intro l hl
    rcases Finset.mem_union.mp hl with hlI | hlJ
    · exact (mem_vertexOrders_iff).2 ((fibre_mem_iff G I l).1 hlI |>.1)
    · exact (mem_vertexOrders_iff).2 ((fibre_mem_iff G J l).1 hlJ |>.1)
  have hle := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdis] at hle
  have hsum :
      fibreCount G I + fibreCount G J ≤ 2 := by
    exact le_trans (by simpa [fibreCount] using hle) horders
  omega

/-- A finite tree has uniform greedy fibres exactly when it has at most two vertices. -/
theorem tree_uniformFibres_iff_card_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree) :
    UniformFibres G ↔ Fintype.card V ≤ 2 := by
  constructor
  · intro hU
    by_contra hnot
    have hthree : 3 ≤ Fintype.card V := by omega
    exact tree_not_uniformFibres_of_three_le_card G hT hthree hU
  · exact uniformFibres_of_card_le_two G

/-- Cardinal form of the exact (K_1/K_2) obstruction for finite trees. -/
theorem tree_uniformFibres_iff_card_eq_one_or_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree) :
    UniformFibres G ↔ Fintype.card V = 1 ∨ Fintype.card V = 2 := by
  rw [tree_uniformFibres_iff_card_le_two G hT]
  letI : Nonempty V := hT.connected.nonempty
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  omega


/-- The exact graph-isomorphism formulation of the two exceptional trees. -/
def IsK1OrK2 (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g (⊤ : SimpleGraph (Fin 1))) ∨
    Nonempty (G ≃g (⊤ : SimpleGraph (Fin 2)))

theorem graph_eq_top_of_card_eq_one
    (G : SimpleGraph V) (hcard : Fintype.card V = 1) :
    G = ⊤ := by
  have hs : Subsingleton V :=
    (Fintype.card_le_one_iff_subsingleton).1 (by omega)
  letI : Subsingleton V := hs
  ext u v
  simp only [SimpleGraph.top_adj]
  constructor
  · intro huv
    exact huv.ne
  · intro huv
    exact (huv (Subsingleton.elim u v)).elim

theorem connected_graph_eq_top_of_card_eq_two
    (G : SimpleGraph V) (hconn : G.Connected)
    (hcard : Fintype.card V = 2) :
    G = ⊤ := by
  ext u v
  simp only [SimpleGraph.top_adj]
  constructor
  · intro huv
    exact huv.ne
  · intro huv
    obtain ⟨p, hp⟩ := hconn.exists_isPath u v
    have hlt : p.length < 2 := by
      simpa [hcard] using hp.length_lt
    have hne : p.length ≠ 0 := by
      intro hz
      apply huv
      exact SimpleGraph.Walk.exists_length_eq_zero_iff.1 ⟨p, hz⟩
    have hone : p.length = 1 := by omega
    exact SimpleGraph.Walk.exists_length_eq_one_iff.1 ⟨p, hone⟩

theorem tree_isK1OrK2_iff_card_eq_one_or_two
    (G : SimpleGraph V) (hT : G.IsTree) :
    IsK1OrK2 G ↔ Fintype.card V = 1 ∨ Fintype.card V = 2 := by
  constructor
  · intro hK
    rcases hK with hK1 | hK2
    · rcases hK1 with ⟨e⟩
      left
      simpa using SimpleGraph.Iso.card_eq e
    · rcases hK2 with ⟨e⟩
      right
      simpa using SimpleGraph.Iso.card_eq e
  · rintro (h1 | h2)
    · left
      let e : V ≃ Fin 1 := Fintype.equivFinOfCardEq h1
      have hG : G = ⊤ := graph_eq_top_of_card_eq_one G h1
      refine ⟨?_⟩
      rw [hG]
      exact SimpleGraph.Iso.completeGraph e
    · right
      let e : V ≃ Fin 2 := Fintype.equivFinOfCardEq h2
      have hG : G = ⊤ :=
        connected_graph_eq_top_of_card_eq_two G hT.connected h2
      refine ⟨?_⟩
      rw [hG]
      exact SimpleGraph.Iso.completeGraph e


/-- Frozen Theorem A, exact finite-law form.  For a finite tree, the greedy
terminal law is uniform exactly in the one-vertex and two-vertex cases
((K_1) and (K_2)). -/
theorem tree_greedyLawEqUniform_iff_card_eq_one_or_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree) :
    GreedyLawEqUniform G ↔
      Fintype.card V = 1 ∨ Fintype.card V = 2 := by
  rw [← uniformFibres_iff_greedyLawEqUniform G]
  exact tree_uniformFibres_iff_card_eq_one_or_two G hT

/-- Frozen Theorem A, zero-bias form. -/
theorem tree_bias_eq_zero_iff_card_eq_one_or_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree) :
    bias G = 0 ↔ Fintype.card V = 1 ∨ Fintype.card V = 2 := by
  rw [bias_eq_zero_iff_greedyLawEqUniform G]
  exact tree_greedyLawEqUniform_iff_card_eq_one_or_two G hT


/-- Frozen Theorem A in the repository's graph-isomorphism formulation. -/
theorem tree_greedyLawEqUniform_iff_isK1OrK2
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree) :
    GreedyLawEqUniform G ↔ IsK1OrK2 G := by
  rw [tree_greedyLawEqUniform_iff_card_eq_one_or_two G hT]
  exact (tree_isK1OrK2_iff_card_eq_one_or_two G hT).symm

/-- Frozen Theorem A in graph-isomorphism form, stated as zero bias. -/
theorem tree_bias_eq_zero_iff_isK1OrK2
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree) :
    bias G = 0 ↔ IsK1OrK2 G := by
  rw [tree_bias_eq_zero_iff_card_eq_one_or_two G hT]
  exact (tree_isK1OrK2_iff_card_eq_one_or_two G hT).symm

end GreedyUniformity
