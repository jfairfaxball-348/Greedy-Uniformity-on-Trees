module

public import GreedyUniformity.Model

@[expose] public section

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

section Greedy

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem greedyStep_subset (I : Finset V) (v : V) : I ⊆ greedyStep G I v := by
  intro x hx
  unfold greedyStep
  split
  · exact hx
  · exact Finset.mem_insert_of_mem hx

theorem greedyScan_subset (I : Finset V) (l : List V) : I ⊆ greedyScan G I l := by
  induction l generalizing I with
  | nil =>
      intro x hx
      exact hx
  | cons v l ih =>
      intro x hx
      exact ih (greedyStep G I v) (greedyStep_subset G I v hx)

theorem greedyStep_independent {I : Finset V} {v : V}
    (hI : IsIndependent G I) : IsIndependent G (greedyStep G I v) := by
  unfold greedyStep
  split_ifs with h
  · exact hI
  · intro a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact G.irrefl hab
      · exact h ⟨b, hb, G.adj_symm hab⟩
    · rcases hb with rfl | hb
      · exact h ⟨a, ha, hab⟩
      · exact hI ha hb hab

theorem greedyScan_independent {I : Finset V} (l : List V)
    (hI : IsIndependent G I) : IsIndependent G (greedyScan G I l) := by
  induction l generalizing I with
  | nil => exact hI
  | cons v l ih =>
      exact ih (greedyStep_independent G hI)

theorem greedyScan_mem_or_adj (I : Finset V) (l : List V) {w : V}
    (hw : w ∈ l) :
    w ∈ greedyScan G I l ∨ ∃ u ∈ greedyScan G I l, G.Adj u w := by
  induction l generalizing I with
  | nil => simp at hw
  | cons v l ih =>
      simp only [List.mem_cons] at hw
      rcases hw with hw | hw
      · subst w
        simp only [greedyScan]
        unfold greedyStep
        split_ifs with h
        · right
          rcases h with ⟨u, hu, huv⟩
          exact ⟨u, greedyScan_subset G I l hu, huv⟩
        · left
          exact greedyScan_subset G (insert v I) l (Finset.mem_insert_self v I)
      · simpa only [greedyScan] using
          (ih (I := greedyStep G I v) hw)

theorem greedyList_independent (l : List V) :
    IsIndependent G (greedyList G l) := by
  apply greedyScan_independent G
  intro a ha
  simp at ha

theorem greedyList_maximal_of_complete (l : List V)
    (hall : ∀ v : V, v ∈ l) :
    IsMaximalIndependent G (greedyList G l) := by
  refine ⟨by simp, greedyList_independent G l, ?_⟩
  intro w _ hw
  rcases greedyScan_mem_or_adj G (∅ : Finset V) l (hall w) with hmem | ⟨u, hu, hadj⟩
  · exact (hw hmem).elim
  · exact ⟨u, hu, hadj⟩

end Greedy

theorem isVertexOrder_complete {l : List V} (hl : IsVertexOrder l) :
    ∀ v : V, v ∈ l := by
  intro v
  have hv : v ∈ (Finset.univ.toList : List V) := by simp
  exact (hl.mem_iff).2 hv

theorem greedyOutput_maximal (G : SimpleGraph V) {l : List V}
    (hl : IsVertexOrder l) :
    IsMaximalIndependent G (greedyOutput G l) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  exact greedyList_maximal_of_complete G l (isVertexOrder_complete hl)

theorem mem_vertexOrders_iff {l : List V} :
    l ∈ vertexOrders (V := V) ↔ IsVertexOrder l := by
  classical
  unfold vertexOrders IsVertexOrder
  simp

theorem fibre_mem_iff (G : SimpleGraph V) (I : Finset V) (l : List V) :
    l ∈ fibre G I ↔ IsVertexOrder l ∧ greedyOutput G l = I := by
  classical
  simp [fibre, mem_vertexOrders_iff]

theorem fibreCount_eq_card_filter (G : SimpleGraph V) (I : Finset V) :
    fibreCount G I =
      ((vertexOrders (V := V)).filter fun l => greedyOutput G l = I).card := by
  rfl

theorem fibre_eq_empty_of_not_maximal (G : SimpleGraph V) {I : Finset V}
    (hI : ¬ IsMaximalIndependent G I) : fibre G I = ∅ := by
  classical
  ext l
  constructor
  · intro hl
    have horder : IsVertexOrder l := (fibre_mem_iff G I l).1 hl |>.1
    have hout : greedyOutput G l = I := (fibre_mem_iff G I l).1 hl |>.2
    exact False.elim (hI (hout ▸ greedyOutput_maximal G horder))
  · intro hl
    exact (by simpa using hl : False).elim

theorem fibreCount_eq_zero_of_not_maximal (G : SimpleGraph V) {I : Finset V}
    (hI : ¬ IsMaximalIndependent G I) : fibreCount G I = 0 := by
  simp [fibreCount, fibre_eq_empty_of_not_maximal G hI]

end GreedyUniformity
