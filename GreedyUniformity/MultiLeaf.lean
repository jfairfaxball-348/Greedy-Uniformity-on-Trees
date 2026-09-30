module

public import GreedyUniformity.Marginal
public import GreedyUniformity.OrderCount

public section

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

section MultiLeaf

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem selected_order_precedes_pendantLeaf
    {y z x : V}
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx : x ∈ pendantLeaves G y z)
    {l : List V} (hl : IsVertexOrder l)
    (hyout : y ∈ greedyOutput G l) :
    Precedes l y x := by
  have hmax := greedyOutput_maximal G hl
  have hxout : x ∉ greedyOutput G l := by
    intro hxout
    exact hmax.2.1 hyout hxout ((mem_pendantLeaves_iff G).1 hx |>.2)
  have hcert := greedyOutput_priorityCertificate G hl
  rcases hcert.2.2 hxout with ⟨u, hu, hux, hprec⟩
  have huy : u = y := by
    apply degree_one_adj_unique G (pendantLeaves_degree_one G hleaf hx)
    · exact G.adj_symm ((mem_pendantLeaves_iff G).1 hx |>.2)
    · exact G.adj_symm hux
  simpa [huy] using hprec

theorem ordersSelecting_subset_firstOfThree_of_pendantLeaves
    {y z x₁ x₂ : V}
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx₁ : x₁ ∈ pendantLeaves G y z)
    (hx₂ : x₂ ∈ pendantLeaves G y z) :
    ordersSelecting G y ⊆ firstOfThreeOrders y x₁ x₂ := by
  intro l hl
  have hsel := Finset.mem_filter.mp hl
  have horder : IsVertexOrder l := (mem_vertexOrders_iff).1 hsel.1
  have hp₁ := selected_order_precedes_pendantLeaf G hleaf hx₁ horder hsel.2
  have hp₂ := selected_order_precedes_pendantLeaf G hleaf hx₂ horder hsel.2
  apply (mem_firstOfThreeOrders_iff).2
  exact ⟨horder,
    precedes_idxOf_lt (isVertexOrder_nodup horder) hp₁,
    precedes_idxOf_lt (isVertexOrder_nodup horder) hp₂⟩

theorem exists_firstOfThree_not_selecting
    {y z x₁ x₂ : V} (hyz : G.Adj y z)
    (hx₁ : x₁ ∈ pendantLeaves G y z)
    (hx₂ : x₂ ∈ pendantLeaves G y z) :
    ∃ l ∈ firstOfThreeOrders y x₁ x₂, l ∉ ordersSelecting G y := by
  classical
  let R : Finset V := (Finset.univ.erase z).erase y
  let l : List V := z :: y :: R.toList
  have hzy : z ≠ y := hyz.ne.symm
  have hx₁z : x₁ ≠ z := (mem_pendantLeaves_iff G).1 hx₁ |>.1
  have hx₂z : x₂ ≠ z := (mem_pendantLeaves_iff G).1 hx₂ |>.1
  have hyx₁ : y ≠ x₁ := ((mem_pendantLeaves_iff G).1 hx₁ |>.2).ne
  have hyx₂ : y ≠ x₂ := ((mem_pendantLeaves_iff G).1 hx₂ |>.2).ne
  have hx₁y : x₁ ≠ y := hyx₁.symm
  have hx₂y : x₂ ≠ y := hyx₂.symm
  have hRnodup : R.toList.Nodup := Finset.nodup_toList _
  have hzR : z ∉ R.toList := by
    simp [R]
  have hyR : y ∉ R.toList := by
    simp [R]
  have hnodup : l.Nodup := by
    simp [l, hzy, hzR, hyR, hRnodup]
  have horder : IsVertexOrder l := by
    unfold IsVertexOrder
    apply (List.perm_ext_iff_of_nodup hnodup (Finset.nodup_toList _)).2
    intro w
    simp [l, R]
    tauto
  have hx₁R : x₁ ∈ R.toList := by
    simp [R, hx₁z, hx₁y]
  have hx₂R : x₂ ∈ R.toList := by
    simp [R, hx₂z, hx₂y]
  have hp₁ : Precedes l y x₁ := by
    change Precedes ([z, y] ++ R.toList) y x₁
    exact precedes_append_of_mem (by simp) hx₁R
  have hp₂ : Precedes l y x₂ := by
    change Precedes ([z, y] ++ R.toList) y x₂
    exact precedes_append_of_mem (by simp) hx₂R
  have hfirst : l ∈ firstOfThreeOrders y x₁ x₂ := by
    apply (mem_firstOfThreeOrders_iff).2
    exact ⟨horder,
      precedes_idxOf_lt hnodup hp₁,
      precedes_idxOf_lt hnodup hp₂⟩
  have hzout : z ∈ greedyOutput G l := by
    classical
    letI : DecidableRel G.Adj := Classical.decRel _
    have hzstep : z ∈ greedyStep G (∅ : Finset V) z := by
      simp [greedyStep]
    have hzlist : z ∈ greedyList G l := by
      change z ∈ greedyScan G ∅ (z :: y :: R.toList)
      simp only [greedyScan]
      exact greedyScan_subset G (greedyStep G ∅ z) (y :: R.toList) hzstep
    simpa [greedyOutput] using hzlist
  have hynot : y ∉ greedyOutput G l := by
    intro hyout
    exact (greedyOutput_maximal G horder).2.1 hzout hyout (G.adj_symm hyz)
  have hnsel : l ∉ ordersSelecting G y := by
    intro h
    exact hynot (Finset.mem_filter.mp h).2
  exact ⟨l, hfirst, hnsel⟩

theorem ordersSelecting_ssubset_firstOfThree_of_two_pendantLeaves
    {y z x₁ x₂ : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx₁ : x₁ ∈ pendantLeaves G y z)
    (hx₂ : x₂ ∈ pendantLeaves G y z) :
    ordersSelecting G y ⊂ firstOfThreeOrders y x₁ x₂ := by
  have hsub :=
    ordersSelecting_subset_firstOfThree_of_pendantLeaves G hleaf hx₁ hx₂
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsub, ?_⟩
  intro heq
  rcases exists_firstOfThree_not_selecting G hyz hx₁ hx₂ with
    ⟨l, hlFirst, hlNot⟩
  exact hlNot (heq ▸ hlFirst)

theorem three_mul_ordersSelecting_lt_vertexOrders_of_two_pendantLeaves
    {y z x₁ x₂ : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx₁ : x₁ ∈ pendantLeaves G y z)
    (hx₂ : x₂ ∈ pendantLeaves G y z)
    (hxne : x₁ ≠ x₂) :
    3 * (ordersSelecting G y).card < (vertexOrders (V := V)).card := by
  have hyx₁ : y ≠ x₁ := ((mem_pendantLeaves_iff G).1 hx₁ |>.2).ne
  have hyx₂ : y ≠ x₂ := ((mem_pendantLeaves_iff G).1 hx₂ |>.2).ne
  have hlt :
      (ordersSelecting G y).card <
        (firstOfThreeOrders y x₁ x₂).card :=
    Finset.card_lt_card
      (ordersSelecting_ssubset_firstOfThree_of_two_pendantLeaves
        G hyz hleaf hx₁ hx₂)
  have htriple :=
    three_mul_firstOfThreeOrders_card hyx₁ hyx₂ hxne
  calc
    3 * (ordersSelecting G y).card <
        3 * (firstOfThreeOrders y x₁ x₂).card := by
      omega
    _ = (vertexOrders (V := V)).card := htriple

theorem not_uniformFibres_of_two_pendantLeaves
    {y z x₁ x₂ : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx₁ : x₁ ∈ pendantLeaves G y z)
    (hx₂ : x₂ ∈ pendantLeaves G y z)
    (hxne : x₁ ≠ x₂) :
    ¬ UniformFibres G := by
  intro hU
  have hL : (pendantLeaves G y z).Nonempty := ⟨x₁, hx₁⟩
  have hcount :=
    maximalIndependentSetsExcluding_card_le_two_mul_containing
      G hyz hleaf hL
  have hlower :=
    uniformFibres_implies_vertexOrders_le_three_mul_ordersSelecting
      G y hcount hU
  have hupper :=
    three_mul_ordersSelecting_lt_vertexOrders_of_two_pendantLeaves
      G hyz hleaf hx₁ hx₂ hxne
  omega

end MultiLeaf

end GreedyUniformity
