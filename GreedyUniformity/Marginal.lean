import GreedyUniformity.Pendant

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def ordersSelecting (G : SimpleGraph V) (y : V) :
    Finset (List V) := by
  classical
  exact (vertexOrders (V := V)).filter fun l => y ∈ greedyOutput G l

theorem maximalIndependentSetsContaining_nonempty
    (G : SimpleGraph V) (y : V) :
    (maximalIndependentSetsContaining G y).Nonempty := by
  classical
  have hsingle : IsIndependent G ({y} : Finset V) := by
    intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact G.irrefl hab
  obtain ⟨I, hIM, hsub⟩ :=
    exists_maximalIndependentOn_superset G
      (S := (Finset.univ : Finset V)) (J := ({y} : Finset V))
      (by simp) hsingle
  refine ⟨I, (mem_maximalIndependentSetsContaining_iff G).2 ⟨hIM, ?_⟩⟩
  exact hsub (by simp)

theorem ordersSelecting_card_eq_sum_fibreCount
    (G : SimpleGraph V) (y : V) :
    (ordersSelecting G y).card =
      ∑ I ∈ maximalIndependentSetsContaining G y, fibreCount G I := by
  classical
  have hfilter :
      ((vertexOrders (V := V)).filter fun l =>
        greedyOutput G l ∈ maximalIndependentSetsContaining G y) =
        ordersSelecting G y := by
    ext l
    simp only [Finset.mem_filter, ordersSelecting]
    constructor
    · rintro ⟨hl, hout⟩
      exact ⟨hl, (mem_maximalIndependentSetsContaining_iff G).1 hout |>.2⟩
    · rintro ⟨hl, hy⟩
      have horder : IsVertexOrder l := (mem_vertexOrders_iff).1 hl
      exact ⟨hl, (mem_maximalIndependentSetsContaining_iff G).2
        ⟨greedyOutput_maximal G horder, hy⟩⟩
  have hsum :=
    Finset.sum_card_fiberwise_eq_card_filter
      (vertexOrders (V := V))
      (maximalIndependentSetsContaining G y)
      (greedyOutput G)
  calc
    (ordersSelecting G y).card =
        (((vertexOrders (V := V)).filter fun l =>
          greedyOutput G l ∈ maximalIndependentSetsContaining G y).card) := by
            rw [hfilter]
    _ = ∑ I ∈ maximalIndependentSetsContaining G y,
          (((vertexOrders (V := V)).filter fun l =>
            greedyOutput G l = I).card) := hsum.symm
    _ = ∑ I ∈ maximalIndependentSetsContaining G y, fibreCount G I := by
          rfl

theorem maximalIndependentSets_partition_card
    (G : SimpleGraph V) (y : V) :
    (maximalIndependentSetsContaining G y).card +
      (maximalIndependentSetsExcluding G y).card =
        (maximalIndependentSets G).card := by
  classical
  simpa [maximalIndependentSetsContaining, maximalIndependentSetsExcluding] using
    (Finset.card_filter_add_card_filter_not
      (s := maximalIndependentSets G) (p := fun I : Finset V => y ∈ I))

theorem uniformFibres_implies_vertexOrders_le_three_mul_ordersSelecting
    (G : SimpleGraph V) (y : V)
    (hcount :
      (maximalIndependentSetsExcluding G y).card ≤
        2 * (maximalIndependentSetsContaining G y).card)
    (hU : UniformFibres G) :
    (vertexOrders (V := V)).card ≤ 3 * (ordersSelecting G y).card := by
  classical
  obtain ⟨I0, hI0⟩ := maximalIndependentSetsContaining_nonempty G y
  let c : ℕ := fibreCount G I0
  have hI0max : IsMaximalIndependent G I0 :=
    (mem_maximalIndependentSetsContaining_iff G).1 hI0 |>.1
  have hsel :
      (ordersSelecting G y).card =
        (maximalIndependentSetsContaining G y).card * c := by
    rw [ordersSelecting_card_eq_sum_fibreCount]
    calc
      (∑ I ∈ maximalIndependentSetsContaining G y, fibreCount G I) =
          ∑ _I ∈ maximalIndependentSetsContaining G y, c := by
            apply Finset.sum_congr rfl
            intro I hI
            exact hU ((mem_maximalIndependentSetsContaining_iff G).1 hI |>.1) hI0max
      _ = (maximalIndependentSetsContaining G y).card * c := by
            simp
  have htot :
      (vertexOrders (V := V)).card =
        (maximalIndependentSets G).card * c := by
    rw [← sum_fibreCount_eq_vertexOrders_card G]
    calc
      (∑ I ∈ maximalIndependentSets G, fibreCount G I) =
          ∑ _I ∈ maximalIndependentSets G, c := by
            apply Finset.sum_congr rfl
            intro I hI
            exact hU ((mem_maximalIndependentSets_iff G).1 hI) hI0max
      _ = (maximalIndependentSets G).card * c := by
            simp
  have hpart := maximalIndependentSets_partition_card G y
  calc
    (vertexOrders (V := V)).card =
        (maximalIndependentSets G).card * c := htot
    _ = ((maximalIndependentSetsContaining G y).card +
          (maximalIndependentSetsExcluding G y).card) * c := by
          rw [hpart]
    _ ≤ ((maximalIndependentSetsContaining G y).card +
          2 * (maximalIndependentSetsContaining G y).card) * c := by
          exact Nat.mul_le_mul_right c
            (Nat.add_le_add_left hcount
              (maximalIndependentSetsContaining G y).card)
    _ = 3 * ((maximalIndependentSetsContaining G y).card * c) := by
          ring
    _ = 3 * (ordersSelecting G y).card := by
          rw [← hsel]

end GreedyUniformity
