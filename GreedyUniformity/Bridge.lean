import GreedyUniformity.Basic

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem isVertexOrder_nodup {l : List V} (hl : IsVertexOrder l) : l.Nodup := by
  exact (List.Perm.nodup_iff hl).2 (Finset.nodup_toList _)

theorem vertexOrders_card :
    (vertexOrders (V := V)).card = (Fintype.card V).factorial := by
  classical
  unfold vertexOrders
  rw [List.toFinset_card_of_nodup
    (List.nodup_permutations _ (Finset.nodup_toList _))]
  simpa using List.length_permutations (Finset.univ.toList : List V)

theorem vertexOrders_card_pos :
    0 < (vertexOrders (V := V)).card := by
  rw [vertexOrders_card]
  exact Nat.factorial_pos _

theorem precedes_mem_left {l : List V} {u v : V}
    (h : Precedes l u v) : u ∈ l := by
  rcases h with ⟨a, b, c, rfl⟩
  simp

theorem precedes_mem_right {l : List V} {u v : V}
    (h : Precedes l u v) : v ∈ l := by
  rcases h with ⟨a, b, c, rfl⟩
  simp

theorem precedes_idxOf_lt {l : List V} {u v : V}
    (hl : l.Nodup) (h : Precedes l u v) :
    l.idxOf u < l.idxOf v := by
  rcases h with ⟨a, b, c, rfl⟩
  let p : List V := a ++ u :: b
  have hnd : (p ++ v :: c).Nodup := by
    simpa [p, List.append_assoc] using hl
  have hu : u ∈ p := by
    simp [p]
  have hd : List.Disjoint p (v :: c) :=
    (List.nodup_append'.1 hnd).2.2
  have hvnot : v ∉ p := by
    intro hv
    have hne := (List.disjoint_iff_ne.mp hd) v hv v (by simp)
    exact hne rfl
  change (p ++ v :: c).idxOf u < (p ++ v :: c).idxOf v
  rw [List.idxOf_append_of_mem hu, List.idxOf_append_of_notMem hvnot]
  simpa using List.idxOf_lt_length_iff.mpr hu

theorem precedes_append_of_mem {a b : List V} {u v : V}
    (hu : u ∈ a) (hv : v ∈ b) :
    Precedes (a ++ b) u v := by
  rcases List.append_of_mem hu with ⟨a₁, a₂, rfl⟩
  rcases List.append_of_mem hv with ⟨b₁, b₂, rfl⟩
  refine ⟨a₁, a₂ ++ b₁, b₂, ?_⟩
  simp [List.append_assoc]

section Greedy

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem greedyStep_subset_insert (I : Finset V) (v : V) :
    greedyStep G I v ⊆ insert v I := by
  intro x hx
  unfold greedyStep at hx
  split at hx
  · exact Finset.mem_insert_of_mem hx
  · exact hx

theorem greedyScan_append (I : Finset V) (a b : List V) :
    greedyScan G I (a ++ b) = greedyScan G (greedyScan G I a) b := by
  induction a generalizing I with
  | nil => rfl
  | cons v a ih =>
      simp only [List.cons_append, greedyScan]
      exact ih (greedyStep G I v)

theorem greedyScan_subset_union (I : Finset V) (l : List V) :
    greedyScan G I l ⊆ I ∪ l.toFinset := by
  induction l generalizing I with
  | nil =>
      simp [greedyScan]
  | cons v l ih =>
      intro x hx
      have hx' := ih (greedyStep G I v) hx
      simp only [Finset.mem_union, List.toFinset_cons, Finset.mem_insert] at hx' ⊢
      rcases hx' with hstep | hl
      · have hs := greedyStep_subset_insert G I v hstep
        rcases (Finset.mem_insert.mp hs) with rfl | hxI
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hxI
      · exact Or.inr (Or.inr hl)

theorem greedyList_rejected_has_predecessor (a b : List V) (w : V)
    (hw : w ∉ greedyList G (a ++ w :: b)) :
    ∃ u ∈ greedyList G (a ++ w :: b),
      G.Adj u w ∧ Precedes (a ++ w :: b) u w := by
  let J : Finset V := greedyScan G ∅ a
  have hscan :
      greedyList G (a ++ w :: b) =
        greedyScan G (greedyStep G J w) b := by
    unfold greedyList
    rw [greedyScan_append]
    rfl
  have hblock : ∃ u ∈ J, G.Adj u w := by
    by_contra h
    have hwstep : w ∈ greedyStep G J w := by
      simp [greedyStep, h]
    have hwfinal : w ∈ greedyList G (a ++ w :: b) := by
      rw [hscan]
      exact greedyScan_subset G (greedyStep G J w) b hwstep
    exact hw hwfinal
  rcases hblock with ⟨u, huJ, hadj⟩
  have huStep : u ∈ greedyStep G J w :=
    greedyStep_subset G J w huJ
  have huFinal : u ∈ greedyList G (a ++ w :: b) := by
    rw [hscan]
    exact greedyScan_subset G (greedyStep G J w) b huStep
  have hua : u ∈ a := by
    have huUnion := greedyScan_subset_union G (∅ : Finset V) a huJ
    simpa [J] using huUnion
  exact ⟨u, huFinal, hadj, precedes_append_of_mem hua (by simp)⟩

theorem greedyScan_take_eq_inter (l : List V) (I : Finset V)
    (hl : l.Nodup) (hI : IsIndependent G I)
    (hcert : ∀ ⦃w⦄, w ∉ I → ∃ u ∈ I, G.Adj u w ∧ Precedes l u w)
    (n : ℕ) :
    greedyScan G ∅ (l.take n) = I ∩ (l.take n).toFinset := by
  induction n with
  | zero =>
      simp [greedyScan]
  | succ n ih =>
      by_cases hn : n < l.length
      · let v : V := l[n]
        have htake :
            l.take (n + 1) = l.take n ++ [v] := by
          simpa [v] using (List.take_concat_get' l n hn).symm
        rw [htake, greedyScan_append]
        simp only [greedyScan]
        rw [ih]
        by_cases hv : v ∈ I
        · have hblock :
              ¬ ∃ u ∈ I ∩ (l.take n).toFinset, G.Adj u v := by
            rintro ⟨u, hu, hadj⟩
            have huI : u ∈ I := (Finset.mem_inter.mp hu).1
            exact (hI huI hv) hadj
          rw [greedyStep]
          simp only [hblock, if_false]
          ext x
          simp [htake, hv]
        · rcases hcert hv with ⟨u, huI, hadj, hprec⟩
          have hul : u ∈ l := precedes_mem_left hprec
          have hidx : l.idxOf u < l.idxOf v :=
            precedes_idxOf_lt hl hprec
          have hvidx : l.idxOf v = n := by
            simpa [v] using hl.idxOf_getElem n hn
          have hutake : u ∈ l.take n := by
            apply (List.mem_take_iff_idxOf_lt hul).2
            simpa [hvidx] using hidx
          have hblock :
              ∃ x ∈ I ∩ (l.take n).toFinset, G.Adj x v := by
            exact ⟨u, by simp [huI, hutake], hadj⟩
          rw [greedyStep]
          simp only [hblock, if_true]
          ext x
          simp [htake, hv]
      · have hle : l.length ≤ n := Nat.le_of_not_gt hn
        have htakeN : l.take n = l :=
          (List.take_eq_self_iff l).2 hle
        have htakeS : l.take (n + 1) = l :=
          (List.take_eq_self_iff l).2 (hle.trans (Nat.le_succ n))
        simpa [htakeN, htakeS] using ih

end Greedy

theorem greedyOutput_priorityCertificate (G : SimpleGraph V) {l : List V}
    (hl : IsVertexOrder l) :
    PriorityCertificate G (greedyOutput G l) l := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  refine ⟨hl, greedyOutput_maximal G hl, ?_⟩
  intro w hw
  have hwl : w ∈ l := isVertexOrder_complete hl w
  rcases List.append_of_mem hwl with ⟨a, b, rfl⟩
  have hw' : w ∉ greedyList G (a ++ w :: b) := by
    simpa [greedyOutput] using hw
  rcases greedyList_rejected_has_predecessor G a b w hw' with
    ⟨u, hu, hadj, hprec⟩
  exact ⟨u, by simpa [greedyOutput] using hu, hadj, hprec⟩

theorem greedyOutput_eq_of_priorityCertificate (G : SimpleGraph V)
    {I : Finset V} {l : List V}
    (hcert : PriorityCertificate G I l) :
    greedyOutput G l = I := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  rcases hcert with ⟨hl, hI, hprio⟩
  have hnodup : l.Nodup := isVertexOrder_nodup hl
  have hsub : I ⊆ l.toFinset := by
    intro x hx
    exact by
      simp only [List.mem_toFinset]
      exact isVertexOrder_complete hl x
  have hscan :=
    greedyScan_take_eq_inter G l I hnodup hI.2.1 hprio l.length
  have hscan' : greedyList G l = I := by
    unfold greedyList
    simpa [Finset.inter_eq_left.mpr hsub] using hscan
  simpa [greedyOutput] using hscan'

theorem priorityCertificate_iff_greedyOutput_eq (G : SimpleGraph V)
    {I : Finset V} {l : List V} (hl : IsVertexOrder l) :
    PriorityCertificate G I l ↔ greedyOutput G l = I := by
  constructor
  · exact greedyOutput_eq_of_priorityCertificate G
  · intro hout
    simpa [hout] using greedyOutput_priorityCertificate G hl

theorem fibre_nonempty_of_maximal (G : SimpleGraph V) {I : Finset V}
    (hI : IsMaximalIndependent G I) :
    (fibre G I).Nonempty := by
  classical
  let l : List V := I.toList ++ (Finset.univ \ I).toList
  have hnodup : l.Nodup := by
    dsimp [l]
    rw [List.nodup_append']
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    subst b
    simp only [Finset.mem_toList, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at ha hb
    exact hb ha
  have horder : IsVertexOrder l := by
    unfold IsVertexOrder
    apply (List.perm_ext_iff_of_nodup hnodup (Finset.nodup_toList _)).2
    intro x
    by_cases hx : x ∈ I
    · simp [l, hx]
    · simp [l, hx]
  have hcert : PriorityCertificate G I l := by
    refine ⟨horder, hI, ?_⟩
    intro w hw
    rcases hI.2.2 (by simp) hw with ⟨u, hu, hadj⟩
    refine ⟨u, hu, hadj, ?_⟩
    apply precedes_append_of_mem
    · simpa [l] using hu
    · simp [l, hw]
  have hout : greedyOutput G l = I :=
    greedyOutput_eq_of_priorityCertificate G hcert
  exact ⟨l, (fibre_mem_iff G I l).2 ⟨horder, hout⟩⟩

theorem fibreCount_pos_of_maximal (G : SimpleGraph V) {I : Finset V}
    (hI : IsMaximalIndependent G I) :
    0 < fibreCount G I := by
  exact Finset.card_pos.mpr (fibre_nonempty_of_maximal G hI)

@[simp] theorem mem_maximalIndependentSets_iff (G : SimpleGraph V)
    {I : Finset V} :
    I ∈ maximalIndependentSets G ↔ IsMaximalIndependent G I := by
  classical
  simp [maximalIndependentSets]

theorem maximalIndependentSets_nonempty (G : SimpleGraph V) :
    (maximalIndependentSets G).Nonempty := by
  classical
  let l : List V := Finset.univ.toList
  have hl : IsVertexOrder l := by
    exact List.Perm.refl _
  refine ⟨greedyOutput G l, ?_⟩
  exact (mem_maximalIndependentSets_iff G).2 (greedyOutput_maximal G hl)

theorem maximalIndependentSets_card_pos (G : SimpleGraph V) :
    0 < (maximalIndependentSets G).card := by
  exact Finset.card_pos.mpr (maximalIndependentSets_nonempty G)

theorem sum_fibreCount_eq_vertexOrders_card (G : SimpleGraph V) :
    (∑ I ∈ maximalIndependentSets G, fibreCount G I) =
      (vertexOrders (V := V)).card := by
  classical
  have hmap :
      ((vertexOrders (V := V) : Finset (List V)) : Set (List V)).MapsTo
        (greedyOutput G) (maximalIndependentSets G) := by
    intro l hl
    have horder : IsVertexOrder l := (mem_vertexOrders_iff).1 hl
    exact (mem_maximalIndependentSets_iff G).2 (greedyOutput_maximal G horder)
  have hsum :=
    Finset.card_eq_sum_card_fiberwise
      (s := vertexOrders (V := V))
      (t := maximalIndependentSets G)
      (f := greedyOutput G) hmap
  simpa [fibreCount, fibre] using hsum.symm

theorem uniformFibres_implies_greedyLawEqUniform (G : SimpleGraph V)
    (hU : UniformFibres G) :
    GreedyLawEqUniform G := by
  classical
  intro I
  by_cases hI : IsMaximalIndependent G I
  · have hsum := sum_fibreCount_eq_vertexOrders_card G
    have hconst :
        (∑ J ∈ maximalIndependentSets G, fibreCount G J) =
          (maximalIndependentSets G).card * fibreCount G I := by
      calc
        (∑ J ∈ maximalIndependentSets G, fibreCount G J) =
            ∑ J ∈ maximalIndependentSets G, fibreCount G I := by
              apply Finset.sum_congr rfl
              intro J hJ
              exact hU ((mem_maximalIndependentSets_iff G).1 hJ) hI
        _ = (maximalIndependentSets G).card * fibreCount G I := by
              simp [Nat.mul_comm]
    have hprod :
        (vertexOrders (V := V)).card =
          (maximalIndependentSets G).card * fibreCount G I :=
      hsum.symm.trans hconst
    have hprodQ :
        ((vertexOrders (V := V)).card : ℚ) =
          ((maximalIndependentSets G).card : ℚ) * (fibreCount G I : ℚ) := by
      exact_mod_cast hprod
    have hmQ : ((maximalIndependentSets G).card : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (maximalIndependentSets_card_pos G))
    have hcQ : (fibreCount G I : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (fibreCount_pos_of_maximal G hI))
    rw [greedyProb, uniformProb, if_pos hI, hprodQ]
    field_simp [hmQ, hcQ]
  · simp [greedyProb, uniformProb, hI,
      fibreCount_eq_zero_of_not_maximal G hI]

theorem greedyLawEqUniform_implies_uniformFibres (G : SimpleGraph V)
    (hL : GreedyLawEqUniform G) :
    UniformFibres G := by
  classical
  intro I J hI hJ
  have hu : uniformProb G I = uniformProb G J := by
    simp [uniformProb, hI, hJ]
  have hg : greedyProb G I = greedyProb G J :=
    (hL I).trans (hu.trans (hL J).symm)
  rw [greedyProb, greedyProb] at hg
  have hnQ : ((vertexOrders (V := V)).card : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (vertexOrders_card_pos (V := V)))
  have hc :
      (fibreCount G I : ℚ) = (fibreCount G J : ℚ) :=
    (div_left_inj' hnQ).1 hg
  exact_mod_cast hc

theorem uniformFibres_iff_greedyLawEqUniform (G : SimpleGraph V) :
    UniformFibres G ↔ GreedyLawEqUniform G :=
  ⟨uniformFibres_implies_greedyLawEqUniform G,
    greedyLawEqUniform_implies_uniformFibres G⟩

theorem greedyLawEqUniform_iff_on_maximal (G : SimpleGraph V) :
    GreedyLawEqUniform G ↔
      ∀ I : Finset V, IsMaximalIndependent G I →
        greedyProb G I =
          1 / ((maximalIndependentSets G).card : ℚ) := by
  constructor
  · intro h I hI
    simpa [uniformProb, hI] using h I
  · intro h I
    by_cases hI : IsMaximalIndependent G I
    · simpa [uniformProb, hI] using h I hI
    · simp [greedyProb, uniformProb, hI,
        fibreCount_eq_zero_of_not_maximal G hI]

theorem bias_eq_zero_iff_greedyLawEqUniform (G : SimpleGraph V) :
    bias G = 0 ↔ GreedyLawEqUniform G := by
  rw [greedyLawEqUniform_iff_on_maximal]
  constructor
  · intro hb I hI
    have hhalf : (1 / 2 : ℚ) ≠ 0 := by norm_num
    have hsum :
        (∑ J ∈ maximalIndependentSets G,
          |greedyProb G J -
            1 / ((maximalIndependentSets G).card : ℚ)|) = 0 := by
      unfold bias at hb
      exact (mul_eq_zero.mp hb).resolve_left hhalf
    have hall :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun J hJ => abs_nonneg
          (greedyProb G J -
            1 / ((maximalIndependentSets G).card : ℚ)))).1 hsum
    have hterm :=
      hall I ((mem_maximalIndependentSets_iff G).2 hI)
    exact sub_eq_zero.mp (abs_eq_zero.mp hterm)
  · intro h
    unfold bias
    have hz :
        ∀ I ∈ maximalIndependentSets G,
          |greedyProb G I -
            1 / ((maximalIndependentSets G).card : ℚ)| = 0 := by
      intro I hI
      rw [abs_eq_zero, sub_eq_zero]
      exact h I ((mem_maximalIndependentSets_iff G).1 hI)
    have hsum :
        (∑ I ∈ maximalIndependentSets G,
          |greedyProb G I -
            1 / ((maximalIndependentSets G).card : ℚ)|) = 0 := by
      apply Finset.sum_eq_zero
      intro I hI
      exact hz I hI
    rw [hsum, mul_zero]

end GreedyUniformity
