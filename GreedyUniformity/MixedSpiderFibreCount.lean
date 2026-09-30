module

public import GreedyUniformity.MixedSpiderExceptional

@[expose] public section

namespace GreedyUniformity

open MixedSpiderVertex

section FibreCount

variable {k l : ℕ}

theorem precedes_trans_of_isVertexOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    {order : List V} (horder : IsVertexOrder order)
    {x y z : V} (hxy : Precedes order x y)
    (hyz : Precedes order y z) :
    Precedes order x z := by
  have hnodup := isVertexOrder_nodup horder
  have hxylt := precedes_idxOf_lt hnodup hxy
  have hyzlt := precedes_idxOf_lt hnodup hyz
  have hxz : x ≠ z := by
    intro hxz
    subst z
    omega
  rcases precedes_or_precedes_of_isVertexOrder horder hxz with hxzPrec | hzxPrec
  · exact hxzPrec
  · have hzxlt := precedes_idxOf_lt hnodup hzxPrec
    omega

/-- A complete order has arm pattern S exactly when it chooses the prescribed
direction on every arm. -/
theorem mixedSpiderArmPattern_eq_iff
    {S : Finset (Fin k)} {order : List (MixedSpiderVertex k l)}
    (horder : IsVertexOrder order) :
    mixedSpiderArmPattern order = S ↔
      (∀ i ∈ S, Precedes order (inner i) (outer i)) ∧
      (∀ i ∉ S, Precedes order (outer i) (inner i)) := by
  constructor
  · intro hpat
    refine ⟨?_, ?_⟩
    · intro i hi
      have : i ∈ mixedSpiderArmPattern order := by simpa [hpat]
      exact (mem_mixedSpiderArmPattern_iff order i).1 this
    · intro i hi
      have hnot : i ∉ mixedSpiderArmPattern order := by simpa [hpat]
      exact (precedes_reverse_iff_not horder
        (by simp : (inner i : MixedSpiderVertex k l) ≠ outer i)).2
        (by simpa [mem_mixedSpiderArmPattern_iff] using hnot)
  · rintro ⟨hforward, hreverse⟩
    ext i
    rw [mem_mixedSpiderArmPattern_iff]
    constructor
    · intro hprec
      by_contra hi
      have hrev := hreverse i hi
      exact (not_precedes_reverse_of_isVertexOrder horder
        (by simp : (inner i : MixedSpiderVertex k l) ≠ outer i)
        hprec) hrev
    · intro hi
      exact hforward i hi

/-- Under arm pattern S, centre-first in R_S is equivalent to the centre
preceding every direct leaf and every selected inner arm vertex. -/
theorem firstRelevant_center_iff
    {S : Finset (Fin k)} {order : List (MixedSpiderVertex k l)}
    (horder : IsVertexOrder order)
    (hpat : mixedSpiderArmPattern order = S) :
    firstInFinset (mixedSpiderRelevant (l := l) S)
        (mixedSpiderRelevant_nonempty S) order = center ↔
      (∀ r : Fin l, Precedes order center (leaf r)) ∧
      (∀ i ∈ S, Precedes order center (inner i)) := by
  constructor
  · intro hfirst
    have hall :=
      ((firstInFinset_eq_iff
        (mixedSpiderRelevant (l := l) S)
        (mixedSpiderRelevant_nonempty S) horder center).1 hfirst).2
    refine ⟨?_, ?_⟩
    · intro r
      exact hall (leaf r) (by simp)
        (by simp : (leaf r : MixedSpiderVertex k l) ≠ center)
    · intro i hi
      exact hall (inner i) (by simpa using hi)
        (by simp : (inner i : MixedSpiderVertex k l) ≠ center)
  · rintro ⟨hleaf, hinner⟩
    apply (firstInFinset_eq_iff
      (mixedSpiderRelevant (l := l) S)
      (mixedSpiderRelevant_nonempty S) horder center).2
    refine ⟨by simp, ?_⟩
    intro z hz hzc
    cases z with
    | center => exact (hzc rfl).elim
    | inner i =>
        have hi : i ∈ S := by simpa using hz
        exact hinner i hi
    | outer i =>
        have hi : i ∈ S := by simpa using hz
        have hci := hinner i hi
        have hio :
            Precedes order (inner i) (outer i) := by
          have hm : i ∈ mixedSpiderArmPattern order := by simpa [hpat]
          exact (mem_mixedSpiderArmPattern_iff order i).1 hm
        exact precedes_trans_of_isVertexOrder horder hci hio
    | leaf r =>
        exact hleaf r

/-- Compact form of the non-centre order certificate: fixed arm pattern and
failure of the corresponding centre-first exceptional event. -/
theorem mixedSpiderNoncenterOrderCertificate_iff_pattern_not_first
    (S : Finset (Fin k)) {order : List (MixedSpiderVertex k l)} :
    MixedSpiderNoncenterOrderCertificate S order ↔
      IsVertexOrder order ∧
        mixedSpiderArmPattern order = S ∧
        firstInFinset (mixedSpiderRelevant (l := l) S)
          (mixedSpiderRelevant_nonempty S) order ≠ center := by
  constructor
  · rintro ⟨horder, hforward, hreverse, hcenter⟩
    have hpat :
        mixedSpiderArmPattern order = S :=
      (mixedSpiderArmPattern_eq_iff horder).2 ⟨hforward, hreverse⟩
    refine ⟨horder, hpat, ?_⟩
    intro hfirst
    have hcf := (firstRelevant_center_iff horder hpat).1 hfirst
    rcases hcenter with ⟨r, hrc⟩ | ⟨i, hi, hic⟩
    · exact (not_precedes_reverse_of_isVertexOrder horder
        (by simp : (center : MixedSpiderVertex k l) ≠ leaf r)
        (hcf.1 r)) hrc
    · exact (not_precedes_reverse_of_isVertexOrder horder
        (by simp : (center : MixedSpiderVertex k l) ≠ inner i)
        (hcf.2 i hi)) hic
  · rintro ⟨horder, hpat, hnotfirst⟩
    rcases (mixedSpiderArmPattern_eq_iff horder).1 hpat with
      ⟨hforward, hreverse⟩
    refine ⟨horder, hforward, hreverse, ?_⟩
    by_contra hno
    push_neg at hno
    have hleaf :
        ∀ r : Fin l, Precedes order center (leaf r) := by
      intro r
      exact (precedes_reverse_iff_not horder
        (by simp : (leaf r : MixedSpiderVertex k l) ≠ center)).2
        (hno.1 r)
    have hinner :
        ∀ i ∈ S, Precedes order center (inner i) := by
      intro i hi
      exact (precedes_reverse_iff_not horder
        (by simp : (inner i : MixedSpiderVertex k l) ≠ center)).2
        (hno.2 i hi)
    exact hnotfirst ((firstRelevant_center_iff horder hpat).2
      ⟨hleaf, hinner⟩)

/-- Under a fixed arm pattern, the centre certificate is exactly the
corresponding centre-first exceptional condition. -/
theorem mixedSpiderCenterOrderCertificate_iff_firstRelevant
    (S : Finset (Fin k)) {order : List (MixedSpiderVertex k l)}
    (horder : IsVertexOrder order)
    (hpat : mixedSpiderArmPattern order = S) :
    MixedSpiderCenterOrderCertificate order ↔
      firstInFinset (mixedSpiderRelevant (l := l) S)
        (mixedSpiderRelevant_nonempty S) order = center := by
  constructor
  · rintro ⟨_, hleaf, harms⟩
    apply (firstRelevant_center_iff horder hpat).2
    refine ⟨hleaf, ?_⟩
    intro i hi
    rcases harms i with hci | hoi
    · exact hci
    · have hio :
          Precedes order (inner i) (outer i) := by
        have hm : i ∈ mixedSpiderArmPattern order := by simpa [hpat]
        exact (mem_mixedSpiderArmPattern_iff order i).1 hm
      exact (not_precedes_reverse_of_isVertexOrder horder
        (by simp : (inner i : MixedSpiderVertex k l) ≠ outer i)
        hio hoi).elim
  · intro hfirst
    have hcf := (firstRelevant_center_iff horder hpat).1 hfirst
    refine ⟨horder, hcf.1, ?_⟩
    intro i
    by_cases hi : i ∈ S
    · exact Or.inl (hcf.2 i hi)
    · right
      have hnot : i ∉ mixedSpiderArmPattern order := by simpa [hpat]
      exact (precedes_reverse_iff_not horder
        (by simp : (inner i : MixedSpiderVertex k l) ≠ outer i)).2
        (by simpa [mem_mixedSpiderArmPattern_iff] using hnot)

/-- The exact non-centre fibre is one orientation class with its exceptional
centre-first orders removed. -/
theorem fibre_mixedSpiderNoncenter_eq_sdiff
    (hl : 0 < l) (S : Finset (Fin k)) :
    fibre (mixedSpider k l) (mixedSpiderNoncenterSet (l := l) S) =
      mixedSpiderOrientationOrders (l := l) S \
        mixedSpiderExceptionalOrders (l := l) S := by
  classical
  ext order
  constructor
  · intro hfib
    rcases (fibre_mem_iff _ _ _).1 hfib with ⟨horder, hout⟩
    have hcert :
        MixedSpiderNoncenterOrderCertificate S order :=
      (greedyOutput_mixedSpiderNoncenter_iff hl S horder).1 hout
    rcases
      (mixedSpiderNoncenterOrderCertificate_iff_pattern_not_first S).1 hcert with
      ⟨_, hpat, hnotfirst⟩
    apply Finset.mem_sdiff.2
    refine ⟨(mem_mixedSpiderOrientationOrders_iff).2 ⟨horder, hpat⟩, ?_⟩
    intro hexc
    have hfirst :=
      ((mem_mixedSpiderExceptionalOrders_iff).1 hexc).2.1
    exact hnotfirst hfirst
  · intro hsdiff
    rcases Finset.mem_sdiff.1 hsdiff with ⟨horient, hnexc⟩
    rcases (mem_mixedSpiderOrientationOrders_iff).1 horient with
      ⟨horder, hpat⟩
    have hnotfirst :
        firstInFinset (mixedSpiderRelevant (l := l) S)
          (mixedSpiderRelevant_nonempty S) order ≠ center := by
      intro hfirst
      apply hnexc
      exact (mem_mixedSpiderExceptionalOrders_iff).2
        ⟨horder, hfirst, hpat⟩
    have hcert :
        MixedSpiderNoncenterOrderCertificate S order :=
      (mixedSpiderNoncenterOrderCertificate_iff_pattern_not_first S).2
        ⟨horder, hpat, hnotfirst⟩
    apply (fibre_mem_iff _ _ _).2
    refine ⟨horder, ?_⟩
    exact (greedyOutput_mixedSpiderNoncenter_iff hl S horder).2 hcert

theorem mixedSpiderExceptionalOrders_subset_orientationOrders
    (S : Finset (Fin k)) :
    mixedSpiderExceptionalOrders (l := l) S ⊆
      mixedSpiderOrientationOrders (l := l) S := by
  intro order h
  rcases (mem_mixedSpiderExceptionalOrders_iff).1 h with
    ⟨horder, hfirst, hpat⟩
  exact (mem_mixedSpiderOrientationOrders_iff).2 ⟨horder, hpat⟩

theorem fibreCount_mixedSpiderNoncenter
    (hl : 0 < l) (S : Finset (Fin k)) :
    fibreCount (mixedSpider k l) (mixedSpiderNoncenterSet (l := l) S) =
      (mixedSpiderOrientationOrders (l := l) S).card -
        (mixedSpiderExceptionalOrders (l := l) S).card := by
  unfold fibreCount
  rw [fibre_mixedSpiderNoncenter_eq_sdiff hl S]
  exact Finset.card_sdiff_of_subset
    (mixedSpiderExceptionalOrders_subset_orientationOrders S)

/-- The part of the centre fibre having arm pattern S is exactly the
exceptional order set indexed by S. -/
theorem centre_fibre_filter_pattern_eq_exceptional
    (S : Finset (Fin k)) :
    (fibre (mixedSpider k l) (mixedSpiderCenterSet k l)).filter
        (fun order => mixedSpiderArmPattern order = S) =
      mixedSpiderExceptionalOrders (l := l) S := by
  classical
  ext order
  constructor
  · intro h
    rcases Finset.mem_filter.1 h with ⟨hfib, hpat⟩
    rcases (fibre_mem_iff _ _ _).1 hfib with ⟨horder, hout⟩
    have hcert :
        MixedSpiderCenterOrderCertificate order :=
      (greedyOutput_mixedSpiderCenter_iff horder).1 hout
    have hfirst :=
      (mixedSpiderCenterOrderCertificate_iff_firstRelevant S horder hpat).1
        hcert
    exact (mem_mixedSpiderExceptionalOrders_iff).2
      ⟨horder, hfirst, hpat⟩
  · intro hexc
    rcases (mem_mixedSpiderExceptionalOrders_iff).1 hexc with
      ⟨horder, hfirst, hpat⟩
    have hcert :
        MixedSpiderCenterOrderCertificate order :=
      (mixedSpiderCenterOrderCertificate_iff_firstRelevant S horder hpat).2
        hfirst
    apply Finset.mem_filter.2
    refine ⟨?_, hpat⟩
    apply (fibre_mem_iff _ _ _).2
    refine ⟨horder, ?_⟩
    exact (greedyOutput_mixedSpiderCenter_iff horder).2 hcert

/-- The centre fibre is the disjoint sum of the exceptional classes. -/
theorem fibreCount_mixedSpiderCenter :
    fibreCount (mixedSpider k l) (mixedSpiderCenterSet k l) =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin k))),
        (mixedSpiderExceptionalOrders (l := l) S).card := by
  classical
  unfold fibreCount
  have hpart :=
    Finset.card_eq_sum_card_fiberwise
      (f := mixedSpiderArmPattern (k := k) (l := l))
      (s := fibre (mixedSpider k l) (mixedSpiderCenterSet k l))
      (t := (Finset.univ : Finset (Finset (Fin k))))
      (by
        intro order horder
        simp)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro S hS
  rw [centre_fibre_filter_pattern_eq_exceptional S]

end FibreCount

end GreedyUniformity
