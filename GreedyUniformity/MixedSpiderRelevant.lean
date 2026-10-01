module

public import GreedyUniformity.FirstInFinset
public import GreedyUniformity.MixedSpiderOrderCount

@[expose] public section

namespace GreedyUniformity

open MixedSpiderVertex

section Relevant

variable {k l : ℕ}

def mixedSpiderInnerEmbedding : Fin k ↪ MixedSpiderVertex k l where
  toFun := inner
  inj' := by
    intro i j h
    exact MixedSpiderVertex.inner.inj h

def mixedSpiderOuterEmbedding : Fin k ↪ MixedSpiderVertex k l where
  toFun := outer
  inj' := by
    intro i j h
    exact MixedSpiderVertex.outer.inj h

def mixedSpiderLeafEmbedding : Fin l ↪ MixedSpiderVertex k l where
  toFun := leaf
  inj' := by
    intro r s h
    exact MixedSpiderVertex.leaf.inj h

/-- Relevant vertices for the exceptional order associated with an arm set S:
the centre, all direct leaves, and both endpoints of each arm in S. -/
noncomputable def mixedSpiderRelevant
    (S : Finset (Fin k)) : Finset (MixedSpiderVertex k l) := by
  classical
  exact insert center
    ((S.map mixedSpiderInnerEmbedding) ∪
      ((S.map mixedSpiderOuterEmbedding) ∪
        ((Finset.univ : Finset (Fin l)).map mixedSpiderLeafEmbedding)))

@[simp] theorem center_mem_mixedSpiderRelevant
    (S : Finset (Fin k)) :
    (center : MixedSpiderVertex k l) ∈ mixedSpiderRelevant (l := l) S := by
  classical
  simp [mixedSpiderRelevant]

@[simp] theorem inner_mem_mixedSpiderRelevant_iff
    (S : Finset (Fin k)) (i : Fin k) :
    inner i ∈ mixedSpiderRelevant (l := l) S ↔ i ∈ S := by
  classical
  change inner i ∈
      insert center
        ((S.map (mixedSpiderInnerEmbedding (k := k) (l := l))) ∪
          ((S.map (mixedSpiderOuterEmbedding (k := k) (l := l))) ∪
            ((Finset.univ : Finset (Fin l)).map
              (mixedSpiderLeafEmbedding (k := k) (l := l))))) ↔
    i ∈ S
  constructor
  · intro h
    rw [Finset.mem_insert, Finset.mem_union, Finset.mem_union] at h
    rcases h with hcenter | hinner | houter | hleaf
    · cases hcenter
    · rcases Finset.mem_map.1 hinner with ⟨w, hwS, hw⟩
      change inner w = inner i at hw
      have hwi : w = i := MixedSpiderVertex.inner.inj hw
      simpa [hwi] using hwS
    · rcases Finset.mem_map.1 houter with ⟨w, hwS, hw⟩
      change outer w = inner i at hw
      cases hw
    · rcases Finset.mem_map.1 hleaf with ⟨w, hwS, hw⟩
      change leaf w = inner i at hw
      cases hw
  · intro hi
    rw [Finset.mem_insert, Finset.mem_union, Finset.mem_union]
    exact Or.inr (Or.inl (Finset.mem_map.2 ⟨i, hi, rfl⟩))

@[simp] theorem outer_mem_mixedSpiderRelevant_iff
    (S : Finset (Fin k)) (i : Fin k) :
    outer i ∈ mixedSpiderRelevant (l := l) S ↔ i ∈ S := by
  classical
  change outer i ∈
      insert center
        ((S.map (mixedSpiderInnerEmbedding (k := k) (l := l))) ∪
          ((S.map (mixedSpiderOuterEmbedding (k := k) (l := l))) ∪
            ((Finset.univ : Finset (Fin l)).map
              (mixedSpiderLeafEmbedding (k := k) (l := l))))) ↔
    i ∈ S
  constructor
  · intro h
    rw [Finset.mem_insert, Finset.mem_union, Finset.mem_union] at h
    rcases h with hcenter | hinner | houter | hleaf
    · cases hcenter
    · rcases Finset.mem_map.1 hinner with ⟨w, hwS, hw⟩
      change inner w = outer i at hw
      cases hw
    · rcases Finset.mem_map.1 houter with ⟨w, hwS, hw⟩
      change outer w = outer i at hw
      have hwi : w = i := MixedSpiderVertex.outer.inj hw
      simpa [hwi] using hwS
    · rcases Finset.mem_map.1 hleaf with ⟨w, hwS, hw⟩
      change leaf w = outer i at hw
      cases hw
  · intro hi
    rw [Finset.mem_insert, Finset.mem_union, Finset.mem_union]
    exact Or.inr (Or.inr (Or.inl (Finset.mem_map.2 ⟨i, hi, rfl⟩)))

@[simp] theorem leaf_mem_mixedSpiderRelevant
    (S : Finset (Fin k)) (r : Fin l) :
    leaf r ∈ mixedSpiderRelevant (l := l) S := by
  classical
  change leaf r ∈
    insert center
      ((S.map (mixedSpiderInnerEmbedding (k := k) (l := l))) ∪
        ((S.map (mixedSpiderOuterEmbedding (k := k) (l := l))) ∪
          ((Finset.univ : Finset (Fin l)).map
            (mixedSpiderLeafEmbedding (k := k) (l := l)))))
  rw [Finset.mem_insert, Finset.mem_union, Finset.mem_union]
  exact Or.inr (Or.inr
    (Or.inr (Finset.mem_map.2 ⟨r, Finset.mem_univ r, rfl⟩)))

theorem mixedSpiderRelevant_nonempty
    (S : Finset (Fin k)) :
    (mixedSpiderRelevant (l := l) S).Nonempty :=
  ⟨center, center_mem_mixedSpiderRelevant S⟩

theorem mixedSpiderRelevant_card
    (S : Finset (Fin k)) :
    (mixedSpiderRelevant (l := l) S).card =
      l + 2 * S.card + 1 := by
  classical
  let A :=
    S.map (mixedSpiderInnerEmbedding (k := k) (l := l))
  let B :=
    S.map (mixedSpiderOuterEmbedding (k := k) (l := l))
  let C :=
    (Finset.univ : Finset (Fin l)).map
      (mixedSpiderLeafEmbedding (k := k) (l := l))
  have hc : (center : MixedSpiderVertex k l) ∉ A ∪ (B ∪ C) := by
    intro h
    rw [Finset.mem_union, Finset.mem_union] at h
    rcases h with hA | hB | hC
    · rcases Finset.mem_map.1 hA with ⟨i, hiS, hi⟩
      change inner i = center at hi
      cases hi
    · rcases Finset.mem_map.1 hB with ⟨i, hiS, hi⟩
      change outer i = center at hi
      cases hi
    · rcases Finset.mem_map.1 hC with ⟨r, hr, hri⟩
      change leaf r = center at hri
      cases hri
  have hA : Disjoint A (B ∪ C) := by
    rw [Finset.disjoint_left]
    intro x hxA hxBC
    rcases Finset.mem_map.1 hxA with ⟨i, hiS, hix⟩
    rcases Finset.mem_union.1 hxBC with hxB | hxC
    · rcases Finset.mem_map.1 hxB with ⟨j, hjS, hjx⟩
      change inner i = x at hix
      change outer j = x at hjx
      have hbad : inner i = outer j := hix.trans hjx.symm
      cases hbad
    · rcases Finset.mem_map.1 hxC with ⟨r, hr, hrx⟩
      change inner i = x at hix
      change leaf r = x at hrx
      have hbad : inner i = leaf r := hix.trans hrx.symm
      cases hbad
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    rcases Finset.mem_map.1 hxB with ⟨i, hiS, hix⟩
    rcases Finset.mem_map.1 hxC with ⟨r, hr, hrx⟩
    change outer i = x at hix
    change leaf r = x at hrx
    have hbad : outer i = leaf r := hix.trans hrx.symm
    cases hbad
  change (insert center (A ∪ (B ∪ C))).card =
    l + 2 * S.card + 1
  rw [Finset.card_insert_of_notMem hc,
    Finset.card_union_of_disjoint hA,
    Finset.card_union_of_disjoint hBC]
  simp [A, B, C]
  omega

/-- Arm-endpoint flips preserve the relevant set, because each selected arm
contributes both endpoints and each unselected arm contributes neither. -/
theorem mixedSpiderArmFlip_mem_relevant_iff
    (S D : Finset (Fin k)) (v : MixedSpiderVertex k l) :
    mixedSpiderArmFlip (l := l) D v ∈ mixedSpiderRelevant (l := l) S ↔
      v ∈ mixedSpiderRelevant (l := l) S := by
  classical
  cases v with
  | center => simp
  | inner i =>
      rw [mixedSpiderArmFlip_inner]
      by_cases hi : i ∈ D <;> simp [hi]
  | outer i =>
      rw [mixedSpiderArmFlip_outer]
      by_cases hi : i ∈ D <;> simp [hi]
  | leaf r => simp

/-- Being the first relevant vertex is preserved by every arm flip; the centre
is fixed by the flip. -/
theorem firstRelevant_center_map_armFlip
    (S D : Finset (Fin k))
    {order : List (MixedSpiderVertex k l)}
    (horder : IsVertexOrder order)
    (hfirst :
      firstInFinset (mixedSpiderRelevant (l := l) S)
        (mixedSpiderRelevant_nonempty S) order = center) :
    firstInFinset (mixedSpiderRelevant (l := l) S)
        (mixedSpiderRelevant_nonempty S)
        (order.map (mixedSpiderArmFlip (l := l) D)) = center := by
  let R := mixedSpiderRelevant (l := l) S
  let hR : R.Nonempty := mixedSpiderRelevant_nonempty S
  let σ := mixedSpiderArmFlip (l := l) D
  apply (firstInFinset_eq_iff R hR
    (map_equiv_isVertexOrder σ horder) center).2
  refine ⟨by simp [R], ?_⟩
  intro z hz hzc
  let y : MixedSpiderVertex k l := σ.symm z
  have hyz : σ y = z := σ.apply_symm_apply z
  have hyR : y ∈ R := by
    have hz' : σ y ∈ R := by simpa [hyz] using hz
    exact (mixedSpiderArmFlip_mem_relevant_iff S D y).1 hz'
  have hyc : y ≠ center := by
    intro hyc
    apply hzc
    rw [← hyz, hyc]
    simp [σ]
  have hsource :=
    ((firstInFinset_eq_iff R hR horder center).1 hfirst).2 y hyR hyc
  have hmapped :
      Precedes (order.map σ) (σ center) (σ y) :=
    (precedes_map_equiv_iff σ order center y).2 hsource
  simpa [σ, hyz] using hmapped

end Relevant

end GreedyUniformity
