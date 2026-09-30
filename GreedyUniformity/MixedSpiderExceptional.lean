module

public import GreedyUniformity.MixedSpiderRelevant

@[expose] public section

namespace GreedyUniformity

open MixedSpiderVertex

section Exceptional

variable {k l : ℕ}

/-- Orders in which the centre is first in R_S and the arm pattern is T. -/
noncomputable def mixedSpiderFirstCenterPatternOrders
    (S T : Finset (Fin k)) :
    Finset (List (MixedSpiderVertex k l)) := by
  classical
  let R := mixedSpiderRelevant (l := l) S
  let hR : R.Nonempty := mixedSpiderRelevant_nonempty S
  exact (firstInFinsetOrders R hR center).filter fun order =>
    mixedSpiderArmPattern order = T

theorem mem_mixedSpiderFirstCenterPatternOrders_iff
    {S T : Finset (Fin k)} {order : List (MixedSpiderVertex k l)} :
    order ∈ mixedSpiderFirstCenterPatternOrders (l := l) S T ↔
      IsVertexOrder order ∧
        firstInFinset (mixedSpiderRelevant (l := l) S)
          (mixedSpiderRelevant_nonempty S) order = center ∧
        mixedSpiderArmPattern order = T := by
  classical
  simpa [mixedSpiderFirstCenterPatternOrders,
    mem_firstInFinsetOrders_iff, and_assoc]

/-- Inside the centre-first orders for R_S, all arm patterns are equinumerous. -/
theorem mixedSpiderFirstCenterPatternOrders_card_eq_empty
    (S T : Finset (Fin k)) :
    (mixedSpiderFirstCenterPatternOrders (l := l) S T).card =
      (mixedSpiderFirstCenterPatternOrders (l := l) S ∅).card := by
  classical
  let σ := mixedSpiderArmFlip (l := l) T
  apply Finset.card_bij (fun order _ => order.map σ)
  · intro order hmem
    rcases (mem_mixedSpiderFirstCenterPatternOrders_iff).1 hmem with
      ⟨horder, hfirst, hpat⟩
    apply (mem_mixedSpiderFirstCenterPatternOrders_iff).2
    refine ⟨map_equiv_isVertexOrder σ horder, ?_, ?_⟩
    · simpa [σ] using firstRelevant_center_map_armFlip S T horder hfirst
    · exact armPattern_map_flip_self_eq_empty horder hpat
  · intro a ha b hb hab
    exact (List.map_injective_iff.mpr σ.injective) hab
  · intro order hmem
    rcases (mem_mixedSpiderFirstCenterPatternOrders_iff).1 hmem with
      ⟨horder, hfirst, hpat⟩
    refine ⟨order.map σ, ?_, ?_⟩
    · apply (mem_mixedSpiderFirstCenterPatternOrders_iff).2
      refine ⟨map_equiv_isVertexOrder σ horder, ?_, ?_⟩
      · simpa [σ] using firstRelevant_center_map_armFlip S T horder hfirst
      · exact armPattern_map_flip_empty_eq_self horder hpat
    · simpa [σ] using map_mixedSpiderArmFlip_twice T order

/-- Restricting to one arm pattern costs a factor 2^k even after conditioning
on the centre being first in R_S. -/
theorem two_pow_mul_mixedSpiderFirstCenterPatternOrders_card
    (S T : Finset (Fin k)) :
    2 ^ k *
        (mixedSpiderFirstCenterPatternOrders (l := l) S T).card =
      (firstInFinsetOrders
        (mixedSpiderRelevant (l := l) S)
        (mixedSpiderRelevant_nonempty S) center).card := by
  classical
  let R := mixedSpiderRelevant (l := l) S
  let hR : R.Nonempty := mixedSpiderRelevant_nonempty S
  let F := firstInFinsetOrders R hR center
  have hpart :
      F.card =
        ∑ U ∈ (Finset.univ : Finset (Finset (Fin k))),
          (mixedSpiderFirstCenterPatternOrders (l := l) S U).card := by
    simpa [F, R, hR, mixedSpiderFirstCenterPatternOrders] using
      (Finset.card_eq_sum_card_fiberwise
        (f := mixedSpiderArmPattern (k := k) (l := l))
        (s := F)
        (t := (Finset.univ : Finset (Finset (Fin k))))
        (by
          intro order horder
          simp))
  have heq :
      ∀ U : Finset (Fin k),
        (mixedSpiderFirstCenterPatternOrders (l := l) S U).card =
          (mixedSpiderFirstCenterPatternOrders (l := l) S ∅).card :=
    mixedSpiderFirstCenterPatternOrders_card_eq_empty S
  calc
    2 ^ k *
        (mixedSpiderFirstCenterPatternOrders (l := l) S T).card =
        2 ^ k *
          (mixedSpiderFirstCenterPatternOrders (l := l) S ∅).card := by
            rw [heq T]
    _ = ∑ U ∈ (Finset.univ : Finset (Finset (Fin k))),
          (mixedSpiderFirstCenterPatternOrders (l := l) S ∅).card := by
            simp
    _ = ∑ U ∈ (Finset.univ : Finset (Finset (Fin k))),
          (mixedSpiderFirstCenterPatternOrders (l := l) S U).card := by
            apply Finset.sum_congr rfl
            intro U hU
            rw [heq U]
    _ = F.card := hpart.symm
    _ = (firstInFinsetOrders
        (mixedSpiderRelevant (l := l) S)
        (mixedSpiderRelevant_nonempty S) center).card := rfl

/-- Exceptional orders for arm pattern S: the pattern is S and the centre is
first among its l+2|S|+1 relevant vertices. -/
noncomputable def mixedSpiderExceptionalOrders
    (S : Finset (Fin k)) :
    Finset (List (MixedSpiderVertex k l)) :=
  mixedSpiderFirstCenterPatternOrders (l := l) S S

theorem mem_mixedSpiderExceptionalOrders_iff
    {S : Finset (Fin k)} {order : List (MixedSpiderVertex k l)} :
    order ∈ mixedSpiderExceptionalOrders (l := l) S ↔
      IsVertexOrder order ∧
        firstInFinset (mixedSpiderRelevant (l := l) S)
          (mixedSpiderRelevant_nonempty S) order = center ∧
        mixedSpiderArmPattern order = S := by
  exact mem_mixedSpiderFirstCenterPatternOrders_iff

/-- Exact exceptional-order count:
(l+2|S|+1) * 2^k * exceptional = all vertex orders. -/
theorem relevant_card_mul_two_pow_mul_exceptional_card
    (S : Finset (Fin k)) :
    (l + 2 * S.card + 1) *
        (2 ^ k * (mixedSpiderExceptionalOrders (l := l) S).card) =
      (vertexOrders (V := MixedSpiderVertex k l)).card := by
  let R := mixedSpiderRelevant (l := l) S
  let hR : R.Nonempty := mixedSpiderRelevant_nonempty S
  have hfirst :=
    card_mul_firstInFinsetOrders_card R hR center
      (center_mem_mixedSpiderRelevant S)
  have horient :=
    two_pow_mul_mixedSpiderFirstCenterPatternOrders_card
      (l := l) S S
  change (l + 2 * S.card + 1) *
      (2 ^ k *
        (mixedSpiderFirstCenterPatternOrders (l := l) S S).card) =
      (vertexOrders (V := MixedSpiderVertex k l)).card
  rw [horient]
  rw [← mixedSpiderRelevant_card (l := l) S]
  exact hfirst

end Exceptional

end GreedyUniformity
