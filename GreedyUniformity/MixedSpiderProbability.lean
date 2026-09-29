import GreedyUniformity.MixedSpiderFibreCount

open scoped BigOperators

namespace GreedyUniformity

section Probability

variable {k l : ℕ}

theorem mixedSpiderOrientationOrders_ratio
    (S : Finset (Fin k)) :
    ((mixedSpiderOrientationOrders (l := l) S).card : ℚ) /
        ((vertexOrders (V := MixedSpiderVertex k l)).card : ℚ) =
      1 / (2 ^ k : ℚ) := by
  have hcount :=
    two_pow_mul_mixedSpiderOrientationOrders_card (l := l) S
  have hT :
      ((vertexOrders (V := MixedSpiderVertex k l)).card : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (vertexOrders_card_pos (V := MixedSpiderVertex k l)))
  have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) hcount
  push_cast at hcast
  field_simp [hT, hN]
  simpa [mul_comm] using hcast

theorem mixedSpiderExceptionalOrders_ratio
    (S : Finset (Fin k)) :
    ((mixedSpiderExceptionalOrders (l := l) S).card : ℚ) /
        ((vertexOrders (V := MixedSpiderVertex k l)).card : ℚ) =
      1 /
        ((2 ^ k : ℚ) * (l + 2 * S.card + 1 : ℚ)) := by
  have hcount :=
    relevant_card_mul_two_pow_mul_exceptional_card (l := l) S
  have hT :
      ((vertexOrders (V := MixedSpiderVertex k l)).card : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (vertexOrders_card_pos (V := MixedSpiderVertex k l)))
  have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
  have hm : (l + 2 * S.card + 1 : ℚ) ≠ 0 := by positivity
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) hcount
  push_cast at hcast
  field_simp [hT, hN, hm]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcast

/-- Frozen B2, non-centre part: every specific maximal independent set of
type j has probability (l+2j)/(2^k(l+2j+1)). -/
theorem greedyProb_mixedSpiderNoncenter
    (hl : 0 < l) (S : Finset (Fin k)) :
    greedyProb (mixedSpider k l)
        (mixedSpiderNoncenterSet (l := l) S) =
      mixedSpiderNoncenterFormula k l S.card := by
  have hsub :=
    mixedSpiderExceptionalOrders_subset_orientationOrders
      (k := k) (l := l) S
  have hle :
      (mixedSpiderExceptionalOrders (l := l) S).card ≤
        (mixedSpiderOrientationOrders (l := l) S).card :=
    Finset.card_le_card hsub
  unfold greedyProb
  rw [fibreCount_mixedSpiderNoncenter hl S]
  rw [Nat.cast_sub hle]
  rw [sub_div]
  rw [mixedSpiderOrientationOrders_ratio S,
    mixedSpiderExceptionalOrders_ratio S,
    mixedSpiderNoncenterFormula_eq]
  have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
  have hm : (l + 2 * S.card + 1 : ℚ) ≠ 0 := by positivity
  field_simp [hN, hm]
  push_cast
  ring

/-- Frozen B2, centre part: exact binomial-sum probability of the unique
centre-containing maximal independent set. -/
theorem greedyProb_mixedSpiderCenter :
    greedyProb (mixedSpider k l) (mixedSpiderCenterSet k l) =
      mixedSpiderCenterFormula k l := by
  classical
  unfold greedyProb
  rw [fibreCount_mixedSpiderCenter]
  simp only [Nat.cast_sum]
  rw [Finset.sum_div]
  have hrat :
      (∑ S ∈ (Finset.univ : Finset (Finset (Fin k))),
          ((mixedSpiderExceptionalOrders (l := l) S).card : ℚ) /
            ((vertexOrders (V := MixedSpiderVertex k l)).card : ℚ)) =
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin k))),
          1 / ((2 ^ k : ℚ) * (l + 2 * S.card + 1 : ℚ)) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [mixedSpiderExceptionalOrders_ratio S]
  rw [hrat]
  have hfactor :
      (∑ S ∈ (Finset.univ : Finset (Finset (Fin k))),
          1 / ((2 ^ k : ℚ) * (l + 2 * S.card + 1 : ℚ))) =
        (1 / (2 ^ k : ℚ)) *
          ∑ S ∈ (Finset.univ : Finset (Finset (Fin k))),
            1 / (l + 2 * S.card + 1 : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
    have hm : (l + 2 * S.card + 1 : ℚ) ≠ 0 := by positivity
    field_simp [hN, hm]
  rw [hfactor]
  rw [mixedSpiderCenterFormula_eq_powerset_average]
  have huniv :
      (Finset.univ : Finset (Finset (Fin k))) =
        (Finset.univ : Finset (Fin k)).powerset := by
    ext S
    simp
  rw [huniv]
  simp only [mixedSpiderN, mixedSpiderDenom]

end Probability

end GreedyUniformity
