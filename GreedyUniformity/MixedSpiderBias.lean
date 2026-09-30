module

public import GreedyUniformity.MixedSpiderProbability

public section

open scoped BigOperators

namespace GreedyUniformity

section BiasBridge

variable {k l : ℕ}

theorem mixedSpiderCenterSet_not_mem_noncenter_image :
    mixedSpiderCenterSet k l ∉
      (Finset.univ : Finset (Finset (Fin k))).map
        (mixedSpiderNoncenterEmbedding (k := k) (l := l)) := by
  classical
  intro hmem
  rcases Finset.mem_map.1 hmem with ⟨S, hS, hEq⟩
  have hmemEq :=
    congrArg
      (fun I : Finset (MixedSpiderVertex k l) => MixedSpiderVertex.center ∈ I) hEq
  simpa [mixedSpiderNoncenterEmbedding] using hmemEq

theorem mixedSpider_uniform_denominator
    (hl : 0 < l) :
    1 / ((maximalIndependentSets (mixedSpider k l)).card : ℚ) =
      mixedSpiderUniformMass k := by
  rw [mixedSpider_maximalIndependentSets_card hl]
  simp [mixedSpiderUniformMass, mixedSpiderN]

/-- B1+B2 identify the actual total-variation bias with the closed-form
mixed-spider expression. -/
theorem bias_mixedSpider_eq_formulaBias
    (hl : 0 < l) :
    bias (mixedSpider k l) = mixedSpiderFormulaBias k l := by
  classical
  unfold bias mixedSpiderFormulaBias
  rw [mixedSpider_uniform_denominator hl]
  rw [maximalIndependentSets_mixedSpider_eq hl]
  rw [Finset.sum_insert mixedSpiderCenterSet_not_mem_noncenter_image]
  rw [greedyProb_mixedSpiderCenter]
  have hmap :
      (∑ I ∈
          (Finset.univ : Finset (Finset (Fin k))).map
            (mixedSpiderNoncenterEmbedding (k := k) (l := l)),
          |greedyProb (mixedSpider k l) I - mixedSpiderUniformMass k|) =
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin k))),
          |mixedSpiderNoncenterFormula k l S.card -
            mixedSpiderUniformMass k| := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro S hS
    change
      |greedyProb (mixedSpider k l)
          (mixedSpiderNoncenterSet (l := l) S) -
          mixedSpiderUniformMass k| =
        |mixedSpiderNoncenterFormula k l S.card -
          mixedSpiderUniformMass k|
    rw [greedyProb_mixedSpiderNoncenter hl S]
  rw [hmap]
  have huniv :
      (Finset.univ : Finset (Finset (Fin k))) =
        (Finset.univ : Finset (Fin k)).powerset := by
    ext S
    simp
  rw [huniv]
  rw [mixedSpider_sum_powerset_by_card k
    (fun j =>
      |mixedSpiderNoncenterFormula k l j -
        mixedSpiderUniformMass k|)]

/-- The exact frozen Stage-3 expectation identity, now for the actual
permutation-law bias of the tuned mixed spider. -/
theorem bias_mixedSpider_tuned_eq_expectation
    {k : ℕ} (hk : 0 < k) :
    bias (mixedSpider k (mixedSpiderTunedL k)) =
      mixedSpiderTunedExpectation k := by
  rw [bias_mixedSpider_eq_formulaBias (mixedSpiderTunedL_pos k)]
  exact mixedSpiderFormulaBias_tuned_eq_expectation hk

/-- Frozen positive-bias assertion for the tuned family. -/
theorem bias_mixedSpider_tuned_pos
    {k : ℕ} (hk : 0 < k) :
    0 < bias (mixedSpider k (mixedSpiderTunedL k)) := by
  have hW : mixedSpiderW k 0 ≠ 0 := by
    have hkQ : (k : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    simpa [mixedSpiderW] using (neg_ne_zero.mpr hkQ)
  have hA : mixedSpiderA k ≠ 0 := by
    unfold mixedSpiderA
    positivity
  have hAW :
      mixedSpiderA k + mixedSpiderW k 0 ≠ 0 :=
    ne_of_gt (mixedSpider_tuned_A_add_W_pos
      (k := k) (j := 0) (Nat.zero_le k))
  have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
  have hdev :=
    mixedSpiderNoncenterFormula_tuned_sub_uniform
      (k := k) (j := 0) hk (Nat.zero_le k)
  have hsubne :
      mixedSpiderNoncenterFormula k (mixedSpiderTunedL k) 0 -
          mixedSpiderUniformMass k ≠ 0 := by
    rw [mixedSpiderUniformMass_eq, hdev]
    exact div_ne_zero hW
      (mul_ne_zero (mul_ne_zero hN hA) hAW)
  have hneq :
      mixedSpiderNoncenterFormula k (mixedSpiderTunedL k) 0 ≠
        mixedSpiderUniformMass k :=
    sub_ne_zero.mp hsubne
  have hbne :
      bias (mixedSpider k (mixedSpiderTunedL k)) ≠ 0 := by
    intro hb
    have hLaw :=
      (bias_eq_zero_iff_greedyLawEqUniform
        (mixedSpider k (mixedSpiderTunedL k))).1 hb
    have hmax :=
      mixedSpiderNoncenterSet_maximal
        (mixedSpiderTunedL_pos k) (∅ : Finset (Fin k))
    have heq :=
      (greedyLawEqUniform_iff_on_maximal
        (mixedSpider k (mixedSpiderTunedL k))).1 hLaw
        (mixedSpiderNoncenterSet
          (l := mixedSpiderTunedL k) (∅ : Finset (Fin k))) hmax
    rw [greedyProb_mixedSpiderNoncenter
      (mixedSpiderTunedL_pos k) (∅ : Finset (Fin k))] at heq
    rw [mixedSpider_uniform_denominator
      (k := k) (l := mixedSpiderTunedL k) (mixedSpiderTunedL_pos k)] at heq
    simp only [Finset.card_empty] at heq
    exact hneq heq
  have hnonneg :
      0 ≤ bias (mixedSpider k (mixedSpiderTunedL k)) := by
    unfold bias
    positivity
  exact lt_of_le_of_ne hnonneg (Ne.symm hbne)

end BiasBridge

end GreedyUniformity
