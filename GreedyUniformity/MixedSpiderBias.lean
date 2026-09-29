import GreedyUniformity.MixedSpiderProbability

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
      (fun I : Finset (MixedSpiderVertex k l) => center ∈ I) hEq
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
  rw [maximalIndependentSets_mixedSpider_eq hl]
  rw [Finset.sum_insert mixedSpiderCenterSet_not_mem_noncenter_image]
  rw [greedyProb_mixedSpiderCenter]
  rw [mixedSpider_uniform_denominator hl]
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
    rw [greedyProb_mixedSpiderNoncenter hl S]
  rw [hmap]
  have huniv :
      (Finset.univ : Finset (Finset (Fin k))) =
        (Finset.univ : Finset (Fin k)).powerset := by
    ext S
    simp
  rw [huniv]
  rw [mixedSpider_sum_powerset_by_card]
  rfl

/-- The exact frozen Stage-3 expectation identity, now for the actual
permutation-law bias of the tuned mixed spider. -/
theorem bias_mixedSpider_tuned_eq_expectation
    {k : ℕ} (hk : 0 < k) :
    bias (mixedSpider k (mixedSpiderTunedL k)) =
      mixedSpiderTunedExpectation k := by
  rw [bias_mixedSpider_eq_formulaBias (mixedSpiderTunedL_pos k)]
  exact mixedSpiderFormulaBias_tuned_eq_expectation hk

end BiasBridge

end GreedyUniformity
