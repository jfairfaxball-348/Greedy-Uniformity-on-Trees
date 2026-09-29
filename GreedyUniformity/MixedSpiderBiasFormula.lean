import GreedyUniformity.MixedSpiderCertificate

open scoped BigOperators

namespace GreedyUniformity

/-- Uniform mass on the 2^k+1 maximal independent sets from B1. -/
def mixedSpiderUniformMass (k : ℕ) : ℚ :=
  1 / ((mixedSpiderN k : ℚ) + 1)

/-- Bias obtained from the frozen B2 closed forms, before identifying those
forms with the finite permutation law. -/
noncomputable def mixedSpiderFormulaBias (k l : ℕ) : ℚ :=
  (1 / 2 : ℚ) *
    (|mixedSpiderCenterFormula k l - mixedSpiderUniformMass k| +
      ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℚ) *
          |mixedSpiderNoncenterFormula k l j -
            mixedSpiderUniformMass k|)

/-- The exact expectation expression frozen in the Stage-3 proof. -/
noncomputable def mixedSpiderTunedExpectation (k : ℕ) : ℚ :=
  (1 / 2 : ℚ) *
    (binomialAverageQ k
        (fun j =>
          mixedSpiderW k j ^ 2 /
            (mixedSpiderA k ^ 2 *
              (mixedSpiderA k + mixedSpiderW k j))) +
      binomialAverageQ k
        (fun j =>
          |mixedSpiderW k j| /
            (mixedSpiderA k *
              (mixedSpiderA k + mixedSpiderW k j))))

theorem mixedSpiderUniformMass_eq (k : ℕ) :
    mixedSpiderUniformMass k = 1 / mixedSpiderA k := by
  simp [mixedSpiderUniformMass, mixedSpiderA, mixedSpiderN]

theorem binomialAverageQ_const (k : ℕ) (c : ℚ) :
    binomialAverageQ k (fun _ => c) = c := by
  have hsum :
      (∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ)) =
        (2 ^ k : ℚ) := by
    exact_mod_cast Nat.sum_range_choose k
  unfold binomialAverageQ
  rw [← Finset.sum_mul, hsum]
  have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
  field_simp

theorem binomialAverageQ_add
    (k : ℕ) (f g : ℕ → ℚ) :
    binomialAverageQ k (fun j => f j + g j) =
      binomialAverageQ k f + binomialAverageQ k g := by
  unfold binomialAverageQ
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

theorem binomialAverageQ_sub
    (k : ℕ) (f g : ℕ → ℚ) :
    binomialAverageQ k (fun j => f j - g j) =
      binomialAverageQ k f - binomialAverageQ k g := by
  unfold binomialAverageQ
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

theorem binomialAverageQ_const_mul
    (k : ℕ) (c : ℚ) (f : ℕ → ℚ) :
    binomialAverageQ k (fun j => c * f j) =
      c * binomialAverageQ k f := by
  unfold binomialAverageQ
  have hsum :
      (∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℚ) * (c * f j)) =
        c * ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℚ) * f j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

theorem mixedSpider_tuned_A_add_W_pos
    {k j : ℕ} (hj : j ≤ k) :
    0 < mixedSpiderA k + mixedSpiderW k j := by
  rw [← mixedSpider_tuned_denom_eq hj]
  exact_mod_cast mixedSpiderDenom_pos (mixedSpiderTunedL k) j

/-- Pointwise algebraic identity whose average, together with E[W]=0,
turns the centre deviation into a positive second-order term. -/
theorem mixedSpider_center_pointwise_identity
    {k j : ℕ} (hj : j ≤ k) :
    1 / (mixedSpiderA k + mixedSpiderW k j) -
        1 / mixedSpiderA k =
      mixedSpiderW k j ^ 2 /
          (mixedSpiderA k ^ 2 *
            (mixedSpiderA k + mixedSpiderW k j)) -
        mixedSpiderW k j / mixedSpiderA k ^ 2 := by
  have hA : mixedSpiderA k ≠ 0 := by
    unfold mixedSpiderA
    positivity
  have hAW : mixedSpiderA k + mixedSpiderW k j ≠ 0 :=
    ne_of_gt (mixedSpider_tuned_A_add_W_pos hj)
  field_simp
  ring

/-- The tuned centre deviation is exactly the first expectation in the frozen
Stage-3 identity. -/
theorem mixedSpiderCenterFormula_tuned_sub_uniform
    {k : ℕ} (hk : 0 < k) :
    mixedSpiderCenterFormula k (mixedSpiderTunedL k) -
        mixedSpiderUniformMass k =
      binomialAverageQ k
        (fun j =>
          mixedSpiderW k j ^ 2 /
            (mixedSpiderA k ^ 2 *
              (mixedSpiderA k + mixedSpiderW k j))) := by
  rw [mixedSpiderUniformMass_eq,
    mixedSpiderCenterFormula_tuned_eq_average hk]
  have hconst :=
    binomialAverageQ_const k (1 / mixedSpiderA k)
  have hrewrite :
      binomialAverageQ k
          (fun j => 1 / (mixedSpiderA k + mixedSpiderW k j)) -
          1 / mixedSpiderA k =
        binomialAverageQ k
          (fun j =>
            1 / (mixedSpiderA k + mixedSpiderW k j) -
              1 / mixedSpiderA k) := by
    rw [binomialAverageQ_sub, hconst]
  rw [hrewrite]
  have hpoint :
      (fun j =>
        1 / (mixedSpiderA k + mixedSpiderW k j) -
          1 / mixedSpiderA k) =
      (fun j =>
        mixedSpiderW k j ^ 2 /
            (mixedSpiderA k ^ 2 *
              (mixedSpiderA k + mixedSpiderW k j)) -
          (1 / mixedSpiderA k ^ 2) * mixedSpiderW k j) := by
    funext j
    have hA : mixedSpiderA k ≠ 0 := by
      unfold mixedSpiderA
      positivity
    have hklt : (k : ℚ) < (2 ^ k : ℚ) := by
      exact_mod_cast mixedSpider_nat_lt_two_pow k
    have hjnonneg : 0 ≤ (j : ℚ) := by positivity
    have hAW : mixedSpiderA k + mixedSpiderW k j ≠ 0 := by
      unfold mixedSpiderA mixedSpiderW
      nlinarith
    field_simp [hA, hAW]
    ring
  rw [hpoint, binomialAverageQ_sub,
    binomialAverageQ_const_mul, binomialAverageQ_W_eq_zero hk]
  ring

/-- Pointwise absolute deviation of a tuned type-j non-centre closed form. -/
theorem abs_mixedSpiderNoncenterFormula_tuned_sub_uniform
    {k j : ℕ} (hk : 0 < k) (hj : j ≤ k) :
    |mixedSpiderNoncenterFormula k (mixedSpiderTunedL k) j -
        mixedSpiderUniformMass k| =
      (1 / (2 ^ k : ℚ)) *
        (|mixedSpiderW k j| /
          (mixedSpiderA k *
            (mixedSpiderA k + mixedSpiderW k j))) := by
  rw [mixedSpiderUniformMass_eq,
    mixedSpiderNoncenterFormula_tuned_sub_uniform hk hj]
  have hN : 0 < (2 ^ k : ℚ) := by positivity
  have hA : 0 < mixedSpiderA k := by
    unfold mixedSpiderA
    positivity
  have hAW : 0 < mixedSpiderA k + mixedSpiderW k j :=
    mixedSpider_tuned_A_add_W_pos hj
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hN,
    abs_of_pos hA, abs_of_pos hAW]
  field_simp

/-- Frozen exact expectation identity for l=2^k-k, at the closed-form B2
level. The graph-law bridge is proved separately. -/
theorem mixedSpiderFormulaBias_tuned_eq_expectation
    {k : ℕ} (hk : 0 < k) :
    mixedSpiderFormulaBias k (mixedSpiderTunedL k) =
      mixedSpiderTunedExpectation k := by
  unfold mixedSpiderFormulaBias mixedSpiderTunedExpectation
  rw [mixedSpiderCenterFormula_tuned_sub_uniform hk]
  have hcenter_nonneg :
      0 ≤ binomialAverageQ k
        (fun j =>
          mixedSpiderW k j ^ 2 /
            (mixedSpiderA k ^ 2 *
              (mixedSpiderA k + mixedSpiderW k j))) := by
    unfold binomialAverageQ
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro j hj
      apply mul_nonneg
      · positivity
      · have hjle : j ≤ k := by
          simpa [Finset.mem_range] using hj
        have hAW : 0 < mixedSpiderA k + mixedSpiderW k j :=
          mixedSpider_tuned_A_add_W_pos hjle
        exact div_nonneg (sq_nonneg _)
          (mul_nonneg (sq_nonneg _) (le_of_lt hAW))
  rw [abs_of_nonneg hcenter_nonneg]
  have hsum :
      (∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℚ) *
            |mixedSpiderNoncenterFormula k (mixedSpiderTunedL k) j -
              mixedSpiderUniformMass k|) =
        binomialAverageQ k
          (fun j =>
            |mixedSpiderW k j| /
              (mixedSpiderA k *
                (mixedSpiderA k + mixedSpiderW k j))) := by
    unfold binomialAverageQ
    apply Eq.symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ k := by
      simpa [Finset.mem_range] using hj
    rw [abs_mixedSpiderNoncenterFormula_tuned_sub_uniform hk hjle]
    ring
  rw [hsum]

end GreedyUniformity
