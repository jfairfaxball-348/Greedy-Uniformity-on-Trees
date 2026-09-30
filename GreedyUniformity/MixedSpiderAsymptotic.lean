import GreedyUniformity.MixedSpiderMoments
import Mathlib.Analysis.Asymptotics.Basic

open scoped BigOperators

namespace GreedyUniformity

/-- For k>=1, the tuned parameter satisfies 2k <= 2^k. -/
theorem two_mul_le_two_pow {k : ℕ} (hk : 0 < k) :
    2 * k ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ n =>
      induction n with
      | zero => norm_num
      | succ n ih =>
          have htwo : 2 ≤ 2 ^ (n + 1) := by
            have h := mixedSpider_nat_lt_two_pow (n + 1)
            omega
          rw [pow_succ]
          omega

/-- In the tuned family every relevant denominator is at least half of 2^k. -/
theorem half_two_pow_le_tuned_denom
    {k j : ℕ} (hk : 0 < k) (hj : j ≤ k) :
    (2 ^ k : ℚ) / 2 ≤
      mixedSpiderA k + mixedSpiderW k j := by
  have h2k : (2 * k : ℚ) ≤ (2 ^ k : ℚ) := by
    exact_mod_cast two_mul_le_two_pow hk
  have hj0 : (0 : ℚ) ≤ (j : ℚ) := by positivity
  simp only [mixedSpiderA, mixedSpiderW]
  push_cast
  linarith

theorem mixedSpider_first_expectand_le
    {k j : ℕ} (hk : 0 < k) (hj : j ≤ k) :
    mixedSpiderW k j ^ 2 /
        (mixedSpiderA k ^ 2 *
          (mixedSpiderA k + mixedSpiderW k j)) ≤
      2 * mixedSpiderW k j ^ 2 / (2 ^ k : ℚ) ^ 3 := by
  let N : ℚ := (2 ^ k : ℚ)
  let A : ℚ := mixedSpiderA k
  let W : ℚ := mixedSpiderW k j
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hA : N ≤ A := by
    dsimp [N, A, mixedSpiderA]
    linarith
  have hAW : N / 2 ≤ A + W := by
    dsimp [N, A, W]
    exact half_two_pow_le_tuned_denom hk hj
  have hA2 : N ^ 2 ≤ A ^ 2 := by
    nlinarith [sq_nonneg (A - N)]
  have hprod :
      N ^ 3 / 2 ≤ A ^ 2 * (A + W) := by
    calc
      N ^ 3 / 2 = N ^ 2 * (N / 2) := by ring
      _ ≤ A ^ 2 * (N / 2) :=
        mul_le_mul_of_nonneg_right hA2 (by positivity)
      _ ≤ A ^ 2 * (A + W) :=
        mul_le_mul_of_nonneg_left hAW (sq_nonneg A)
  have hhalf : 0 < N ^ 3 / 2 := by positivity
  have hnum : 0 ≤ W ^ 2 := sq_nonneg W
  have hdiv :
      W ^ 2 / (A ^ 2 * (A + W)) ≤
        W ^ 2 / (N ^ 3 / 2) :=
    div_le_div_of_nonneg_left hnum hhalf hprod
  dsimp [N, A, W] at hdiv ⊢
  calc
    mixedSpiderW k j ^ 2 /
        (mixedSpiderA k ^ 2 *
          (mixedSpiderA k + mixedSpiderW k j)) ≤
        mixedSpiderW k j ^ 2 / ((2 ^ k : ℚ) ^ 3 / 2) := hdiv
    _ = 2 * mixedSpiderW k j ^ 2 / (2 ^ k : ℚ) ^ 3 := by
      have hN0 : (2 ^ k : ℚ) ^ 3 ≠ 0 := by positivity
      field_simp [hN0]

theorem mixedSpider_second_expectand_le
    {k j : ℕ} (hk : 0 < k) (hj : j ≤ k) :
    |mixedSpiderW k j| /
        (mixedSpiderA k *
          (mixedSpiderA k + mixedSpiderW k j)) ≤
      2 * |mixedSpiderW k j| / (2 ^ k : ℚ) ^ 2 := by
  let N : ℚ := (2 ^ k : ℚ)
  let A : ℚ := mixedSpiderA k
  let W : ℚ := mixedSpiderW k j
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hA : N ≤ A := by
    dsimp [N, A, mixedSpiderA]
    linarith
  have hAW : N / 2 ≤ A + W := by
    dsimp [N, A, W]
    exact half_two_pow_le_tuned_denom hk hj
  have hprod :
      N ^ 2 / 2 ≤ A * (A + W) := by
    calc
      N ^ 2 / 2 = N * (N / 2) := by ring
      _ ≤ A * (N / 2) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ A * (A + W) := by
        apply mul_le_mul_of_nonneg_left hAW
        exact le_trans (by positivity : (0 : ℚ) ≤ N) hA
  have hhalf : 0 < N ^ 2 / 2 := by positivity
  have hnum : 0 ≤ |W| := abs_nonneg W
  have hdiv :
      |W| / (A * (A + W)) ≤ |W| / (N ^ 2 / 2) :=
    div_le_div_of_nonneg_left hnum hhalf hprod
  dsimp [N, A, W] at hdiv ⊢
  calc
    |mixedSpiderW k j| /
        (mixedSpiderA k *
          (mixedSpiderA k + mixedSpiderW k j)) ≤
        |mixedSpiderW k j| / ((2 ^ k : ℚ) ^ 2 / 2) := hdiv
    _ = 2 * |mixedSpiderW k j| / (2 ^ k : ℚ) ^ 2 := by
      have hN0 : (2 ^ k : ℚ) ^ 2 ≠ 0 := by positivity
      field_simp [hN0]

theorem binomialAverageQ_mono_on_range
    {k : ℕ} {f g : ℕ → ℚ}
    (hfg : ∀ j ≤ k, f j ≤ g j) :
    binomialAverageQ k f ≤ binomialAverageQ k g := by
  unfold binomialAverageQ
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left
    · exact hfg j (by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hj)
    · positivity
  · positivity

theorem mixedSpider_first_average_le
    {k : ℕ} (hk : 0 < k) :
    binomialAverageQ k
        (fun j =>
          mixedSpiderW k j ^ 2 /
            (mixedSpiderA k ^ 2 *
              (mixedSpiderA k + mixedSpiderW k j))) ≤
      2 * (k : ℚ) / (2 ^ k : ℚ) ^ 3 := by
  calc
    binomialAverageQ k
        (fun j =>
          mixedSpiderW k j ^ 2 /
            (mixedSpiderA k ^ 2 *
              (mixedSpiderA k + mixedSpiderW k j))) ≤
        binomialAverageQ k
          (fun j =>
            (2 / (2 ^ k : ℚ) ^ 3) * mixedSpiderW k j ^ 2) := by
              apply binomialAverageQ_mono_on_range
              intro j hj
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                mixedSpider_first_expectand_le hk hj
    _ = (2 / (2 ^ k : ℚ) ^ 3) *
        binomialAverageQ k (fun j => mixedSpiderW k j ^ 2) := by
          rw [binomialAverageQ_const_mul]
    _ = 2 * (k : ℚ) / (2 ^ k : ℚ) ^ 3 := by
          rw [binomialAverageQ_W_sq]
          ring

theorem mixedSpider_second_average_le
    {k : ℕ} (hk : 0 < k) :
    binomialAverageQ k
        (fun j =>
          |mixedSpiderW k j| /
            (mixedSpiderA k *
              (mixedSpiderA k + mixedSpiderW k j))) ≤
      (2 / (2 ^ k : ℚ) ^ 2) *
        binomialAverageQ k (fun j => |mixedSpiderW k j|) := by
  calc
    binomialAverageQ k
        (fun j =>
          |mixedSpiderW k j| /
            (mixedSpiderA k *
              (mixedSpiderA k + mixedSpiderW k j))) ≤
        binomialAverageQ k
          (fun j =>
            (2 / (2 ^ k : ℚ) ^ 2) * |mixedSpiderW k j|) := by
              apply binomialAverageQ_mono_on_range
              intro j hj
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                mixedSpider_second_expectand_le hk hj
    _ = (2 / (2 ^ k : ℚ) ^ 2) *
        binomialAverageQ k (fun j => |mixedSpiderW k j|) := by
          rw [binomialAverageQ_const_mul]

/-- Explicit rational precursor to the sparse-family asymptotic estimate. -/
theorem bias_mixedSpider_tuned_le_moments
    {k : ℕ} (hk : 0 < k) :
    bias (mixedSpider k (mixedSpiderTunedL k)) ≤
      (k : ℚ) / (2 ^ k : ℚ) ^ 3 +
        binomialAverageQ k (fun j => |mixedSpiderW k j|) /
          (2 ^ k : ℚ) ^ 2 := by
  rw [bias_mixedSpider_tuned_eq_expectation hk]
  unfold mixedSpiderTunedExpectation
  have h1 := mixedSpider_first_average_le hk
  have h2 := mixedSpider_second_average_le hk
  have h1' :
      (1 / 2 : ℚ) *
          binomialAverageQ k
            (fun j =>
              mixedSpiderW k j ^ 2 /
                (mixedSpiderA k ^ 2 *
                  (mixedSpiderA k + mixedSpiderW k j))) ≤
        (k : ℚ) / (2 ^ k : ℚ) ^ 3 := by
    calc
      (1 / 2 : ℚ) *
          binomialAverageQ k
            (fun j =>
              mixedSpiderW k j ^ 2 /
                (mixedSpiderA k ^ 2 *
                  (mixedSpiderA k + mixedSpiderW k j))) ≤
          (1 / 2 : ℚ) *
            (2 * (k : ℚ) / (2 ^ k : ℚ) ^ 3) := by
              exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (k : ℚ) / (2 ^ k : ℚ) ^ 3 := by ring
  have h2' :
      (1 / 2 : ℚ) *
          binomialAverageQ k
            (fun j =>
              |mixedSpiderW k j| /
                (mixedSpiderA k *
                  (mixedSpiderA k + mixedSpiderW k j))) ≤
        binomialAverageQ k (fun j => |mixedSpiderW k j|) /
          (2 ^ k : ℚ) ^ 2 := by
    calc
      (1 / 2 : ℚ) *
          binomialAverageQ k
            (fun j =>
              |mixedSpiderW k j| /
                (mixedSpiderA k *
                  (mixedSpiderA k + mixedSpiderW k j))) ≤
          (1 / 2 : ℚ) *
            ((2 / (2 ^ k : ℚ) ^ 2) *
              binomialAverageQ k (fun j => |mixedSpiderW k j|)) := by
                exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = binomialAverageQ k (fun j => |mixedSpiderW k j|) /
          (2 ^ k : ℚ) ^ 2 := by ring
  calc
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
                  (mixedSpiderA k + mixedSpiderW k j)))) =
      (1 / 2 : ℚ) *
          binomialAverageQ k
            (fun j =>
              mixedSpiderW k j ^ 2 /
                (mixedSpiderA k ^ 2 *
                  (mixedSpiderA k + mixedSpiderW k j))) +
        (1 / 2 : ℚ) *
          binomialAverageQ k
            (fun j =>
              |mixedSpiderW k j| /
                (mixedSpiderA k *
                  (mixedSpiderA k + mixedSpiderW k j))) := by ring
    _ ≤ (k : ℚ) / (2 ^ k : ℚ) ^ 3 +
        binomialAverageQ k (fun j => |mixedSpiderW k j|) /
          (2 ^ k : ℚ) ^ 2 := add_le_add h1' h2'

/-- Real-valued form of the explicit estimate, after Cauchy-Schwarz. -/
theorem cast_bias_mixedSpider_tuned_le
    {k : ℕ} (hk : 0 < k) :
    ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ) ≤
      (k : ℝ) / (2 ^ k : ℝ) ^ 3 +
        Real.sqrt (k : ℝ) / (2 ^ k : ℝ) ^ 2 := by
  have hq := bias_mixedSpider_tuned_le_moments hk
  have hr0 :
      ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ) ≤
        (((k : ℚ) / (2 ^ k : ℚ) ^ 3 +
          binomialAverageQ k (fun j => |mixedSpiderW k j|) /
            (2 ^ k : ℚ) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast hq
  have hr := hr0
  push_cast at hr
  rw [cast_binomialAverageQ_abs_W] at hr
  have habs := mixedSpider_absMoment_average_le_sqrt k
  calc
    ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ) ≤
        (k : ℝ) / (2 ^ k : ℝ) ^ 3 +
          (mixedSpiderAbsMomentSum k / (2 ^ k : ℝ)) /
            (2 ^ k : ℝ) ^ 2 := hr
    _ ≤ (k : ℝ) / (2 ^ k : ℝ) ^ 3 +
        Real.sqrt (k : ℝ) / (2 ^ k : ℝ) ^ 2 := by
          gcongr

/-- Explicit bound implying b(T)=O(sqrt(k)/4^k). -/
theorem cast_bias_mixedSpider_tuned_le_two_sqrt_div_four_pow
    {k : ℕ} (hk : 0 < k) :
    ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ) ≤
      2 * Real.sqrt (k : ℝ) / (4 ^ k : ℝ) := by
  have hb := cast_bias_mixedSpider_tuned_le hk
  have hkN : (k : ℝ) ≤ (2 ^ k : ℝ) := by
    exact_mod_cast Nat.le_of_lt (mixedSpider_nat_lt_two_pow k)
  have hN : 0 < (2 ^ k : ℝ) := by positivity
  have hsqrt : 1 ≤ Real.sqrt (k : ℝ) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hk
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hk1
  have hfirst :
      (k : ℝ) / (2 ^ k : ℝ) ^ 3 ≤
        Real.sqrt (k : ℝ) / (2 ^ k : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (k : ℝ) * (2 ^ k : ℝ) ^ 2 ≤
        Real.sqrt (k : ℝ) * (2 ^ k : ℝ) ^ 3 := by
      have hkdiv : (k : ℝ) ≤
          Real.sqrt (k : ℝ) * (2 ^ k : ℝ) := by
        calc
          (k : ℝ) ≤ (2 ^ k : ℝ) := hkN
          _ ≤ Real.sqrt (k : ℝ) * (2 ^ k : ℝ) := by
            nlinarith
      nlinarith [sq_nonneg ((2 ^ k : ℝ) ^ 2)]
    exact this
  calc
    ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ) ≤
        (k : ℝ) / (2 ^ k : ℝ) ^ 3 +
          Real.sqrt (k : ℝ) / (2 ^ k : ℝ) ^ 2 := hb
    _ ≤ 2 * (Real.sqrt (k : ℝ) / (2 ^ k : ℝ) ^ 2) := by
      linarith
    _ = 2 * Real.sqrt (k : ℝ) / (4 ^ k : ℝ) := by
      rw [show (4 ^ k : ℝ) = (2 ^ k : ℝ) ^ 2 by
        norm_num [← pow_mul]]
      ring

/-- Frozen B3 first asymptotic conclusion. -/
theorem bias_mixedSpider_tuned_isBigO :
    (fun k : ℕ =>
      ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ)) =O[Filter.atTop]
      (fun k : ℕ => Real.sqrt (k : ℝ) / (4 ^ k : ℝ)) := by
  apply (Asymptotics.IsBigOWith.of_bound ?_).isBigO
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
  have hkpos : 0 < k := by omega
  have hbnonneg :
      0 ≤ ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ) := by
    positivity
  have hg :
      0 ≤ Real.sqrt (k : ℝ) / (4 ^ k : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hbnonneg,
    Real.norm_eq_abs, abs_of_nonneg hg]
  simpa [mul_div_assoc] using
    cast_bias_mixedSpider_tuned_le_two_sqrt_div_four_pow hkpos

end GreedyUniformity
