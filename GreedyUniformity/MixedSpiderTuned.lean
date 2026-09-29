import GreedyUniformity.MixedSpiderFormula

open scoped BigOperators

namespace GreedyUniformity

/-- Tuned direct-leaf count l = 2^k-k. -/
def mixedSpiderTunedL (k : ℕ) : ℕ := 2 ^ k - k

/-- A = 2^k+1 in the Stage-3 proof. -/
def mixedSpiderA (k : ℕ) : ℚ := (2 ^ k : ℚ) + 1

/-- W = 2j-k in the Stage-3 binomial expectation. -/
def mixedSpiderW (k j : ℕ) : ℚ := 2 * (j : ℚ) - (k : ℚ)

/-- Finite exact expectation under J ~ Bin(k,1/2). -/
noncomputable def binomialAverageQ (k : ℕ) (f : ℕ → ℚ) : ℚ :=
  (1 / (2 ^ k : ℚ)) *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * f j

/-- Elementary growth fact needed to cast the tuned natural-number subtraction. -/
theorem mixedSpider_nat_lt_two_pow (k : ℕ) : k < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ k := by positivity
      omega

theorem mixedSpiderTunedL_pos (k : ℕ) :
    0 < mixedSpiderTunedL k := by
  exact Nat.sub_pos_of_lt (mixedSpider_nat_lt_two_pow k)

/-- For j<=k, the tuned denominator is exactly A+W after casting to Q. -/
theorem mixedSpider_tuned_denom_eq
    {k j : ℕ} (hj : j ≤ k) :
    (mixedSpiderDenom (mixedSpiderTunedL k) j : ℚ) =
      mixedSpiderA k + mixedSpiderW k j := by
  have hk : k ≤ 2 ^ k := Nat.le_of_lt (mixedSpider_nat_lt_two_pow k)
  simp only [mixedSpiderDenom, mixedSpiderTunedL, mixedSpiderA, mixedSpiderW]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_sub hk]
  norm_num
  ring

/-- The binomial average of W is zero. -/
theorem binomialAverageQ_W_eq_zero
    {k : ℕ} (hk : 0 < k) :
    binomialAverageQ k (mixedSpiderW k) = 0 := by
  have hchoose :
      (∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ)) =
        (2 ^ k : ℚ) := by
    exact_mod_cast Nat.sum_range_choose k
  have hjchoose :
      (∑ j ∈ Finset.range (k + 1),
          (j : ℚ) * (k.choose j : ℚ)) =
        (k * 2 ^ (k - 1) : ℕ) := by
    exact_mod_cast Nat.sum_range_mul_choose k
  have hpow :
      (2 : ℚ) * (2 ^ (k - 1) : ℚ) = (2 ^ k : ℚ) := by
    cases k with
    | zero => simp at hk
    | succ k =>
        simpa [pow_succ, mul_comm]
  have hsum :
      (∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℚ) * mixedSpiderW k j) = 0 := by
    calc
      (∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℚ) * mixedSpiderW k j) =
          ∑ j ∈ Finset.range (k + 1),
            (2 * ((j : ℚ) * (k.choose j : ℚ)) -
              (k : ℚ) * (k.choose j : ℚ)) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp only [mixedSpiderW]
              ring
      _ =
          2 * (∑ j ∈ Finset.range (k + 1),
            (j : ℚ) * (k.choose j : ℚ)) -
          (k : ℚ) * (∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℚ)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 0 := by
        rw [hchoose, hjchoose]
        push_cast
        rw [← hpow]
        ring
  simp [binomialAverageQ, hsum]

/-- In tuned parameters, the centre closed form is E[1/(A+W)]. -/
theorem mixedSpiderCenterFormula_tuned_eq_average
    {k : ℕ} (hk : 0 < k) :
    mixedSpiderCenterFormula k (mixedSpiderTunedL k) =
      binomialAverageQ k
        (fun j => 1 / (mixedSpiderA k + mixedSpiderW k j)) := by
  unfold mixedSpiderCenterFormula binomialAverageQ mixedSpiderN
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ k := by
    simpa [Finset.mem_range] using hj
  rw [mixedSpider_tuned_denom_eq hjle]
  ring

/-- Frozen equation (7.1): the deviation of a type-j non-centre formula from
the uniform mass 1/A is W/(N*A*(A+W)). -/
theorem mixedSpiderNoncenterFormula_tuned_sub_uniform
    {k j : ℕ} (hk : 0 < k) (hj : j ≤ k) :
    mixedSpiderNoncenterFormula k (mixedSpiderTunedL k) j -
        1 / mixedSpiderA k =
      mixedSpiderW k j /
        ((2 ^ k : ℚ) * mixedSpiderA k *
          (mixedSpiderA k + mixedSpiderW k j)) := by
  have hdenNat :
      0 < mixedSpiderDenom (mixedSpiderTunedL k) j :=
    mixedSpiderDenom_pos _ _
  have hden :
      mixedSpiderA k + mixedSpiderW k j ≠ 0 := by
    rw [← mixedSpider_tuned_denom_eq hj]
    exact_mod_cast (Nat.ne_of_gt hdenNat)
  have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
  have hA : mixedSpiderA k ≠ 0 := by
    unfold mixedSpiderA
    positivity
  unfold mixedSpiderNoncenterFormula
  rw [mixedSpider_tuned_denom_eq hj]
  simp only [mixedSpiderN]
  push_cast
  field_simp [hN, hA, hden]
  unfold mixedSpiderA
  ring

end GreedyUniformity
