import GreedyUniformity.MixedSpiderBias
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open scoped BigOperators

namespace GreedyUniformity

/-- Exact unnormalised second moment of W=2J-k under binomial weights. -/
theorem sum_choose_mul_mixedSpiderW_sq (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℚ) * mixedSpiderW k j ^ 2) =
      (k : ℚ) * (2 ^ k : ℚ) := by
  induction k with
  | zero =>
      simp [mixedSpiderW]
  | succ k ih =>
      let f : ℕ → ℕ → ℚ := fun i j => ((i : ℚ) - (j : ℚ)) ^ 2
      have hsplit :=
        Finset.sum_choose_succ_mul (R := ℚ) f k
      have hleft :
          (∑ i ∈ Finset.range (k + 2),
              ((k + 1).choose i : ℚ) * mixedSpiderW (k + 1) i ^ 2) =
            ∑ i ∈ Finset.range (k + 2),
              ((k + 1).choose i : ℚ) * f i (k + 1 - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hile : i ≤ k + 1 := by
          simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
        simp only [f, mixedSpiderW]
        rw [Nat.cast_sub hile]
        ring
      rw [hleft, hsplit]
      rw [← Finset.sum_add_distrib]
      calc
        (∑ i ∈ Finset.range (k + 1),
            ((k.choose i : ℚ) * f i (k + 1 - i) +
              (k.choose i : ℚ) * f (i + 1) (k - i))) =
            ∑ i ∈ Finset.range (k + 1),
              (k.choose i : ℚ) *
                (2 * mixedSpiderW k i ^ 2 + 2) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hile : i ≤ k := by
                    simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
                  have hile' : i ≤ k + 1 := Nat.le_trans hile (Nat.le_succ k)
                  simp only [f, mixedSpiderW]
                  rw [Nat.cast_sub hile, Nat.cast_sub hile']
                  push_cast
                  ring
        _ = 2 *
              (∑ i ∈ Finset.range (k + 1),
                (k.choose i : ℚ) * mixedSpiderW k i ^ 2) +
            2 *
              (∑ i ∈ Finset.range (k + 1),
                (k.choose i : ℚ)) := by
                  simp_rw [mul_add]
                  rw [Finset.sum_add_distrib]
                  rw [Finset.mul_sum, Finset.mul_sum]
                  apply congrArg₂ (· + ·)
                  · apply Finset.sum_congr rfl
                    intro i hi
                    ring
                  · apply Finset.sum_congr rfl
                    intro i hi
                    ring
        _ = 2 * ((k : ℚ) * (2 ^ k : ℚ)) +
            2 * (2 ^ k : ℚ) := by
              rw [ih]
              have hchoose :
                  (∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ)) =
                    (2 ^ k : ℚ) := by
                exact_mod_cast Nat.sum_range_choose k
              rw [hchoose]
        _ = ((k + 1 : ℕ) : ℚ) * (2 ^ (k + 1) : ℚ) := by
              push_cast
              rw [pow_succ]
              ring

/-- Exact binomial variance identity E[W^2]=k. -/
theorem binomialAverageQ_W_sq (k : ℕ) :
    binomialAverageQ k (fun j => mixedSpiderW k j ^ 2) = (k : ℚ) := by
  unfold binomialAverageQ
  rw [sum_choose_mul_mixedSpiderW_sq]
  have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
  field_simp [hN]

/-- Real version of W, used only for the square-root bound. -/
def mixedSpiderWReal (k j : ℕ) : ℝ :=
  2 * (j : ℝ) - (k : ℝ)

/-- The unnormalised first absolute binomial moment. -/
noncomputable def mixedSpiderAbsMomentSum (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (k.choose j : ℝ) * |mixedSpiderWReal k j|

theorem sum_choose_mul_mixedSpiderWReal_sq (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * mixedSpiderWReal k j ^ 2) =
      (k : ℝ) * (2 ^ k : ℝ) := by
  exact_mod_cast sum_choose_mul_mixedSpiderW_sq k

/-- Finite Cauchy-Schwarz gives E|W| <= sqrt(k). -/
theorem mixedSpider_absMoment_average_le_sqrt (k : ℕ) :
    mixedSpiderAbsMomentSum k / (2 ^ k : ℝ) ≤ Real.sqrt (k : ℝ) := by
  let s := Finset.range (k + 1)
  let r : ℕ → ℝ := fun j =>
    (k.choose j : ℝ) * |mixedSpiderWReal k j|
  let f : ℕ → ℝ := fun j => (k.choose j : ℝ)
  let g : ℕ → ℝ := fun j =>
    (k.choose j : ℝ) * mixedSpiderWReal k j ^ 2
  have hcs :
      (∑ j ∈ s, r j) ^ 2 ≤
        (∑ j ∈ s, f j) * ∑ j ∈ s, g j := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    · intro j hj
      dsimp [f]
      positivity
    · intro j hj
      dsimp [g]
      positivity
    · intro j hj
      dsimp [r, f, g]
      rw [sq_abs]
      ring
  have hsumf : (∑ j ∈ s, f j) = (2 ^ k : ℝ) := by
    dsimp [s, f]
    exact_mod_cast Nat.sum_range_choose k
  have hsumg : (∑ j ∈ s, g j) = (k : ℝ) * (2 ^ k : ℝ) := by
    dsimp [s, g]
    exact sum_choose_mul_mixedSpiderWReal_sq k
  have hsums :
      (∑ j ∈ s, r j) = mixedSpiderAbsMomentSum k := by
    rfl
  rw [hsumf, hsumg, hsums] at hcs
  have hN : 0 < (2 ^ k : ℝ) := by positivity
  have hsq :
      (mixedSpiderAbsMomentSum k / (2 ^ k : ℝ)) ^ 2 ≤ (k : ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hN)).2
    nlinarith
  exact Real.le_sqrt_of_sq_le hsq

/-- Casting the rational binomial absolute average agrees with the real
normalised absolute-moment sum. -/
theorem cast_binomialAverageQ_abs_W (k : ℕ) :
    ((binomialAverageQ k (fun j => |mixedSpiderW k j|) : ℚ) : ℝ) =
      mixedSpiderAbsMomentSum k / (2 ^ k : ℝ) := by
  unfold binomialAverageQ mixedSpiderAbsMomentSum
  push_cast
  simp only [mixedSpiderW, mixedSpiderWReal, Rat.cast_abs]
  ring

end GreedyUniformity
