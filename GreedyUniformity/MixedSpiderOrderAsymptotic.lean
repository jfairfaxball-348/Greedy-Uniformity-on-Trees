module

public import GreedyUniformity.MixedSpiderAsymptotic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace GreedyUniformity

/-- Number of vertices in the tuned mixed-spider family. -/
def mixedSpiderTunedOrder (k : ℕ) : ℕ :=
  2 ^ k + k + 1

theorem mixedSpider_tuned_vertex_card (k : ℕ) :
    Fintype.card (MixedSpiderVertex k (mixedSpiderTunedL k)) =
      mixedSpiderTunedOrder k := by
  rw [mixedSpiderVertex_card]
  unfold mixedSpiderTunedL mixedSpiderTunedOrder
  have hk : k ≤ 2 ^ k := Nat.le_of_lt (mixedSpider_nat_lt_two_pow k)
  omega

theorem two_pow_le_mixedSpiderTunedOrder (k : ℕ) :
    2 ^ k ≤ mixedSpiderTunedOrder k := by
  unfold mixedSpiderTunedOrder
  omega

theorem mixedSpiderTunedOrder_le_two_mul_two_pow
    {k : ℕ} (hk : 0 < k) :
    mixedSpiderTunedOrder k ≤ 2 * 2 ^ k := by
  unfold mixedSpiderTunedOrder
  have hlt := mixedSpider_nat_lt_two_pow k
  omega

theorem sqrt_k_le_sqrt_log_order_div_sqrt_log_two
    {k : ℕ} (hk : 0 < k) :
    Real.sqrt (k : ℝ) ≤
      Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
        Real.sqrt (Real.log 2) := by
  have hNpos : 0 < (2 ^ k : ℝ) := by positivity
  have hnpos : 0 < (mixedSpiderTunedOrder k : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt (lt_of_lt_of_le
      (pow_pos (by omega : 0 < (2 : ℕ)) k)
      (two_pow_le_mixedSpiderTunedOrder k))
  have hNle :
      (2 ^ k : ℝ) ≤ (mixedSpiderTunedOrder k : ℝ) := by
    exact_mod_cast two_pow_le_mixedSpiderTunedOrder k
  have hlogle :
      Real.log (2 ^ k : ℝ) ≤
        Real.log (mixedSpiderTunedOrder k : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hNpos hnpos hNle
  have hlogpow :
      Real.log (2 ^ k : ℝ) = (k : ℝ) * Real.log 2 := by
    simpa using Real.log_pow (2 : ℝ) k
  rw [hlogpow] at hlogle
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hsqrt2 : 0 < Real.sqrt (Real.log 2) := by positivity
  have hsqrtle :
      Real.sqrt ((k : ℝ) * Real.log 2) ≤
        Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) :=
    Real.sqrt_le_sqrt hlogle
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  rw [Real.sqrt_mul hk0] at hsqrtle
  exact (le_div_iff₀ hsqrt2).2 hsqrtle

theorem inv_two_pow_sq_le_four_div_order_sq
    {k : ℕ} (hk : 0 < k) :
    1 / (2 ^ k : ℝ) ^ 2 ≤
      4 / (mixedSpiderTunedOrder k : ℝ) ^ 2 := by
  have hNpos : 0 < (2 ^ k : ℝ) := by positivity
  have hnpos : 0 < (mixedSpiderTunedOrder k : ℝ) := by
    unfold mixedSpiderTunedOrder
    positivity
  have hnle :
      (mixedSpiderTunedOrder k : ℝ) ≤ 2 * (2 ^ k : ℝ) := by
    exact_mod_cast mixedSpiderTunedOrder_le_two_mul_two_pow hk
  have hsq :
      (mixedSpiderTunedOrder k : ℝ) ^ 2 ≤
        4 * (2 ^ k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      ((mixedSpiderTunedOrder k : ℝ) - 2 * (2 ^ k : ℝ))]
  apply (le_div_iff₀ (sq_pos_of_pos hnpos)).2
  calc
    (1 / (2 ^ k : ℝ) ^ 2) *
        (mixedSpiderTunedOrder k : ℝ) ^ 2 =
        (mixedSpiderTunedOrder k : ℝ) ^ 2 /
          (2 ^ k : ℝ) ^ 2 := by ring
    _ ≤ 4 := by
      exact (div_le_iff₀ (sq_pos_of_pos hNpos)).2 (by
        simpa [mul_comm] using hsq)

theorem sqrt_k_div_four_pow_le_order_scale
    {k : ℕ} (hk : 0 < k) :
    Real.sqrt (k : ℝ) / (4 ^ k : ℝ) ≤
      (4 / Real.sqrt (Real.log 2)) *
        (Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
          (mixedSpiderTunedOrder k : ℝ) ^ 2) := by
  have hsqrt :=
    sqrt_k_le_sqrt_log_order_div_sqrt_log_two hk
  have hden := inv_two_pow_sq_le_four_div_order_sq hk
  have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := by positivity
  have hlog0 :
      0 ≤ Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
        Real.sqrt (Real.log 2) := by positivity
  have hmul :=
    mul_le_mul hsqrt hden (by positivity) hlog0
  have hfour :
      (4 ^ k : ℝ) = (2 ^ k : ℝ) ^ 2 := by
    calc
      (4 ^ k : ℝ) = (((2 : ℝ) ^ 2) ^ k) := by norm_num
      _ = (2 : ℝ) ^ (2 * k) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (k * 2) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ k) ^ 2 := by rw [pow_mul]
  rw [hfour]
  calc
    Real.sqrt (k : ℝ) / (2 ^ k : ℝ) ^ 2 =
        Real.sqrt (k : ℝ) * (1 / (2 ^ k : ℝ) ^ 2) := by ring
    _ ≤
        (Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
          Real.sqrt (Real.log 2)) *
        (4 / (mixedSpiderTunedOrder k : ℝ) ^ 2) := hmul
    _ =
        (4 / Real.sqrt (Real.log 2)) *
          (Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
            (mixedSpiderTunedOrder k : ℝ) ^ 2) := by ring

/-- Frozen B3 reformulation along n_k=2^k+k+1. -/
theorem bias_mixedSpider_tuned_isBigO_sqrt_log_order_div_order_sq :
    (fun k : ℕ =>
      ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ)) =O[Filter.atTop]
      (fun k : ℕ =>
        Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
          (mixedSpiderTunedOrder k : ℝ) ^ 2) := by
  apply Asymptotics.IsBigO.of_bound
    (8 / Real.sqrt (Real.log 2) : ℝ)
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
  have hkpos : 0 < k := by omega
  have hbnonnegQ :
      (0 : ℚ) ≤ bias (mixedSpider k (mixedSpiderTunedL k)) := by
    unfold bias
    positivity
  have hbnonneg :
      0 ≤ ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ) := by
    exact_mod_cast hbnonnegQ
  have htarget :
      0 ≤ Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
        (mixedSpiderTunedOrder k : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hbnonneg,
    Real.norm_eq_abs, abs_of_nonneg htarget]
  have hb :=
    cast_bias_mixedSpider_tuned_le_two_sqrt_div_four_pow hkpos
  have hs :=
    sqrt_k_div_four_pow_le_order_scale hkpos
  calc
    ((bias (mixedSpider k (mixedSpiderTunedL k)) : ℚ) : ℝ) ≤
        2 * Real.sqrt (k : ℝ) / (4 ^ k : ℝ) := hb
    _ = 2 * (Real.sqrt (k : ℝ) / (4 ^ k : ℝ)) := by ring
    _ ≤ 2 *
        ((4 / Real.sqrt (Real.log 2)) *
          (Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
            (mixedSpiderTunedOrder k : ℝ) ^ 2)) := by
              gcongr
    _ =
        (8 / Real.sqrt (Real.log 2)) *
          (Real.sqrt (Real.log (mixedSpiderTunedOrder k : ℝ)) /
            (mixedSpiderTunedOrder k : ℝ) ^ 2) := by ring

end GreedyUniformity
