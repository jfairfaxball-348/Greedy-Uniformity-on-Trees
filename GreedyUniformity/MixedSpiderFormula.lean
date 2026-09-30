module

public import GreedyUniformity.MixedSpiderMIS
public import Mathlib.Data.Nat.Choose.Sum

public section

open scoped BigOperators

namespace GreedyUniformity

/-- N = 2^k, the number of non-centre maximal independent sets. -/
def mixedSpiderN (k : ℕ) : ℕ := 2 ^ k

/-- The denominator l + 2j + 1 appearing in the exact mixed-spider law. -/
def mixedSpiderDenom (l j : ℕ) : ℕ := l + 2 * j + 1

/-- Frozen B2 closed form for the centre-containing maximal independent set. -/
noncomputable def mixedSpiderCenterFormula (k l : ℕ) : ℚ :=
  (1 / (mixedSpiderN k : ℚ)) *
    ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℚ) / (mixedSpiderDenom l j : ℚ)

/-- Frozen B2 closed form for a particular non-centre maximal independent set
whose arm pattern contains exactly j inner vertices. -/
noncomputable def mixedSpiderNoncenterFormula (k l j : ℕ) : ℚ :=
  (1 / (mixedSpiderN k : ℚ)) *
    (1 - 1 / (mixedSpiderDenom l j : ℚ))

theorem mixedSpiderN_pos (k : ℕ) : 0 < mixedSpiderN k := by
  simp [mixedSpiderN]

theorem mixedSpiderDenom_pos (l j : ℕ) : 0 < mixedSpiderDenom l j := by
  simp [mixedSpiderDenom]

/-- The non-centre closed form in the exact quotient presentation frozen in B2. -/
theorem mixedSpiderNoncenterFormula_eq
    (k l j : ℕ) :
    mixedSpiderNoncenterFormula k l j =
      (l + 2 * j : ℚ) /
        ((2 ^ k : ℚ) * (l + 2 * j + 1 : ℚ)) := by
  have hN : (2 ^ k : ℚ) ≠ 0 := by positivity
  have hd : (l + 2 * j + 1 : ℚ) ≠ 0 := by positivity
  simp only [mixedSpiderNoncenterFormula, mixedSpiderN, mixedSpiderDenom]
  push_cast
  field_simp
  ring

/-- Subsets of the k arms group by their cardinality with binomial
multiplicity. This is the exact multiplicity statement used in B2. -/
theorem mixedSpider_sum_powerset_by_card
    (k : ℕ) (f : ℕ → ℚ) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, f S.card =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * f j := by
  simpa using
    (Finset.sum_powerset_apply_card (x := (Finset.univ : Finset (Fin k))) f)

/-- There are exactly binom(k,j) arm patterns of type j. -/
theorem mixedSpider_armPatterns_card
    (k j : ℕ) :
    ((Finset.univ : Finset (Finset (Fin k))).filter
      (fun S => S.card = j)).card = k.choose j := by
  simpa using Finset.card_powersetCard j (Finset.univ : Finset (Fin k))

/-- The centre formula can equivalently be written as an average over all
2^k arm patterns. This is the finite form most convenient for the order proof. -/
theorem mixedSpiderCenterFormula_eq_powerset_average
    (k l : ℕ) :
    mixedSpiderCenterFormula k l =
      (1 / (mixedSpiderN k : ℚ)) *
        ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
          1 / (mixedSpiderDenom l S.card : ℚ) := by
  rw [mixedSpiderCenterFormula]
  congr 1
  rw [mixedSpider_sum_powerset_by_card k
    (fun j => 1 / (mixedSpiderDenom l j : ℚ))]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end GreedyUniformity
