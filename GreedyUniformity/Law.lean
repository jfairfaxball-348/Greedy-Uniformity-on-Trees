import GreedyUniformity.Scan

open scoped BigOperators

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

@[simp]
theorem mem_maximalIndependentSets (I : Finset V) :
    I ∈ maximalIndependentSets G ↔ IsMaximalIndependent G I := by
  classical
  simp [maximalIndependentSets]

theorem greedyOutput_isMaximalIndependent (π : Equiv.Perm V) :
    IsMaximalIndependent G (greedyOutput G π) :=
  (greedyOutput_priorityCertificate G π).1

theorem maximalIndependentSets_nonempty :
    (maximalIndependentSets G).Nonempty := by
  classical
  refine ⟨greedyOutput G (1 : Equiv.Perm V), ?_⟩
  simp [greedyOutput_isMaximalIndependent]

theorem fibre_eq_empty_of_not_maximal {I : Finset V}
    (hI : ¬ IsMaximalIndependent G I) :
    fibre G I = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro π hπ
  apply hI
  have hout : greedyOutput G π = I := (mem_fibre G π I).mp hπ
  rw [← hout]
  exact greedyOutput_isMaximalIndependent G π

theorem fibreCount_eq_zero_of_not_maximal {I : Finset V}
    (hI : ¬ IsMaximalIndependent G I) :
    fibreCount G I = 0 := by
  rw [fibreCount, fibre_eq_empty_of_not_maximal G hI]
  simp

/-- The literal greedy fibres partition all vertex permutations. -/
theorem sum_fibreCount_maximalIndependentSets :
    ∑ I ∈ maximalIndependentSets G, fibreCount G I =
      Nat.factorial (Fintype.card V) := by
  classical
  have hmap :
      ∀ π ∈ (Finset.univ : Finset (Equiv.Perm V)),
        greedyOutput G π ∈ maximalIndependentSets G := by
    intro π _
    simp [greedyOutput_isMaximalIndependent]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Equiv.Perm V)))
    (t := maximalIndependentSets G)
    (g := greedyOutput G)
    hmap
    (fun _ => (1 : ℕ))
  simpa [fibreCount, fibre, Fintype.card_perm] using h

theorem maximalIndependentSets_card_pos :
    0 < (maximalIndependentSets G).card :=
  Finset.card_pos.mpr (maximalIndependentSets_nonempty G)

theorem factorial_card_pos :
    0 < Nat.factorial (Fintype.card V) :=
  Nat.factorial_pos _

/-- Equality of the two laws is equivalent to constancy of the exact
permutation-fibre counts on maximal independent sets. -/
theorem uniformFibres_iff_greedyLawEqUniform :
    UniformFibres G ↔ GreedyLawEqUniform G := by
  classical
  constructor
  · intro hU I
    by_cases hI : IsMaximalIndependent G I
    · have hsum := sum_fibreCount_maximalIndependentSets G
      have hconst :
          ∑ J ∈ maximalIndependentSets G, fibreCount G J =
            (maximalIndependentSets G).card * fibreCount G I := by
        calc
          ∑ J ∈ maximalIndependentSets G, fibreCount G J =
              ∑ J ∈ maximalIndependentSets G, fibreCount G I := by
                apply Finset.sum_congr rfl
                intro J hJ
                exact hU ((mem_maximalIndependentSets G J).mp hJ) hI
          _ = (maximalIndependentSets G).card * fibreCount G I := by simp
      have hprod :
          (maximalIndependentSets G).card * fibreCount G I =
            Nat.factorial (Fintype.card V) := by
        rw [← hconst]
        exact hsum
      have hmQ : ((maximalIndependentSets G).card : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (maximalIndependentSets_card_pos G))
      have hfQ : (Nat.factorial (Fintype.card V) : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (factorial_card_pos G))
      rw [greedyProb, uniformProb, if_pos hI]
      field_simp
      exact_mod_cast hprod
    · rw [uniformProb, if_neg hI, greedyProb,
        fibreCount_eq_zero_of_not_maximal G hI]
      simp
  · intro hLaw I J hI hJ
    have hIeq := hLaw I
    have hJeq := hLaw J
    rw [uniformProb, if_pos hI] at hIeq
    rw [uniformProb, if_pos hJ] at hJeq
    have hprob : greedyProb G I = greedyProb G J := hIeq.trans hJeq.symm
    have hfQ : (Nat.factorial (Fintype.card V) : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (factorial_card_pos G))
    have hcast : (fibreCount G I : ℚ) = (fibreCount G J : ℚ) := by
      apply (div_right_inj hfQ).mp
      simpa [greedyProb] using hprob
    exact_mod_cast hcast

/-- Total variation distance between the exact greedy output law and the
uniform law on maximal independent sets. -/
noncomputable def bias (G : SimpleGraph V) : ℚ :=
  (1 / 2 : ℚ) *
    ∑ I ∈ maximalIndependentSets G, |greedyProb G I - uniformProb G I|

theorem bias_nonneg : 0 ≤ bias G := by
  classical
  unfold bias
  positivity

theorem bias_eq_zero_iff_greedyLawEqUniform :
    bias G = 0 ↔ GreedyLawEqUniform G := by
  classical
  constructor
  · intro hb
    have hsum :
        ∑ I ∈ maximalIndependentSets G,
            |greedyProb G I - uniformProb G I| = 0 := by
      have hhalf : (1 / 2 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp (by simpa [bias] using hb)).resolve_left hhalf
    have hterms :
        ∀ I ∈ maximalIndependentSets G,
          |greedyProb G I - uniformProb G I| = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun I _ => abs_nonneg (greedyProb G I - uniformProb G I))).mp hsum
    intro I
    by_cases hI : IsMaximalIndependent G I
    · have hi := hterms I ((mem_maximalIndependentSets G I).2 hI)
      simpa only [abs_eq_zero, sub_eq_zero] using hi
    · rw [uniformProb, if_neg hI, greedyProb,
        fibreCount_eq_zero_of_not_maximal G hI]
      simp
  · intro hLaw
    unfold bias
    have hzero :
        ∀ I ∈ maximalIndependentSets G,
          |greedyProb G I - uniformProb G I| = 0 := by
      intro I _
      rw [hLaw I, sub_self, abs_zero]
    rw [Finset.sum_eq_zero hzero]
    ring

theorem bias_eq_zero_iff_uniformFibres :
    bias G = 0 ↔ UniformFibres G := by
  rw [bias_eq_zero_iff_greedyLawEqUniform,
      ← uniformFibres_iff_greedyLawEqUniform]

end GreedyUniformity
