import GreedyUniformity.Model

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

@[simp]
theorem rank_vertexAt (π : Equiv.Perm V) (i : Fin (Fintype.card V)) :
    rank π (vertexAt π i) = i := by
  simp [rank, vertexAt, baseEquiv]

@[simp]
theorem vertexAt_rank (π : Equiv.Perm V) (v : V) :
    vertexAt π (rank π v) = v := by
  simp [rank, vertexAt, baseEquiv]

theorem rank_injective (π : Equiv.Perm V) :
    Function.Injective (rank π) := by
  intro a b h
  have := congrArg (vertexAt π) h
  simpa using this

theorem subset_greedyStep (I : Finset V) (v : V) :
    I ⊆ greedyStep G I v := by
  classical
  simp only [greedyStep]
  split
  · exact fun _ h => h
  · exact Finset.subset_insert v I

theorem greedyStep_eq_self_of_neighbor {I : Finset V} {v : V}
    (h : ∃ u ∈ I, G.Adj u v) :
    greedyStep G I v = I := by
  classical
  simp [greedyStep, h]

theorem greedyStep_eq_insert_of_no_neighbor {I : Finset V} {v : V}
    (h : ¬ ∃ u ∈ I, G.Adj u v) :
    greedyStep G I v = insert v I := by
  classical
  simp [greedyStep, h]

theorem mem_greedyStep_iff {I : Finset V} {v w : V} :
    w ∈ greedyStep G I v ↔
      w ∈ I ∨ (w = v ∧ ¬ ∃ u ∈ I, G.Adj u v) := by
  classical
  by_cases h : ∃ u ∈ I, G.Adj u v
  · simp [greedyStep, h]
  · simp [greedyStep, h, eq_comm, or_comm]

theorem greedyPrefix_step (π : Equiv.Perm V) {n : ℕ}
    (hn : n < Fintype.card V) :
    greedyPrefix G π (n + 1) =
      greedyStep G (greedyPrefix G π n) (vertexAt π ⟨n, hn⟩) := by
  simp [greedyPrefix, hn]


/-- The scan prefix contains only already processed vertices, is independent,
and every rejected processed vertex has an earlier selected neighbour. -/
theorem greedyPrefix_spec (π : Equiv.Perm V) {n : ℕ}
    (hn : n ≤ Fintype.card V) :
    (∀ v ∈ greedyPrefix G π n, (rank π v).val < n) ∧
    IsIndependent G (greedyPrefix G π n) ∧
    (∀ w, (rank π w).val < n → w ∉ greedyPrefix G π n →
      ∃ u ∈ greedyPrefix G π n, G.Adj u w ∧ Precedes π u w) := by
  induction n with
  | zero =>
      simp [greedyPrefix, IsIndependent]
  | succ n ih =>
      have hnlt : n < Fintype.card V := by omega
      have hprev := ih (by omega)
      let v : V := vertexAt π ⟨n, hnlt⟩
      have hrankv : (rank π v).val = n := by
        simp [v]
      rw [greedyPrefix_step G π hnlt]
      by_cases hblock : ∃ u ∈ greedyPrefix G π n, G.Adj u v
      · rw [greedyStep_eq_self_of_neighbor G hblock]
        refine ⟨?_, hprev.2.1, ?_⟩
        · intro w hw
          have := hprev.1 w hw
          omega
        · intro w hrw hnot
          by_cases hlt : (rank π w).val < n
          · exact hprev.2.2 w hlt hnot
          · have heq : (rank π w).val = n := by omega
            have hrv : rank π w = rank π v := by
              apply Fin.ext
              simpa [hrankv] using heq
            have hwv : w = v := rank_injective π hrv
            subst w
            obtain ⟨u, hu, hadj⟩ := hblock
            refine ⟨u, hu, hadj, ?_⟩
            have hru := hprev.1 u hu
            show (rank π u).val < (rank π v).val
            omega
      · rw [greedyStep_eq_insert_of_no_neighbor G hblock]
        refine ⟨?_, ?_, ?_⟩
        · intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with rfl | hw
          · omega
          · have := hprev.1 w hw
            omega
        · intro a ha b hb
          simp only [Finset.mem_insert] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact G.loopless.irrefl _
          · intro hadj
            exact hblock ⟨b, hb, G.symm.symm hadj⟩
          · intro hadj
            exact hblock ⟨a, ha, hadj⟩
          · exact hprev.2.1 ha hb
        · intro w hrw hnot
          have hwv : w ≠ v := by
            intro hwv
            subst w
            exact hnot (Finset.mem_insert_self _ _)
          have hnotI : w ∉ greedyPrefix G π n := by
            intro hw
            exact hnot (Finset.mem_insert_of_mem hw)
          have hlt : (rank π w).val < n := by
            by_contra hnl
            have heq : (rank π w).val = n := by omega
            have hrv : rank π w = rank π v := by
              apply Fin.ext
              simpa [hrankv] using heq
            exact hwv (rank_injective π hrv)
          obtain ⟨u, hu, hadj, hprec⟩ := hprev.2.2 w hlt hnotI
          exact ⟨u, Finset.mem_insert_of_mem hu, hadj, hprec⟩

/-- Every concrete permutation scan produces a maximal independent set and
satisfies the exact earlier-neighbour certificate. -/
theorem greedyOutput_priorityCertificate (π : Equiv.Perm V) :
    PriorityCertificate G (greedyOutput G π) π := by
  have hs := greedyPrefix_spec G π (n := Fintype.card V) (le_rfl)
  have hout :
      ∀ w, w ∉ greedyOutput G π →
        ∃ u ∈ greedyOutput G π, G.Adj u w ∧ Precedes π u w := by
    intro w hnot
    have hwlt : (rank π w).val < Fintype.card V := (rank π w).isLt
    simpa [greedyOutput] using hs.2.2 w hwlt (by simpa [greedyOutput] using hnot)
  refine ⟨?_, hout⟩
  refine ⟨Finset.subset_univ _, ?_, ?_⟩
  · simpa [greedyOutput] using hs.2.1
  · intro w _ hnot
    obtain ⟨u, hu, hadj, _⟩ := hout w hnot
    exact ⟨u, hu, hadj⟩

/-- For a fixed total priority order the priority certificate is unique. -/
theorem priorityCertificate_unique (π : Equiv.Perm V) {I J : Finset V}
    (hI : PriorityCertificate G I π) (hJ : PriorityCertificate G J π) :
    I = J := by
  have hindI : IsIndependent G I := hI.1.2.1
  have hindJ : IsIndependent G J := hJ.1.2.1
  have hmem : ∀ n : ℕ, ∀ v : V, (rank π v).val = n → (v ∈ I ↔ v ∈ J) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro v hvn
        constructor
        · intro hvI
          by_contra hvJ
          obtain ⟨u, huJ, hadj, hprec⟩ := hJ.2 hvJ
          have hprec' : (rank π u).val < (rank π v).val := hprec
          have hlt : (rank π u).val < n := by
            omega
          have huI : u ∈ I := (ih _ hlt u rfl).2 huJ
          exact (hindI huI hvI) hadj
        · intro hvJ
          by_contra hvI
          obtain ⟨u, huI, hadj, hprec⟩ := hI.2 hvI
          have hprec' : (rank π u).val < (rank π v).val := hprec
          have hlt : (rank π u).val < n := by
            omega
          have huJ : u ∈ J := (ih _ hlt u rfl).1 huI
          exact (hindJ huJ hvJ) hadj
  apply Finset.ext
  intro v
  exact hmem (rank π v).val v rfl

/-- Formal bridge between one-pass greedy scanning and the iid-priority
certificate used in the informal proof. -/
theorem priorityCertificate_iff_greedyOutput_eq (π : Equiv.Perm V)
    (I : Finset V) :
    PriorityCertificate G I π ↔ greedyOutput G π = I := by
  constructor
  · intro hI
    exact (priorityCertificate_unique G π hI
      (greedyOutput_priorityCertificate G π)).symm
  · intro h
    rw [← h]
    exact greedyOutput_priorityCertificate G π

@[simp]
theorem mem_fibre (π : Equiv.Perm V) (I : Finset V) :
    π ∈ fibre G I ↔ greedyOutput G π = I := by
  classical
  simp [fibre]

theorem mem_fibre_iff_certificate (π : Equiv.Perm V) (I : Finset V) :
    π ∈ fibre G I ↔ PriorityCertificate G I π := by
  rw [mem_fibre, ← priorityCertificate_iff_greedyOutput_eq]


end GreedyUniformity
