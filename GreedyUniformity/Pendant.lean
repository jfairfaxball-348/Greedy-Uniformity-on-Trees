module

public import GreedyUniformity.Counting

@[expose] public section

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

section Pendant

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def pendantLeaves (y z : V) : Finset V :=
  (G.neighborFinset y).erase z

def pendantR (y z : V) : Finset V :=
  Finset.univ \ insert y (pendantLeaves G y z)

def pendantF (y z : V) : Finset V :=
  (pendantR G y z).erase z

noncomputable def maximalIndependentSetsContaining (y : V) : Finset (Finset V) := by
  classical
  exact (maximalIndependentSets G).filter fun I => y ∈ I

noncomputable def maximalIndependentSetsExcluding (y : V) : Finset (Finset V) := by
  classical
  exact (maximalIndependentSets G).filter fun I => y ∉ I

@[simp] theorem mem_maximalIndependentSetsContaining_iff {y : V} {I : Finset V} :
    I ∈ maximalIndependentSetsContaining G y ↔
      IsMaximalIndependent G I ∧ y ∈ I := by
  classical
  simp [maximalIndependentSetsContaining, mem_maximalIndependentSets_iff]

@[simp] theorem mem_maximalIndependentSetsExcluding_iff {y : V} {I : Finset V} :
    I ∈ maximalIndependentSetsExcluding G y ↔
      IsMaximalIndependent G I ∧ y ∉ I := by
  classical
  simp [maximalIndependentSetsExcluding, mem_maximalIndependentSets_iff]

theorem mem_pendantLeaves_iff {y z w : V} :
    w ∈ pendantLeaves G y z ↔ w ≠ z ∧ G.Adj y w := by
  simp [pendantLeaves, SimpleGraph.mem_neighborFinset]

theorem mem_pendantR_iff {y z w : V} :
    w ∈ pendantR G y z ↔ w ≠ y ∧ w ∉ pendantLeaves G y z := by
  simp [pendantR, and_left_comm, and_assoc]

theorem mem_pendantF_iff {y z w : V} :
    w ∈ pendantF G y z ↔
      w ≠ z ∧ w ≠ y ∧ w ∉ pendantLeaves G y z := by
  simp [pendantF, mem_pendantR_iff, and_assoc]

theorem pendantF_not_adj_center {y z w : V}
    (hw : w ∈ pendantF G y z) :
    ¬ G.Adj y w := by
  intro hadj
  have hwz : w ≠ z := (mem_pendantF_iff G).1 hw |>.1
  have hwL : w ∈ pendantLeaves G y z :=
    (mem_pendantLeaves_iff G).2 ⟨hwz, hadj⟩
  exact ((mem_pendantF_iff G).1 hw).2.2 hwL

theorem degree_one_adj_unique {w y t : V}
    (hdeg : G.degree w = 1) (hwy : G.Adj w y) (hwt : G.Adj w t) :
    t = y := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hdeg
  rcases hdeg with ⟨a, ha, huniq⟩
  exact (huniq t hwt).trans (huniq y hwy).symm

theorem pendantLeaves_degree_one {y z w : V}
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hw : w ∈ pendantLeaves G y z) :
    G.degree w = 1 := by
  exact hleaf w ((mem_pendantLeaves_iff G).1 hw).2
    ((mem_pendantLeaves_iff G).1 hw).1

theorem pendantLeaves_unique_neighbor {y z w t : V}
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hw : w ∈ pendantLeaves G y z) (hwt : G.Adj w t) :
    t = y := by
  apply degree_one_adj_unique G (pendantLeaves_degree_one G hleaf hw)
  · exact G.adj_symm ((mem_pendantLeaves_iff G).1 hw).2
  · exact hwt

theorem maximalIndependentSetsContaining_card_eq_pendantF
    {y z : V} (hyz : G.Adj y z) :
    (maximalIndependentSetsContaining G y).card =
      (maximalIndependentSetsOn G (pendantF G y z)).card := by
  classical
  apply Finset.card_bij (fun I _ => I.erase y)
  · intro I hI
    have hIM := (mem_maximalIndependentSetsContaining_iff G).1 hI
    apply (mem_maximalIndependentSetsOn_iff G).2
    refine ⟨?_, isIndependent_mono G hIM.1.2.1 (Finset.erase_subset y I), ?_⟩
    · intro a ha
      have hae := Finset.mem_erase.mp ha
      apply (mem_pendantF_iff G).2
      refine ⟨?_, hae.1, ?_⟩
      · intro haz
        subst a
        exact hIM.1.2.1 hIM.2 hae.2 hyz
      · intro haL
        have haya : G.Adj y a := (mem_pendantLeaves_iff G).1 haL |>.2
        exact hIM.1.2.1 hIM.2 hae.2 haya
    · intro w hwF hwE
      have hwy : w ≠ y := (mem_pendantF_iff G).1 hwF |>.2.1
      have hwI : w ∉ I := by
        intro hw
        exact hwE (Finset.mem_erase.mpr ⟨hwy, hw⟩)
      rcases hIM.1.2.2 (by simp) hwI with ⟨a, haI, haw⟩
      have hay : a ≠ y := by
        intro hay
        subst a
        exact pendantF_not_adj_center G hwF haw
      exact ⟨a, Finset.mem_erase.mpr ⟨hay, haI⟩, haw⟩
  · intro I hI J hJ hEq
    have hi := (mem_maximalIndependentSetsContaining_iff G).1 hI |>.2
    have hj := (mem_maximalIndependentSetsContaining_iff G).1 hJ |>.2
    calc
      I = insert y (I.erase y) := (Finset.insert_erase hi).symm
      _ = insert y (J.erase y) := congrArg (insert y) hEq
      _ = J := Finset.insert_erase hj
  · intro A hA
    have hAM : IsMaximalIndependentOn G (pendantF G y z) A :=
      (mem_maximalIndependentSetsOn_iff G).1 hA
    let I : Finset V := insert y A
    have hIind : IsIndependent G I := by
      intro a ha b hb hab
      simp only [I, Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact G.irrefl hab
        · exact pendantF_not_adj_center G (hAM.1 hb) hab
      · rcases hb with rfl | hb
        · exact pendantF_not_adj_center G (hAM.1 ha) (G.adj_symm hab)
        · exact hAM.2.1 ha hb hab
    have hIM : IsMaximalIndependent G I := by
      refine ⟨by simp, hIind, ?_⟩
      intro w _ hwI
      by_cases hwy : G.Adj y w
      · exact ⟨y, by simp [I], hwy⟩
      · have hwyne : w ≠ y := by
          intro h
          subst w
          exact hwI (by simp [I])
        have hwz : w ≠ z := by
          intro h
          subst w
          exact hwy hyz
        have hwL : w ∉ pendantLeaves G y z := by
          intro hwL
          exact hwy ((mem_pendantLeaves_iff G).1 hwL |>.2)
        have hwF : w ∈ pendantF G y z :=
          (mem_pendantF_iff G).2 ⟨hwz, hwyne, hwL⟩
        have hwA : w ∉ A := by
          intro hwA
          exact hwI (by simp [I, hwA])
        rcases hAM.2.2 hwF hwA with ⟨a, haA, haw⟩
        exact ⟨a, by simp [I, haA], haw⟩
    refine ⟨I, (mem_maximalIndependentSetsContaining_iff G).2
      ⟨hIM, by simp [I]⟩, ?_⟩
    ext a
    simp only [I, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hay, ha | ha⟩
      · exact (hay ha).elim
      · exact ha
    · intro ha
      exact ⟨fun h => ((mem_pendantF_iff G).1 (hAM.1 ha)).2.1 h,
        Or.inr ha⟩

theorem leaf_forced_into_maximal_of_center_absent
    {y z l : V}
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    {I : Finset V} (hI : IsMaximalIndependent G I)
    (hyI : y ∉ I) (hl : l ∈ pendantLeaves G y z) :
    l ∈ I := by
  by_contra hlI
  rcases hI.2.2 (by simp) hlI with ⟨a, haI, hal⟩
  have hay : a = y :=
    pendantLeaves_unique_neighbor G hleaf hl (G.adj_symm hal)
  exact hyI (hay ▸ haI)

theorem maximalIndependentSetsExcluding_card_eq_pendantR
    {y z : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hL : (pendantLeaves G y z).Nonempty) :
    (maximalIndependentSetsExcluding G y).card =
      (maximalIndependentSetsOn G (pendantR G y z)).card := by
  classical
  apply Finset.card_bij (fun I _ => I \ pendantLeaves G y z)
  · intro I hI
    have hIM := (mem_maximalIndependentSetsExcluding_iff G).1 hI
    apply (mem_maximalIndependentSetsOn_iff G).2
    refine ⟨?_, isIndependent_mono G hIM.1.2.1 (Finset.sdiff_subset), ?_⟩
    · intro a ha
      have haI : a ∈ I := (Finset.mem_sdiff.mp ha).1
      have haL : a ∉ pendantLeaves G y z := (Finset.mem_sdiff.mp ha).2
      exact (mem_pendantR_iff G).2
        ⟨fun hay => hIM.2 (hay ▸ haI), haL⟩
    · intro w hwR hwB
      have hwL : w ∉ pendantLeaves G y z := (mem_pendantR_iff G).1 hwR |>.2
      have hwI : w ∉ I := by
        intro hwI
        exact hwB (Finset.mem_sdiff.mpr ⟨hwI, hwL⟩)
      rcases hIM.1.2.2 (by simp) hwI with ⟨a, haI, haw⟩
      have haL : a ∉ pendantLeaves G y z := by
        intro haL
        have hay : w = y :=
          pendantLeaves_unique_neighbor G hleaf haL haw
        exact (mem_pendantR_iff G).1 hwR |>.1 hay
      exact ⟨a, Finset.mem_sdiff.mpr ⟨haI, haL⟩, haw⟩
  · intro I hI J hJ hEq
    have hIM := (mem_maximalIndependentSetsExcluding_iff G).1 hI
    have hJM := (mem_maximalIndependentSetsExcluding_iff G).1 hJ
    have hLI : pendantLeaves G y z ⊆ I := by
      intro l hl
      exact leaf_forced_into_maximal_of_center_absent G hleaf hIM.1 hIM.2 hl
    have hLJ : pendantLeaves G y z ⊆ J := by
      intro l hl
      exact leaf_forced_into_maximal_of_center_absent G hleaf hJM.1 hJM.2 hl
    apply Finset.Subset.antisymm
    · intro a ha
      by_cases haL : a ∈ pendantLeaves G y z
      · exact hLJ haL
      · have haB : a ∈ I \ pendantLeaves G y z :=
          Finset.mem_sdiff.mpr ⟨ha, haL⟩
        have : a ∈ J \ pendantLeaves G y z := hEq ▸ haB
        exact (Finset.mem_sdiff.mp this).1
    · intro a ha
      by_cases haL : a ∈ pendantLeaves G y z
      · exact hLI haL
      · have haB : a ∈ J \ pendantLeaves G y z :=
          Finset.mem_sdiff.mpr ⟨ha, haL⟩
        have : a ∈ I \ pendantLeaves G y z := hEq.symm ▸ haB
        exact (Finset.mem_sdiff.mp this).1
  · intro B hB
    have hBM : IsMaximalIndependentOn G (pendantR G y z) B :=
      (mem_maximalIndependentSetsOn_iff G).1 hB
    let L := pendantLeaves G y z
    let I : Finset V := L ∪ B
    have hIind : IsIndependent G I := by
      intro a ha b hb hab
      simp only [I, Finset.mem_union] at ha hb
      rcases ha with haL | haB
      · rcases hb with hbL | hbB
        · have hby : b = y :=
            pendantLeaves_unique_neighbor G hleaf haL hab
          have : y ∉ L := by
            simp [L, pendantLeaves, SimpleGraph.mem_neighborFinset]
          exact this (hby ▸ hbL)
        · have hby : b = y :=
            pendantLeaves_unique_neighbor G hleaf haL hab
          have hbR := hBM.1 hbB
          exact ((mem_pendantR_iff G).1 hbR).1 hby
      · rcases hb with hbL | hbB
        · have hay : a = y :=
            pendantLeaves_unique_neighbor G hleaf hbL (G.adj_symm hab)
          have haR := hBM.1 haB
          exact ((mem_pendantR_iff G).1 haR).1 hay
        · exact hBM.2.1 haB hbB hab
    have hIM : IsMaximalIndependent G I := by
      refine ⟨by simp, hIind, ?_⟩
      intro w _ hwI
      by_cases hwy : w = y
      · subst w
        rcases hL with ⟨l, hl⟩
        exact ⟨l, by simp [I, L, hl],
          G.adj_symm ((mem_pendantLeaves_iff G).1 hl |>.2)⟩
      · have hwL : w ∉ L := by
          intro hwL
          exact hwI (by simp [I, hwL])
        have hwR : w ∈ pendantR G y z :=
          (mem_pendantR_iff G).2 ⟨hwy, by simpa [L] using hwL⟩
        have hwB : w ∉ B := by
          intro hwB
          exact hwI (by simp [I, hwB])
        rcases hBM.2.2 hwR hwB with ⟨a, haB, haw⟩
        exact ⟨a, by simp [I, haB], haw⟩
    have hyI : y ∉ I := by
      intro hy
      rcases Finset.mem_union.mp hy with hyL | hyB
      · have : y ∉ L := by
          simp [L, pendantLeaves, SimpleGraph.mem_neighborFinset]
        exact this hyL
      · exact ((mem_pendantR_iff G).1 (hBM.1 hyB)).1 rfl
    refine ⟨I, (mem_maximalIndependentSetsExcluding_iff G).2 ⟨hIM, hyI⟩, ?_⟩
    ext a
    simp only [I, L, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨haL | haB, hnotL⟩
      · exact (hnotL haL).elim
      · exact haB
    · intro haB
      refine ⟨Or.inr haB, ?_⟩
      intro haL
      have haR := hBM.1 haB
      exact ((mem_pendantR_iff G).1 haR).2 haL

theorem maximalIndependentSetsExcluding_card_le_two_mul_containing
    {y z : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hL : (pendantLeaves G y z).Nonempty) :
    (maximalIndependentSetsExcluding G y).card ≤
      2 * (maximalIndependentSetsContaining G y).card := by
  rw [maximalIndependentSetsExcluding_card_eq_pendantR G hyz hleaf hL,
    maximalIndependentSetsContaining_card_eq_pendantF G hyz]
  simpa [pendantF] using
    maximalIndependentSetsOn_card_le_two_mul_erase
      G (pendantR G y z) z

end Pendant

end GreedyUniformity
