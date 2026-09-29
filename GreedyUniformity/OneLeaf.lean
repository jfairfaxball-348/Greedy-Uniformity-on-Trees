import GreedyUniformity.MultiLeaf

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem precedes_map_equiv (σ : Equiv.Perm V) {l : List V} {u v : V}
    (h : Precedes l u v) :
    Precedes (l.map σ) (σ u) (σ v) := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨a.map σ, b.map σ, c.map σ, ?_⟩
  simp [List.map_append, List.append_assoc]

section OneLeaf

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem pendantLeaves_eq_singleton_of_card_eq_one
    {y z x : V} (hx : x ∈ pendantLeaves G y z)
    (hcard : (pendantLeaves G y z).card = 1) :
    pendantLeaves G y z = {x} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨hx, ?_⟩
  intro w hw
  exact Finset.card_le_one.1 hcard.le w hw x hx

theorem center_insert_maximal_of_maximalOn_pendantF
    {y z : V} (hyz : G.Adj y z) {A : Finset V}
    (hA : IsMaximalIndependentOn G (pendantF G y z) A) :
    IsMaximalIndependent G (insert y A) := by
  have hIind : IsIndependent G (insert y A) := by
    intro a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact G.irrefl hab
      · exact pendantF_not_adj_center G (hA.1 hb) hab
    · rcases hb with rfl | hb
      · exact pendantF_not_adj_center G (hA.1 ha) (G.adj_symm hab)
      · exact hA.2.1 ha hb hab
  refine ⟨by simp, hIind, ?_⟩
  intro w _ hwI
  by_cases hwy : G.Adj y w
  · exact ⟨y, by simp, hwy⟩
  · have hwyne : w ≠ y := by
      intro h
      subst w
      exact hwI (by simp)
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
      exact hwI (by simp [hwA])
    rcases hA.2.2 hwF hwA with ⟨a, haA, haw⟩
    exact ⟨a, by simp [haA], haw⟩

theorem leaf_insert_maximal_of_dominates_z
    {y z x : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx : x ∈ pendantLeaves G y z)
    (hcard : (pendantLeaves G y z).card = 1)
    {A : Finset V}
    (hA : IsMaximalIndependentOn G (pendantF G y z) A)
    (hdom : ∃ a ∈ A, G.Adj a z) :
    IsMaximalIndependent G (insert x A) := by
  have hL := pendantLeaves_eq_singleton_of_card_eq_one G hx hcard
  have hIind : IsIndependent G (insert x A) := by
    intro a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact G.irrefl hab
      · have hby : b = y :=
          pendantLeaves_unique_neighbor G hleaf hx hab
        exact ((mem_pendantF_iff G).1 (hA.1 hb)).2.1 hby
    · rcases hb with rfl | hb
      · have hay : a = y :=
          pendantLeaves_unique_neighbor G hleaf hx (G.adj_symm hab)
        exact ((mem_pendantF_iff G).1 (hA.1 ha)).2.1 hay
      · exact hA.2.1 ha hb hab
  refine ⟨by simp, hIind, ?_⟩
  intro w _ hwI
  by_cases hwy : w = y
  · subst w
    exact ⟨x, by simp, G.adj_symm ((mem_pendantLeaves_iff G).1 hx |>.2)⟩
  by_cases hwz : w = z
  · subst w
    rcases hdom with ⟨a, ha, haz⟩
    exact ⟨a, by simp [ha], haz⟩
  have hwL : w ∉ pendantLeaves G y z := by
    intro hw
    have hwx : w = x := by
      rw [hL] at hw
      simpa using hw
    subst w
    exact hwI (by simp)
  have hwF : w ∈ pendantF G y z :=
    (mem_pendantF_iff G).2 ⟨hwz, hwy, hwL⟩
  have hwA : w ∉ A := by
    intro hwA
    exact hwI (by simp [hwA])
  rcases hA.2.2 hwF hwA with ⟨a, ha, haw⟩
  exact ⟨a, by simp [ha], haw⟩

theorem leaf_z_insert_maximal_of_not_dominates_z
    {y z x : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx : x ∈ pendantLeaves G y z)
    (hcard : (pendantLeaves G y z).card = 1)
    {A : Finset V}
    (hA : IsMaximalIndependentOn G (pendantF G y z) A)
    (hdom : ¬ ∃ a ∈ A, G.Adj a z) :
    IsMaximalIndependent G (insert x (insert z A)) := by
  have hL := pendantLeaves_eq_singleton_of_card_eq_one G hx hcard
  have hIind : IsIndependent G (insert x (insert z A)) := by
    intro a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | (rfl | ha)
    · rcases hb with rfl | (rfl | hb)
      · exact G.irrefl hab
      · have hzy : z = y :=
          pendantLeaves_unique_neighbor G hleaf hx hab
        exact hyz.ne hzy.symm
      · have hby : b = y :=
          pendantLeaves_unique_neighbor G hleaf hx hab
        exact ((mem_pendantF_iff G).1 (hA.1 hb)).2.1 hby
    · rcases hb with rfl | (rfl | hb)
      · have hzy : z = y :=
          pendantLeaves_unique_neighbor G hleaf hx (G.adj_symm hab)
        exact hyz.ne hzy.symm
      · exact G.irrefl hab
      · exact hdom ⟨b, hb, G.adj_symm hab⟩
    · rcases hb with rfl | (rfl | hb)
      · have hay : a = y :=
          pendantLeaves_unique_neighbor G hleaf hx (G.adj_symm hab)
        exact ((mem_pendantF_iff G).1 (hA.1 ha)).2.1 hay
      · exact hdom ⟨a, ha, hab⟩
      · exact hA.2.1 ha hb hab
  refine ⟨by simp, hIind, ?_⟩
  intro w _ hwI
  by_cases hwy : w = y
  · subst w
    exact ⟨x, by simp, G.adj_symm ((mem_pendantLeaves_iff G).1 hx |>.2)⟩
  have hwz : w ≠ z := by
    intro h
    subst w
    exact hwI (by simp)
  have hwx : w ≠ x := by
    intro h
    subst w
    exact hwI (by simp)
  have hwL : w ∉ pendantLeaves G y z := by
    intro hw
    have : w = x := by
      rw [hL] at hw
      simpa using hw
    exact hwx this
  have hwF : w ∈ pendantF G y z :=
    (mem_pendantF_iff G).2 ⟨hwz, hwy, hwL⟩
  have hwA : w ∉ A := by
    intro hwA
    exact hwI (by simp [hwA])
  rcases hA.2.2 hwF hwA with ⟨a, ha, haw⟩
  exact ⟨a, by simp [ha], haw⟩

end OneLeaf

end GreedyUniformity
