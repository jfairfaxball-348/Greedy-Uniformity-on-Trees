module

public import GreedyUniformity.MultiLeaf

@[expose] public section

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
      · exact hyz.ne
          (pendantLeaves_unique_neighbor G hleaf hx hab).symm
      · have hby : b = y :=
          pendantLeaves_unique_neighbor G hleaf hx hab
        exact ((mem_pendantF_iff G).1 (hA.1 hb)).2.1 hby
    · rcases hb with rfl | (rfl | hb)
      · exact hyz.ne
          (pendantLeaves_unique_neighbor G hleaf hx (G.adj_symm hab)).symm
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



theorem exists_fibre_order_with_adjacent_prefix
    {I : Finset V} (hI : IsMaximalIndependent G I)
    {v w : V} (hv : v ∈ I) (hw : w ∉ I) (hvw : G.Adj v w) :
    ∃ l ∈ fibre G I, ∃ t : List V, l = v :: w :: t := by
  classical
  let J : Finset V := I.erase v
  let R : Finset V := Finset.univ \ insert w I
  let l : List V := v :: w :: (J.toList ++ R.toList)
  have hnodupJR : (J.toList ++ R.toList).Nodup := by
    rw [List.nodup_append']
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    subst b
    have haI : a ∈ I := by
      have haJ : a ∈ J := by simpa using ha
      exact Finset.mem_of_mem_erase haJ
    have hbR : a ∈ Finset.univ \ insert w I := by
      simpa [R] using hb
    exact (Finset.mem_sdiff.mp hbR).2 (Finset.mem_insert_of_mem haI)
  have hnodup : l.Nodup := by
    simp [l, J, R, hvw.ne, hv, hw, hnodupJR]
  have horder : IsVertexOrder l := by
    unfold IsVertexOrder
    apply (List.perm_ext_iff_of_nodup hnodup (Finset.nodup_toList _)).2
    intro a
    by_cases hav : a = v
    · subst a
      simp [l]
    by_cases haw : a = w
    · subst a
      simp [l]
    by_cases haI : a ∈ I
    · simp [l, J, R, hav, haw, haI]
    · simp [l, J, R, hav, haw, haI]
  have hcert : PriorityCertificate G I l := by
    refine ⟨horder, hI, ?_⟩
    intro q hqI
    by_cases hqw : q = w
    · subst q
      refine ⟨v, hv, hvw, ?_⟩
      refine ⟨[], [], J.toList ++ R.toList, ?_⟩
      simp [l]
    · have hqR : q ∈ R := by
        simp [R, hqI, hqw]
      rcases hI.2.2 (by simp) hqI with ⟨u, huI, huq⟩
      refine ⟨u, huI, huq, ?_⟩
      have huPrefix : u ∈ v :: w :: J.toList := by
        simp only [List.mem_cons, Finset.mem_toList]
        by_cases huv : u = v
        · exact Or.inl huv
        · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨huv, huI⟩))
      have hqTail : q ∈ R.toList := by
        simpa using hqR
      have hp :=
        precedes_append_of_mem
          (a := v :: w :: J.toList) (b := R.toList) huPrefix hqTail
      simpa [l] using hp
  have hout : greedyOutput G l = I :=
    greedyOutput_eq_of_priorityCertificate G hcert
  refine ⟨l, (fibre_mem_iff G I l).2 ⟨horder, hout⟩,
    J.toList ++ R.toList, rfl⟩


theorem mem_image_map_swap_iff (x y : V) (s : Finset (List V)) (l : List V) :
    l ∈ s.image (fun q => q.map (Equiv.swap x y)) ↔
      l.map (Equiv.swap x y) ∈ s := by
  classical
  constructor
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨q, hq, hql⟩
    subst l
    simpa [List.map_map, Function.comp_def] using hq
  · intro hl
    apply Finset.mem_image.mpr
    refine ⟨l.map (Equiv.swap x y), hl, ?_⟩
    simpa [List.map_map, Function.comp_def]


theorem swap_leaf_fibre_to_center
    {y z x : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx : x ∈ pendantLeaves G y z)
    {A : Finset V}
    (hA : IsMaximalIndependentOn G (pendantF G y z) A)
    {l : List V} (hl : l ∈ fibre G (insert x A)) :
    l.map (Equiv.swap x y) ∈ fibre G (insert y A) := by
  classical
  let σ : Equiv.Perm V := Equiv.swap x y
  have hxy : x ≠ y := ((mem_pendantLeaves_iff G).1 hx |>.2).ne.symm
  have hyA : y ∉ A := by
    intro hyA
    exact ((mem_pendantF_iff G).1 (hA.1 hyA)).2.1 rfl
  have hxA : x ∉ A := by
    intro hxA
    exact ((mem_pendantF_iff G).1 (hA.1 hxA)).2.2 hx
  have hdata := (fibre_mem_iff G (insert x A) l).1 hl
  have hcert : PriorityCertificate G (insert x A) l :=
    (priorityCertificate_iff_greedyOutput_eq G hdata.1).2 hdata.2
  have horder' : IsVertexOrder (l.map σ) :=
    map_equiv_isVertexOrder σ hdata.1
  apply (fibre_mem_iff G (insert y A) (l.map σ)).2
  refine ⟨horder', ?_⟩
  apply greedyOutput_eq_of_priorityCertificate G
  refine ⟨horder', center_insert_maximal_of_maximalOn_pendantF G hyz hA, ?_⟩
  intro w hw
  by_cases hwx : w = x
  · subst w
    have hyIx : y ∉ insert x A := by
      simp [hxy.symm, hyA]
    rcases hcert.2.2 hyIx with ⟨u, hu, huyadj, hprec⟩
    have hux : u = x := by
      rcases Finset.mem_insert.mp hu with hux | huA
      · exact hux
      · exfalso
        exact pendantF_not_adj_center G (hA.1 huA) (G.adj_symm huyadj)
    subst u
    refine ⟨y, by simp, (mem_pendantLeaves_iff G).1 hx |>.2, ?_⟩
    simpa [σ] using (precedes_map_equiv σ hprec)
  · have hwy : w ≠ y := by
      intro hwy
      subst w
      exact hw (by simp)
    have hwA : w ∉ A := by
      intro hwA
      exact hw (Finset.mem_insert_of_mem hwA)
    have hwIx : w ∉ insert x A := by
      simp [hwx, hwA]
    rcases hcert.2.2 hwIx with ⟨u, hu, hadj, hprec⟩
    have huA : u ∈ A := by
      rcases Finset.mem_insert.mp hu with hux | huA
      · subst u
        have hwy' : w = y :=
          pendantLeaves_unique_neighbor G hleaf hx hadj
        exact (hwy hwy').elim
      · exact huA
    have hux : u ≠ x := by
      intro h
      subst u
      exact hxA huA
    have huy : u ≠ y := by
      intro h
      subst u
      exact hyA huA
    refine ⟨u, by simp [huA], hadj, ?_⟩
    have hp := precedes_map_equiv σ hprec
    have hfixu : σ u = u :=
      Equiv.swap_apply_of_ne_of_ne hux huy
    have hfixw : σ w = w :=
      Equiv.swap_apply_of_ne_of_ne hwx hwy
    simpa [hfixu, hfixw] using hp



theorem fibreCount_leaf_lt_center_of_dominates_z
    {y z x : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx : x ∈ pendantLeaves G y z)
    {A : Finset V}
    (hA : IsMaximalIndependentOn G (pendantF G y z) A)
    (hdom : ∃ a ∈ A, G.Adj a z) :
    fibreCount G (insert x A) < fibreCount G (insert y A) := by
  classical
  let σ : Equiv.Perm V := Equiv.swap x y
  let S : Finset (List V) :=
    (fibre G (insert x A)).image (fun q => q.map σ)
  have hxz : x ≠ z := (mem_pendantLeaves_iff G).1 hx |>.1
  have hxy : x ≠ y := ((mem_pendantLeaves_iff G).1 hx |>.2).ne.symm
  have hzA : z ∉ A := by
    intro hzA
    exact ((mem_pendantF_iff G).1 (hA.1 hzA)).1 rfl
  have hIy : IsMaximalIndependent G (insert y A) :=
    center_insert_maximal_of_maximalOn_pendantF G hyz hA
  have hzIy : z ∉ insert y A := by
    simp [hyz.ne.symm, hzA]
  obtain ⟨l, hlbig, t, hlt⟩ :=
    exists_fibre_order_with_adjacent_prefix
      G hIy (v := y) (w := z) (by simp) hzIy hyz
  have hfixz : σ z = z :=
    Equiv.swap_apply_of_ne_of_ne hxz.symm hyz.ne.symm
  have hmapshape : l.map σ = x :: z :: t.map σ := by
    rw [hlt]
    simp [σ, hfixz]
  have hxznot : ¬ G.Adj x z := by
    intro hxzadj
    have hzy : z = y :=
      pendantLeaves_unique_neighbor G hleaf hx hxzadj
    exact hyz.ne hzy.symm
  have hbad : l.map σ ∉ fibre G (insert x A) := by
    intro hmem
    have hout := (fibre_mem_iff G (insert x A) (l.map σ)).1 hmem |>.2
    have hzout : z ∈ greedyOutput G (l.map σ) := by
      classical
      letI : DecidableRel G.Adj := Classical.decRel _
      have hzstep : z ∈ greedyStep G (greedyStep G ∅ x) z := by
        simp [greedyStep, hxznot]
      have hzscan :
          z ∈ greedyList G (x :: z :: t.map σ) := by
        change z ∈ greedyScan G ∅ (x :: z :: t.map σ)
        simp only [greedyScan]
        exact greedyScan_subset G
          (greedyStep G (greedyStep G ∅ x) z) (t.map σ) hzstep
      rw [hmapshape]
      simpa [greedyOutput] using hzscan
    have hzsmall : z ∈ insert x A := by
      rw [← hout]
      exact hzout
    simp [hxz.symm, hzA] at hzsmall
  have hsub : S ⊆ fibre G (insert y A) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
    exact swap_leaf_fibre_to_center G hyz hleaf hx hA hr
  have hmiss : l ∉ S := by
    intro hlS
    have hlSwap :
        l.map (Equiv.swap x y) ∈ fibre G (insert x A) :=
      (mem_image_map_swap_iff x y (fibre G (insert x A)) l).1
        (by simpa [S, σ] using hlS)
    exact hbad (by simpa [σ] using hlSwap)
  have hproper : S ⊂ fibre G (insert y A) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub, ?_⟩
    intro heq
    exact hmiss (heq ▸ hlbig)
  have hltCard : S.card < (fibre G (insert y A)).card :=
    Finset.card_lt_card hproper
  have hcardS : S.card = (fibre G (insert x A)).card := by
    dsimp [S]
    exact Finset.card_image_of_injective _
      (List.map_injective_iff.mpr σ.injective)
  rw [hcardS] at hltCard
  simpa [fibreCount] using hltCard


theorem swap_center_fibre_to_leaf_z_of_not_dominates_z
    {y z x : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx : x ∈ pendantLeaves G y z)
    (hcard : (pendantLeaves G y z).card = 1)
    {A : Finset V}
    (hA : IsMaximalIndependentOn G (pendantF G y z) A)
    (hdom : ¬ ∃ a ∈ A, G.Adj a z)
    {l : List V} (hl : l ∈ fibre G (insert y A)) :
    l.map (Equiv.swap x y) ∈ fibre G (insert x (insert z A)) := by
  classical
  let σ : Equiv.Perm V := Equiv.swap x y
  have hxy : x ≠ y := ((mem_pendantLeaves_iff G).1 hx |>.2).ne.symm
  have hyA : y ∉ A := by
    intro hyA
    exact ((mem_pendantF_iff G).1 (hA.1 hyA)).2.1 rfl
  have hxA : x ∉ A := by
    intro hxA
    exact ((mem_pendantF_iff G).1 (hA.1 hxA)).2.2 hx
  have hL := pendantLeaves_eq_singleton_of_card_eq_one G hx hcard
  have hdata := (fibre_mem_iff G (insert y A) l).1 hl
  have hcert : PriorityCertificate G (insert y A) l :=
    (priorityCertificate_iff_greedyOutput_eq G hdata.1).2 hdata.2
  have horder' : IsVertexOrder (l.map σ) :=
    map_equiv_isVertexOrder σ hdata.1
  apply (fibre_mem_iff G (insert x (insert z A)) (l.map σ)).2
  refine ⟨horder', ?_⟩
  apply greedyOutput_eq_of_priorityCertificate G
  refine ⟨horder',
    leaf_z_insert_maximal_of_not_dominates_z
      G hyz hleaf hx hcard hA hdom, ?_⟩
  intro w hw
  by_cases hwy : w = y
  · subst w
    have hxIy : x ∉ insert y A := by
      simp [hxy, hxA]
    rcases hcert.2.2 hxIy with ⟨u, hu, huxadj, hprec⟩
    have huy : u = y :=
      pendantLeaves_unique_neighbor G hleaf hx (G.adj_symm huxadj)
    subst u
    refine ⟨x, by simp, G.adj_symm ((mem_pendantLeaves_iff G).1 hx |>.2), ?_⟩
    simpa [σ] using (precedes_map_equiv σ hprec)
  · have hwx : w ≠ x := by
      intro hwx
      subst w
      exact hw (by simp)
    have hwz : w ≠ z := by
      intro hwz
      subst w
      exact hw (by simp)
    have hwA : w ∉ A := by
      intro hwA
      exact hw (by simp [hwA])
    have hwIy : w ∉ insert y A := by
      simp [hwy, hwA]
    rcases hcert.2.2 hwIy with ⟨u, hu, hadj, hprec⟩
    have huA : u ∈ A := by
      rcases Finset.mem_insert.mp hu with huy | huA
      · subst u
        have hwL : w ∈ pendantLeaves G y z :=
          (mem_pendantLeaves_iff G).2 ⟨hwz, hadj⟩
        have hwxeq : w = x := by
          rw [hL] at hwL
          simpa using hwL
        exact (hwx hwxeq).elim
      · exact huA
    have hux : u ≠ x := by
      intro h
      subst u
      exact hxA huA
    have huy : u ≠ y := by
      intro h
      subst u
      exact hyA huA
    refine ⟨u, by simp [huA], hadj, ?_⟩
    have hp := precedes_map_equiv σ hprec
    have hfixu : σ u = u :=
      Equiv.swap_apply_of_ne_of_ne hux huy
    have hfixw : σ w = w :=
      Equiv.swap_apply_of_ne_of_ne hwx hwy
    simpa [hfixu, hfixw] using hp


theorem fibreCount_center_lt_leaf_z_of_not_dominates_z
    {y z x : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx : x ∈ pendantLeaves G y z)
    (hcard : (pendantLeaves G y z).card = 1)
    {A : Finset V}
    (hA : IsMaximalIndependentOn G (pendantF G y z) A)
    (hdom : ¬ ∃ a ∈ A, G.Adj a z) :
    fibreCount G (insert y A) <
      fibreCount G (insert x (insert z A)) := by
  classical
  let σ : Equiv.Perm V := Equiv.swap x y
  let S : Finset (List V) :=
    (fibre G (insert y A)).image (fun q => q.map σ)
  have hxz : x ≠ z := (mem_pendantLeaves_iff G).1 hx |>.1
  have hxy : x ≠ y := ((mem_pendantLeaves_iff G).1 hx |>.2).ne.symm
  have hyA : y ∉ A := by
    intro hyA
    exact ((mem_pendantF_iff G).1 (hA.1 hyA)).2.1 rfl
  have hzA : z ∉ A := by
    intro hzA
    exact ((mem_pendantF_iff G).1 (hA.1 hzA)).1 rfl
  have hIx : IsMaximalIndependent G (insert x (insert z A)) :=
    leaf_z_insert_maximal_of_not_dominates_z
      G hyz hleaf hx hcard hA hdom
  have hyIx : y ∉ insert x (insert z A) := by
    simp [hxy.symm, hyz.ne, hyA]
  obtain ⟨l, hlbig, t, hlt⟩ :=
    exists_fibre_order_with_adjacent_prefix
      G hIx (v := z) (w := y) (by simp) hyIx (G.adj_symm hyz)
  have hfixz : σ z = z :=
    Equiv.swap_apply_of_ne_of_ne hxz.symm hyz.ne.symm
  have hmapshape : l.map σ = z :: x :: t.map σ := by
    rw [hlt]
    simp [σ, hfixz]
  have hIy : IsMaximalIndependent G (insert y A) :=
    center_insert_maximal_of_maximalOn_pendantF G hyz hA
  have hzIy : z ∉ insert y A := by
    simp [hyz.ne.symm, hzA]
  have hbad : l.map σ ∉ fibre G (insert y A) := by
    intro hmem
    have hout := (fibre_mem_iff G (insert y A) (l.map σ)).1 hmem |>.2
    have hzout : z ∈ greedyOutput G (l.map σ) := by
      classical
      letI : DecidableRel G.Adj := Classical.decRel _
      have hzstep : z ∈ greedyStep G (∅ : Finset V) z := by
        simp [greedyStep]
      have hzscan : z ∈ greedyList G (z :: x :: t.map σ) := by
        change z ∈ greedyScan G ∅ (z :: x :: t.map σ)
        simp only [greedyScan]
        exact greedyScan_subset G (greedyStep G ∅ z)
          (x :: t.map σ) hzstep
      rw [hmapshape]
      simpa [greedyOutput] using hzscan
    have hzsmall : z ∈ insert y A := by
      rw [← hout]
      exact hzout
    exact hzIy hzsmall
  have hsub : S ⊆ fibre G (insert x (insert z A)) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
    exact swap_center_fibre_to_leaf_z_of_not_dominates_z
      G hyz hleaf hx hcard hA hdom hr
  have hmiss : l ∉ S := by
    intro hlS
    have hlSwap :
        l.map (Equiv.swap x y) ∈ fibre G (insert y A) :=
      (mem_image_map_swap_iff x y (fibre G (insert y A)) l).1
        (by simpa [S, σ] using hlS)
    exact hbad (by simpa [σ] using hlSwap)
  have hproper : S ⊂ fibre G (insert x (insert z A)) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub, ?_⟩
    intro heq
    exact hmiss (heq ▸ hlbig)
  have hltCard : S.card < (fibre G (insert x (insert z A))).card :=
    Finset.card_lt_card hproper
  have hcardS : S.card = (fibre G (insert y A)).card := by
    dsimp [S]
    exact Finset.card_image_of_injective _
      (List.map_injective_iff.mpr σ.injective)
  rw [hcardS] at hltCard
  simpa [fibreCount] using hltCard

theorem not_uniformFibres_of_one_pendantLeaf
    {y z x : V} (hyz : G.Adj y z)
    (hleaf : ∀ q : V, G.Adj y q → q ≠ z → G.degree q = 1)
    (hx : x ∈ pendantLeaves G y z)
    (hcard : (pendantLeaves G y z).card = 1) :
    ¬ UniformFibres G := by
  classical
  have hemptySub : (∅ : Finset V) ⊆ pendantF G y z := by simp
  have hemptyInd : IsIndependent G (∅ : Finset V) := by
    intro a ha
    simp at ha
  obtain ⟨A, hA, _⟩ :=
    exists_maximalIndependentOn_superset
      G hemptySub hemptyInd
  have hIy : IsMaximalIndependent G (insert y A) :=
    center_insert_maximal_of_maximalOn_pendantF G hyz hA
  by_cases hdom : ∃ a ∈ A, G.Adj a z
  · have hIx : IsMaximalIndependent G (insert x A) :=
      leaf_insert_maximal_of_dominates_z
        G hyz hleaf hx hcard hA hdom
    have hlt :=
      fibreCount_leaf_lt_center_of_dominates_z
        G hyz hleaf hx hA hdom
    intro hU
    have heq := hU hIx hIy
    omega
  · have hIx : IsMaximalIndependent G (insert x (insert z A)) :=
      leaf_z_insert_maximal_of_not_dominates_z
        G hyz hleaf hx hcard hA hdom
    have hlt :=
      fibreCount_center_lt_leaf_z_of_not_dominates_z
        G hyz hleaf hx hcard hA hdom
    intro hU
    have heq := hU hIy hIx
    omega

end OneLeaf

end GreedyUniformity
