import GreedyUniformity.Bridge

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem idxOf_map_equiv (σ : Equiv.Perm V) (l : List V) (x : V) :
    (l.map σ).idxOf (σ x) = l.idxOf x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : a = x
      · subst a
        simp
      · have hs : σ a ≠ σ x := fun h' => h (σ.injective h')
        rw [List.map_cons, List.idxOf_cons_ne _ hs, List.idxOf_cons_ne _ h, ih]

theorem map_equiv_isVertexOrder (σ : Equiv.Perm V) {l : List V}
    (hl : IsVertexOrder l) :
    IsVertexOrder (l.map σ) := by
  apply (List.perm_ext_iff_of_nodup
    ((isVertexOrder_nodup hl).map σ.injective)
    (Finset.nodup_toList _)).2
  intro x
  constructor
  · intro hx
    simp
  · intro _
    apply List.mem_map.mpr
    refine ⟨σ.symm x, isVertexOrder_complete hl (σ.symm x), ?_⟩
    exact σ.apply_symm_apply x

noncomputable def firstOfThreeOrders (a b c : V) : Finset (List V) := by
  classical
  exact (vertexOrders (V := V)).filter fun l =>
    l.idxOf a < l.idxOf b ∧ l.idxOf a < l.idxOf c

theorem mem_firstOfThreeOrders_iff {a b c : V} {l : List V} :
    l ∈ firstOfThreeOrders a b c ↔
      IsVertexOrder l ∧ l.idxOf a < l.idxOf b ∧ l.idxOf a < l.idxOf c := by
  classical
  simp [firstOfThreeOrders, mem_vertexOrders_iff]

theorem firstOfThreeOrders_card_swap_first_second
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (firstOfThreeOrders a b c).card =
      (firstOfThreeOrders b a c).card := by
  classical
  let σ : Equiv.Perm V := Equiv.swap a b
  apply Finset.card_bij (fun l _ => l.map σ)
  · intro l hl
    have h := (mem_firstOfThreeOrders_iff).1 hl
    apply (mem_firstOfThreeOrders_iff).2
    refine ⟨map_equiv_isVertexOrder σ h.1, ?_, ?_⟩
    · have hbpos : (l.map σ).idxOf b = l.idxOf a := by
        simpa [σ] using idxOf_map_equiv σ l a
      have hapos : (l.map σ).idxOf a = l.idxOf b := by
        simpa [σ] using idxOf_map_equiv σ l b
      simpa [hbpos, hapos] using h.2.1
    · have hbpos : (l.map σ).idxOf b = l.idxOf a := by
        simpa [σ] using idxOf_map_equiv σ l a
      have hcpos : (l.map σ).idxOf c = l.idxOf c := by
        have hs : σ c = c := by
          exact Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm
        simpa [hs] using idxOf_map_equiv σ l c
      simpa [hbpos, hcpos] using h.2.2
  · intro l hl m hm heq
    exact (List.map_injective_iff.mpr σ.injective) heq
  · intro m hm
    refine ⟨m.map σ, ?_, ?_⟩
    · have h := (mem_firstOfThreeOrders_iff).1 hm
      apply (mem_firstOfThreeOrders_iff).2
      refine ⟨map_equiv_isVertexOrder σ h.1, ?_, ?_⟩
      · have hapos : ((m.map σ).map σ).idxOf a = m.idxOf a := by
          simp [σ, List.map_map]
        have hbpos : ((m.map σ).map σ).idxOf b = m.idxOf b := by
          simp [σ, List.map_map]
        simpa [hapos, hbpos] using h.2.1
      · have hapos : ((m.map σ).map σ).idxOf a = m.idxOf a := by
          simp [σ, List.map_map]
        have hcpos : ((m.map σ).map σ).idxOf c = m.idxOf c := by
          simp [σ, List.map_map]
        simpa [hapos, hcpos] using h.2.2
    · simp [σ, List.map_map]

theorem firstOfThreeOrders_card_swap_first_third
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (firstOfThreeOrders a b c).card =
      (firstOfThreeOrders c b a).card := by
  have h :=
    firstOfThreeOrders_card_swap_first_second
      (a := a) (b := c) (c := b) hac hab hbc.symm
  simpa [and_comm] using h

theorem vertexOrders_partition_firstOfThree
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (vertexOrders (V := V)).card =
      (firstOfThreeOrders a b c).card +
      (firstOfThreeOrders b a c).card +
      (firstOfThreeOrders c a b).card := by
  classical
  let A := firstOfThreeOrders a b c
  let B := firstOfThreeOrders b a c
  let C := firstOfThreeOrders c a b
  have hunion : (vertexOrders (V := V)) = A ∪ B ∪ C := by
    ext l
    constructor
    · intro hl
      have horder : IsVertexOrder l := (mem_vertexOrders_iff).1 hl
      have ha : a ∈ l := isVertexOrder_complete horder a
      have hb : b ∈ l := isVertexOrder_complete horder b
      have hc : c ∈ l := isVertexOrder_complete horder c
      have hai : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 ha
      have hbi : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hb
      have hci : l.idxOf c < l.length := List.idxOf_lt_length_iff.2 hc
      have hiab : l.idxOf a ≠ l.idxOf b := by
        intro h
        have hnd := isVertexOrder_nodup horder
        have haeq : l.get ⟨l.idxOf a, hai⟩ = a := List.idxOf_get hai
        have hbeq : l.get ⟨l.idxOf b, hbi⟩ = b := List.idxOf_get hbi
        have : a = b := by
          rw [← haeq, ← hbeq, h]
        exact hab this
      have hiac : l.idxOf a ≠ l.idxOf c := by
        intro h
        have haeq : l.get ⟨l.idxOf a, hai⟩ = a := List.idxOf_get hai
        have hceq : l.get ⟨l.idxOf c, hci⟩ = c := List.idxOf_get hci
        have : a = c := by
          rw [← haeq, ← hceq, h]
        exact hac this
      have hibc : l.idxOf b ≠ l.idxOf c := by
        intro h
        have hbeq : l.get ⟨l.idxOf b, hbi⟩ = b := List.idxOf_get hbi
        have hceq : l.get ⟨l.idxOf c, hci⟩ = c := List.idxOf_get hci
        have : b = c := by
          rw [← hbeq, ← hceq, h]
        exact hbc this
      simp only [Finset.mem_union]
      rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with hablt | habeq | hbalt
      · rcases lt_trichotomy (l.idxOf a) (l.idxOf c) with haclt | haceq | hcalt
        · left
          exact (mem_firstOfThreeOrders_iff).2 ⟨horder, hablt, haclt⟩
        · exact (hiac haceq).elim
        · right
          right
          have hcb : l.idxOf c < l.idxOf b := hcalt.trans hablt
          exact (mem_firstOfThreeOrders_iff).2 ⟨horder, hcalt, hcb⟩
      · exact (hiab habeq).elim
      · rcases lt_trichotomy (l.idxOf b) (l.idxOf c) with hbclt | hbceq | hcblt
        · right
          left
          exact (mem_firstOfThreeOrders_iff).2 ⟨horder, hbalt, hbclt⟩
        · exact (hibc hbceq).elim
        · right
          right
          have hca : l.idxOf c < l.idxOf a := hcblt.trans hbalt
          exact (mem_firstOfThreeOrders_iff).2 ⟨horder, hca, hcblt⟩
    · intro hl
      rcases Finset.mem_union.mp hl with hAB | hC
      · rcases Finset.mem_union.mp hAB with hA | hB
        · exact (mem_vertexOrders_iff).2 ((mem_firstOfThreeOrders_iff).1 hA |>.1)
        · exact (mem_vertexOrders_iff).2 ((mem_firstOfThreeOrders_iff).1 hB |>.1)
      · exact (mem_vertexOrders_iff).2 ((mem_firstOfThreeOrders_iff).1 hC |>.1)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro l hA hB
    have ha := (mem_firstOfThreeOrders_iff).1 hA |>.2.1
    have hb := (mem_firstOfThreeOrders_iff).1 hB |>.2.1
    exact (Nat.lt_asymm ha hb)
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro l hA hC
    have ha := (mem_firstOfThreeOrders_iff).1 hA |>.2.2
    have hc := (mem_firstOfThreeOrders_iff).1 hC |>.2.1
    exact (Nat.lt_asymm ha hc)
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro l hB hC
    have hb := (mem_firstOfThreeOrders_iff).1 hB |>.2.2
    have hc := (mem_firstOfThreeOrders_iff).1 hC |>.2.2
    exact (Nat.lt_asymm hb hc)
  rw [hunion, Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint hAB]
  · exact Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩

theorem three_mul_firstOfThreeOrders_card
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 * (firstOfThreeOrders a b c).card =
      (vertexOrders (V := V)).card := by
  have hpart := vertexOrders_partition_firstOfThree
    (a := a) (b := b) (c := c) hab hac hbc
  have habc := firstOfThreeOrders_card_swap_first_second
    (a := a) (b := b) (c := c) hab hac hbc
  have hacb := firstOfThreeOrders_card_swap_first_third
    (a := a) (b := b) (c := c) hab hac hbc
  rw [← habc, ← hacb] at hpart
  omega

end GreedyUniformity
