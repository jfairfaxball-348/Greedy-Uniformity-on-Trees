import GreedyUniformity.MixedSpiderBiasFormula
import GreedyUniformity.OrderCount

namespace GreedyUniformity

open MixedSpiderVertex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Precedence is transported exactly by a permutation of vertex labels. -/
theorem precedes_map_equiv_iff
    (σ : Equiv.Perm V) (order : List V) (x y : V) :
    Precedes (order.map σ) (σ x) (σ y) ↔ Precedes order x y := by
  constructor
  · rintro ⟨a, b, c, h⟩
    have h' := congrArg (List.map σ.symm) h
    simp only [List.map_append, List.map_cons, List.map_map,
      Function.comp_def, σ.symm_apply_apply] at h'
    exact ⟨a.map σ.symm, b.map σ.symm, c.map σ.symm, h'⟩
  · rintro ⟨a, b, c, rfl⟩
    refine ⟨a.map σ, b.map σ, c.map σ, ?_⟩
    simp [List.map_append]

/-- Two distinct vertices in a complete vertex order occur in exactly one
relative orientation. -/
theorem precedes_or_precedes_of_isVertexOrder
    {order : List V} (horder : IsVertexOrder order)
    {x y : V} (hxy : x ≠ y) :
    Precedes order x y ∨ Precedes order y x := by
  have hx : x ∈ order := isVertexOrder_complete horder x
  have hy : y ∈ order := isVertexOrder_complete horder y
  rcases List.append_of_mem hx with ⟨a, b, rfl⟩
  have hy' : y ∈ a ∨ y ∈ b := by
    simpa [hxy.symm] using hy
  rcases hy' with hya | hyb
  · right
    rcases List.append_of_mem hya with ⟨a₁, a₂, rfl⟩
    refine ⟨a₁, a₂, b, ?_⟩
    simp [List.append_assoc]
  · left
    rcases List.append_of_mem hyb with ⟨b₁, b₂, rfl⟩
    refine ⟨a, b₁, b₂, ?_⟩
    simp [List.append_assoc]

theorem not_precedes_reverse_of_isVertexOrder
    {order : List V} (horder : IsVertexOrder order)
    {x y : V} (hxy : x ≠ y)
    (hxyPrec : Precedes order x y) :
    ¬ Precedes order y x := by
  intro hyxPrec
  have hnodup := isVertexOrder_nodup horder
  have hlt := precedes_idxOf_lt hnodup hxyPrec
  have hgt := precedes_idxOf_lt hnodup hyxPrec
  exact (Nat.lt_asymm hlt hgt)

theorem precedes_reverse_iff_not
    {order : List V} (horder : IsVertexOrder order)
    {x y : V} (hxy : x ≠ y) :
    Precedes order y x ↔ ¬ Precedes order x y := by
  constructor
  · intro hyx hxyPrec
    exact not_precedes_reverse_of_isVertexOrder horder hxy hyx hxyPrec
  · intro hnot
    rcases precedes_or_precedes_of_isVertexOrder horder hxy with hxyPrec | hyxPrec
    · exact (hnot hxyPrec).elim
    · exact hyxPrec

section ArmFlip

variable {k l : ℕ}

/-- Swap the two endpoints on exactly the arms in D. -/
def mixedSpiderArmFlip (D : Finset (Fin k)) :
    Equiv.Perm (MixedSpiderVertex k l) where
  toFun
    | .center => .center
    | .inner i => if i ∈ D then .outer i else .inner i
    | .outer i => if i ∈ D then .inner i else .outer i
    | .leaf r => .leaf r
  invFun
    | .center => .center
    | .inner i => if i ∈ D then .outer i else .inner i
    | .outer i => if i ∈ D then .inner i else .outer i
    | .leaf r => .leaf r
  left_inv x := by
    cases x with
    | center => rfl
    | inner i => by_cases hi : i ∈ D <;> simp [hi]
    | outer i => by_cases hi : i ∈ D <;> simp [hi]
    | leaf r => rfl
  right_inv x := by
    cases x with
    | center => rfl
    | inner i => by_cases hi : i ∈ D <;> simp [hi]
    | outer i => by_cases hi : i ∈ D <;> simp [hi]
    | leaf r => rfl

@[simp] theorem mixedSpiderArmFlip_center
    (D : Finset (Fin k)) :
    mixedSpiderArmFlip (l := l) D center = center := rfl

@[simp] theorem mixedSpiderArmFlip_leaf
    (D : Finset (Fin k)) (r : Fin l) :
    mixedSpiderArmFlip (l := l) D (leaf r) = leaf r := rfl

theorem mixedSpiderArmFlip_inner
    (D : Finset (Fin k)) (i : Fin k) :
    mixedSpiderArmFlip (l := l) D (inner i) =
      if i ∈ D then outer i else inner i := rfl

theorem mixedSpiderArmFlip_outer
    (D : Finset (Fin k)) (i : Fin k) :
    mixedSpiderArmFlip (l := l) D (outer i) =
      if i ∈ D then inner i else outer i := rfl

/-- The arm orientation encoded by a complete order. -/
noncomputable def mixedSpiderArmPattern
    (order : List (MixedSpiderVertex k l)) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i => Precedes order (inner i) (outer i)

@[simp] theorem mem_mixedSpiderArmPattern_iff
    (order : List (MixedSpiderVertex k l)) (i : Fin k) :
    i ∈ mixedSpiderArmPattern order ↔
      Precedes order (inner i) (outer i) := by
  classical
  simp [mixedSpiderArmPattern]

/-- Flipping an arm toggles exactly its membership in the orientation pattern. -/
theorem mem_mixedSpiderArmPattern_map_armFlip_iff
    {order : List (MixedSpiderVertex k l)}
    (horder : IsVertexOrder order)
    (D : Finset (Fin k)) (i : Fin k) :
    i ∈ mixedSpiderArmPattern (order.map (mixedSpiderArmFlip (l := l) D)) ↔
      ((i ∈ D ∧ i ∉ mixedSpiderArmPattern order) ∨
        (i ∉ D ∧ i ∈ mixedSpiderArmPattern order)) := by
  classical
  by_cases hiD : i ∈ D
  · have horder' :=
      map_equiv_isVertexOrder (mixedSpiderArmFlip (l := l) D) horder
    rw [mem_mixedSpiderArmPattern_iff, mixedSpiderArmFlip_inner,
      mixedSpiderArmFlip_outer]
    simp only [hiD, if_true]
    rw [precedes_map_equiv_iff]
    rw [precedes_reverse_iff_not horder
      (by simp : (inner i : MixedSpiderVertex k l) ≠ outer i)]
    simp [mem_mixedSpiderArmPattern_iff, hiD]
  · rw [mem_mixedSpiderArmPattern_iff, mixedSpiderArmFlip_inner,
      mixedSpiderArmFlip_outer]
    simp only [hiD, if_false]
    rw [precedes_map_equiv_iff]
    simp [mem_mixedSpiderArmPattern_iff, hiD]

theorem mixedSpiderArmFlip_involutive
    (D : Finset (Fin k)) (v : MixedSpiderVertex k l) :
    mixedSpiderArmFlip (l := l) D
      (mixedSpiderArmFlip (l := l) D v) = v := by
  cases v with
  | center => rfl
  | inner i => by_cases hi : i ∈ D <;> simp [mixedSpiderArmFlip, hi]
  | outer i => by_cases hi : i ∈ D <;> simp [mixedSpiderArmFlip, hi]
  | leaf r => rfl

theorem map_mixedSpiderArmFlip_twice
    (D : Finset (Fin k)) (order : List (MixedSpiderVertex k l)) :
    (order.map (mixedSpiderArmFlip (l := l) D)).map
        (mixedSpiderArmFlip (l := l) D) = order := by
  simp [List.map_map, Function.comp_def, mixedSpiderArmFlip_involutive]

/-- Vertex orders having one fixed orientation choice on every length-two arm. -/
noncomputable def mixedSpiderOrientationOrders
    (S : Finset (Fin k)) :
    Finset (List (MixedSpiderVertex k l)) := by
  classical
  exact (vertexOrders (V := MixedSpiderVertex k l)).filter fun order =>
    mixedSpiderArmPattern order = S

theorem mem_mixedSpiderOrientationOrders_iff
    {S : Finset (Fin k)} {order : List (MixedSpiderVertex k l)} :
    order ∈ mixedSpiderOrientationOrders (l := l) S ↔
      IsVertexOrder order ∧ mixedSpiderArmPattern order = S := by
  classical
  simp [mixedSpiderOrientationOrders, mem_vertexOrders_iff]

theorem armPattern_map_flip_self_eq_empty
    {S : Finset (Fin k)} {order : List (MixedSpiderVertex k l)}
    (horder : IsVertexOrder order)
    (hpat : mixedSpiderArmPattern order = S) :
    mixedSpiderArmPattern
        (order.map (mixedSpiderArmFlip (l := l) S)) = ∅ := by
  classical
  ext i
  rw [Finset.not_mem_empty]
  push_neg
  rw [mem_mixedSpiderArmPattern_map_armFlip_iff horder S i, hpat]
  simp

theorem armPattern_map_flip_empty_eq_self
    {S : Finset (Fin k)} {order : List (MixedSpiderVertex k l)}
    (horder : IsVertexOrder order)
    (hpat : mixedSpiderArmPattern order = ∅) :
    mixedSpiderArmPattern
        (order.map (mixedSpiderArmFlip (l := l) S)) = S := by
  classical
  ext i
  rw [mem_mixedSpiderArmPattern_map_armFlip_iff horder S i, hpat]
  simp

/-- All 2^k arm-orientation classes have the same number of vertex orders. -/
theorem mixedSpiderOrientationOrders_card_eq_empty
    (S : Finset (Fin k)) :
    (mixedSpiderOrientationOrders (l := l) S).card =
      (mixedSpiderOrientationOrders (l := l) ∅).card := by
  classical
  let σ := mixedSpiderArmFlip (l := l) S
  apply Finset.card_bij (fun order _ => order.map σ)
  · intro order horder
    rcases (mem_mixedSpiderOrientationOrders_iff).1 horder with
      ⟨hvo, hpat⟩
    apply (mem_mixedSpiderOrientationOrders_iff).2
    refine ⟨map_equiv_isVertexOrder σ hvo, ?_⟩
    exact armPattern_map_flip_self_eq_empty hvo hpat
  · intro a ha b hb hab
    exact (List.map_injective_iff.mpr σ.injective) hab
  · intro order horder
    rcases (mem_mixedSpiderOrientationOrders_iff).1 horder with
      ⟨hvo, hpat⟩
    refine ⟨order.map σ, ?_, ?_⟩
    · apply (mem_mixedSpiderOrientationOrders_iff).2
      refine ⟨map_equiv_isVertexOrder σ hvo, ?_⟩
      exact armPattern_map_flip_empty_eq_self hvo hpat
    · simpa [σ] using
        (map_mixedSpiderArmFlip_twice (l := l) S order)

/-- Exact orientation count: prescribing one relative order on every arm
costs a factor 2^k. -/
theorem two_pow_mul_mixedSpiderOrientationOrders_card
    (S : Finset (Fin k)) :
    2 ^ k * (mixedSpiderOrientationOrders (l := l) S).card =
      (vertexOrders (V := MixedSpiderVertex k l)).card := by
  classical
  have hpart :
      (vertexOrders (V := MixedSpiderVertex k l)).card =
        ∑ T ∈ (Finset.univ : Finset (Finset (Fin k))),
          (mixedSpiderOrientationOrders (l := l) T).card := by
    simpa [mixedSpiderOrientationOrders] using
      (Finset.card_eq_sum_card_fiberwise
        (f := mixedSpiderArmPattern (k := k) (l := l))
        (s := vertexOrders (V := MixedSpiderVertex k l))
        (t := (Finset.univ : Finset (Finset (Fin k))))
        (by
          intro order horder
          simp))
  have heq :
      ∀ T : Finset (Fin k),
        (mixedSpiderOrientationOrders (l := l) T).card =
          (mixedSpiderOrientationOrders (l := l) ∅).card :=
    mixedSpiderOrientationOrders_card_eq_empty (l := l)
  calc
    2 ^ k * (mixedSpiderOrientationOrders (l := l) S).card =
        2 ^ k * (mixedSpiderOrientationOrders (l := l) ∅).card := by
          rw [heq S]
    _ = ∑ T ∈ (Finset.univ : Finset (Finset (Fin k))),
          (mixedSpiderOrientationOrders (l := l) ∅).card := by
          simp
    _ = ∑ T ∈ (Finset.univ : Finset (Finset (Fin k))),
          (mixedSpiderOrientationOrders (l := l) T).card := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [heq T]
    _ = (vertexOrders (V := MixedSpiderVertex k l)).card := hpart.symm

end ArmFlip

end GreedyUniformity
