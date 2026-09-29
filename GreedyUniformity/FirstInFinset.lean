import GreedyUniformity.OrderCount
import Mathlib.Order.WellFounded

namespace GreedyUniformity

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The element of a nonempty finite set occurring first in a list, defined by
minimising its list index. It is used only on complete vertex orders below. -/
noncomputable def firstInFinset
    (R : Finset V) (hR : R.Nonempty) (order : List V) : V :=
  Function.argminOn (fun x : V => order.idxOf x) (↑R : Set V) (by
    simpa using hR)

theorem firstInFinset_mem
    (R : Finset V) (hR : R.Nonempty) (order : List V) :
    firstInFinset R hR order ∈ R := by
  unfold firstInFinset
  simpa using
    (Function.argminOn_mem
      (fun x : V => order.idxOf x) (↑R : Set V) (by simpa using hR))

/-- On a complete order, firstInFinset = a is equivalent to a preceding
every other member of the finite set. -/
theorem firstInFinset_eq_iff
    (R : Finset V) (hR : R.Nonempty)
    {order : List V} (horder : IsVertexOrder order) (a : V) :
    firstInFinset R hR order = a ↔
      a ∈ R ∧ ∀ b ∈ R, b ≠ a → Precedes order a b := by
  constructor
  · intro hfirst
    have ha : a ∈ R := by
      rw [← hfirst]
      exact firstInFinset_mem R hR order
    refine ⟨ha, ?_⟩
    intro b hb hba
    rcases precedes_or_precedes_of_isVertexOrder horder hba.symm with
      hab | hbaPrec
    · exact hab
    · have hlt :=
        precedes_idxOf_lt (isVertexOrder_nodup horder) hbaPrec
      have hle :
          order.idxOf (firstInFinset R hR order) ≤ order.idxOf b := by
        unfold firstInFinset
        exact Function.argminOn_le
          (fun x : V => order.idxOf x) (↑R : Set V) hb
      rw [hfirst] at hle
      omega
  · rintro ⟨ha, hprec⟩
    let m := firstInFinset R hR order
    have hm : m ∈ R := firstInFinset_mem R hR order
    by_contra hma
    have ham : Precedes order a m := hprec m hm hma
    have hlt := precedes_idxOf_lt (isVertexOrder_nodup horder) ham
    have hle : order.idxOf m ≤ order.idxOf a := by
      dsimp [m]
      unfold firstInFinset
      exact Function.argminOn_le
        (fun x : V => order.idxOf x) (↑R : Set V) ha
    omega

theorem swap_mem_iff_of_mem
    {R : Finset V} {a b x : V} (ha : a ∈ R) (hb : b ∈ R) :
    Equiv.swap a b x ∈ R ↔ x ∈ R := by
  by_cases hab : a = b
  · subst b
    simp
  · by_cases hxa : x = a
    · subst x
      simp [ha, hb]
    · by_cases hxb : x = b
      · subst x
        simp [ha, hb]
      · have hs : Equiv.swap a b x = x :=
          Equiv.swap_apply_of_ne_of_ne hxa hxb
        rw [hs]

/-- Orders whose first member of R is exactly a. -/
noncomputable def firstInFinsetOrders
    (R : Finset V) (hR : R.Nonempty) (a : V) : Finset (List V) := by
  classical
  exact (vertexOrders (V := V)).filter fun order =>
    firstInFinset R hR order = a

theorem mem_firstInFinsetOrders_iff
    {R : Finset V} {hR : R.Nonempty} {a : V} {order : List V} :
    order ∈ firstInFinsetOrders R hR a ↔
      IsVertexOrder order ∧ firstInFinset R hR order = a := by
  classical
  simp [firstInFinsetOrders, mem_vertexOrders_iff]

theorem firstInFinset_map_swap
    {R : Finset V} (hR : R.Nonempty)
    {a b : V} (ha : a ∈ R) (hb : b ∈ R) (hab : a ≠ b)
    {order : List V} (horder : IsVertexOrder order)
    (hfirst : firstInFinset R hR order = a) :
    firstInFinset R hR (order.map (Equiv.swap a b)) = b := by
  let σ : Equiv.Perm V := Equiv.swap a b
  apply (firstInFinset_eq_iff R hR
    (map_equiv_isVertexOrder σ horder) b).2
  refine ⟨hb, ?_⟩
  intro z hz hzb
  let y : V := σ.symm z
  have hyz : σ y = z := σ.apply_symm_apply z
  have hyR : y ∈ R := by
    apply (swap_mem_iff_of_mem ha hb).1
    simpa [σ, hyz] using hz
  have hya : y ≠ a := by
    intro hya
    apply hzb
    rw [← hyz, hya]
    simp [σ]
  have hsource :=
    ((firstInFinset_eq_iff R hR horder a).1 hfirst).2 y hyR hya
  have hmapped :
      Precedes (order.map σ) (σ a) (σ y) :=
    (precedes_map_equiv_iff σ order a y).2 hsource
  simpa [σ, hyz] using hmapped

theorem firstInFinsetOrders_card_eq
    {R : Finset V} (hR : R.Nonempty)
    {a b : V} (ha : a ∈ R) (hb : b ∈ R) :
    (firstInFinsetOrders R hR a).card =
      (firstInFinsetOrders R hR b).card := by
  classical
  by_cases hab : a = b
  · subst b
    rfl
  · let σ : Equiv.Perm V := Equiv.swap a b
    apply Finset.card_bij (fun order _ => order.map σ)
    · intro order hmem
      rcases (mem_firstInFinsetOrders_iff).1 hmem with
        ⟨horder, hfirst⟩
      apply (mem_firstInFinsetOrders_iff).2
      refine ⟨map_equiv_isVertexOrder σ horder, ?_⟩
      simpa [σ] using
        (firstInFinset_map_swap hR ha hb hab horder hfirst)
    · intro x hx y hy hxy
      exact (List.map_injective_iff.mpr σ.injective) hxy
    · intro order hmem
      rcases (mem_firstInFinsetOrders_iff).1 hmem with
        ⟨horder, hfirst⟩
      refine ⟨order.map σ, ?_, ?_⟩
      · apply (mem_firstInFinsetOrders_iff).2
        refine ⟨map_equiv_isVertexOrder σ horder, ?_⟩
        have hback :=
          firstInFinset_map_swap hR hb ha hab.symm horder hfirst
        simpa [σ, Equiv.swap_comm] using hback
      · simpa [List.map_map, Function.comp_def, σ] using
          (rfl : order = order)

/-- Exact first-element count in a nonempty finite relevant set. -/
theorem card_mul_firstInFinsetOrders_card
    (R : Finset V) (hR : R.Nonempty) (a : V) (ha : a ∈ R) :
    R.card * (firstInFinsetOrders R hR a).card =
      (vertexOrders (V := V)).card := by
  classical
  have hpart :
      (vertexOrders (V := V)).card =
        ∑ b ∈ R, (firstInFinsetOrders R hR b).card := by
    simpa [firstInFinsetOrders] using
      (Finset.card_eq_sum_card_fiberwise
        (f := firstInFinset R hR)
        (s := vertexOrders (V := V))
        (t := R)
        (by
          intro order horder
          exact firstInFinset_mem R hR order))
  calc
    R.card * (firstInFinsetOrders R hR a).card =
        ∑ b ∈ R, (firstInFinsetOrders R hR a).card := by
          simp
    _ = ∑ b ∈ R, (firstInFinsetOrders R hR b).card := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [firstInFinsetOrders_card_eq hR ha hb]
    _ = (vertexOrders (V := V)).card := hpart.symm

end GreedyUniformity
