import GreedyUniformity.Bridge

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def maximalIndependentSetsOn (G : SimpleGraph V) (S : Finset V) :
    Finset (Finset V) := by
  classical
  exact Finset.univ.filter (IsMaximalIndependentOn G S)

@[simp] theorem mem_maximalIndependentSetsOn_iff (G : SimpleGraph V)
    {S I : Finset V} :
    I ∈ maximalIndependentSetsOn G S ↔ IsMaximalIndependentOn G S I := by
  classical
  simp [maximalIndependentSetsOn]

theorem isIndependent_mono (G : SimpleGraph V) {I J : Finset V}
    (hI : IsIndependent G I) (hJI : J ⊆ I) :
    IsIndependent G J := by
  intro u hu v hv
  exact hI (hJI hu) (hJI hv)

theorem exists_maximalIndependentOn_superset (G : SimpleGraph V)
    {S J : Finset V} (hJS : J ⊆ S) (hJ : IsIndependent G J) :
    ∃ K : Finset V, IsMaximalIndependentOn G S K ∧ J ⊆ K := by
  classical
  let C : Finset (Finset V) := S.powerset.filter (IsIndependent G)
  have hJmem : J ∈ C := by
    simp [C, hJS, hJ]
  obtain ⟨K, hJK, hKmax⟩ := C.exists_le_maximal hJmem
  have hKmem : K ∈ C := hKmax.1
  have hKS : K ⊆ S := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hKmem).1
  have hKind : IsIndependent G K :=
    (Finset.mem_filter.mp hKmem).2
  refine ⟨K, ⟨hKS, hKind, ?_⟩, hJK⟩
  intro w hwS hwK
  by_contra hno
  push_neg at hno
  have hInsInd : IsIndependent G (insert w K) := by
    intro a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact G.irrefl hab
      · exact hno b hb (G.adj_symm hab)
    · rcases hb with rfl | hb
      · exact hno a ha hab
      · exact hKind ha hb hab
  have hInsC : insert w K ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, hInsInd⟩
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hwS
    · exact hKS hx
  have hback : insert w K ⊆ K :=
    hKmax.2 hInsC (Finset.subset_insert w K)
  exact hwK (hback (Finset.mem_insert_self w K))

noncomputable def maximalIndependentExtension (G : SimpleGraph V)
    (S J : Finset V) : Finset V := by
  classical
  if h : J ⊆ S ∧ IsIndependent G J then
    exact (exists_maximalIndependentOn_superset G h.1 h.2).choose
  else
    exact ∅

theorem maximalIndependentExtension_spec (G : SimpleGraph V)
    {S J : Finset V} (hJS : J ⊆ S) (hJ : IsIndependent G J) :
    IsMaximalIndependentOn G S (maximalIndependentExtension G S J) ∧
      J ⊆ maximalIndependentExtension G S J := by
  classical
  unfold maximalIndependentExtension
  rw [dif_pos ⟨hJS, hJ⟩]
  exact (exists_maximalIndependentOn_superset G hJS hJ).choose_spec

theorem maximalIndependentOn_erase_of_not_mem (G : SimpleGraph V)
    {S I : Finset V} {z : V}
    (hI : IsMaximalIndependentOn G S I) (hz : z ∉ I) :
    IsMaximalIndependentOn G (S.erase z) I := by
  refine ⟨?_, hI.2.1, ?_⟩
  · intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxz => hz (hxz ▸ hx), hI.1 hx⟩
  · intro w hw hwI
    exact hI.2.2 (Finset.mem_of_mem_erase hw) hwI

noncomputable def nonneighborsIn (G : SimpleGraph V) (S : Finset V) (z : V) :
    Finset V := by
  classical
  exact S.filter fun w => ¬ G.Adj z w

theorem erase_eq_inter_nonneighbors_of_extension (G : SimpleGraph V)
    {S I K : Finset V} {z : V}
    (hI : IsMaximalIndependentOn G S I) (hz : z ∈ I)
    (hK : IsMaximalIndependentOn G (S.erase z) K)
    (hsub : I.erase z ⊆ K) :
    I.erase z = K ∩ nonneighborsIn G (S.erase z) z := by
  classical
  ext x
  constructor
  · intro hx
    have hxe := Finset.mem_erase.mp hx
    have hxK : x ∈ K := hsub hx
    have hxNoAdj : ¬ G.Adj z x :=
      hI.2.1 hz hxe.2
    exact Finset.mem_inter.mpr
      ⟨hxK, by
        simp only [nonneighborsIn, Finset.mem_filter]
        exact ⟨Finset.mem_erase.mpr ⟨hxe.1, hI.1 hxe.2⟩, hxNoAdj⟩⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxK, hxF⟩
    have hxF' :
        x ∈ S.erase z ∧ ¬ G.Adj z x := by
      simpa only [nonneighborsIn, Finset.mem_filter] using hxF
    rcases hxF' with ⟨hxSz, hxNoAdj⟩
    rcases Finset.mem_erase.mp hxSz with ⟨hxne, hxS⟩
    have hxI : x ∈ I := by
      by_contra hxi
      rcases hI.2.2 hxS hxi with ⟨a, haI, hadj⟩
      have haz : a ≠ z := by
        intro haz
        subst a
        exact hxNoAdj hadj
      have haErase : a ∈ I.erase z :=
        Finset.mem_erase.mpr ⟨haz, haI⟩
      exact hK.2.1 (hsub haErase) hxK hadj
    exact Finset.mem_erase.mpr ⟨hxne, hxI⟩

theorem maximalIndependentSetsOn_card_le_two_mul_erase
    (G : SimpleGraph V) (S : Finset V) (z : V) :
    (maximalIndependentSetsOn G S).card ≤
      2 * (maximalIndependentSetsOn G (S.erase z)).card := by
  classical
  let A := maximalIndependentSetsOn G S
  let B := maximalIndependentSetsOn G (S.erase z)
  let encode : Finset V → Bool × Finset V := fun I =>
    if z ∈ I then
      (true, maximalIndependentExtension G (S.erase z) (I.erase z))
    else
      (false, I)
  have hmaps :
      Set.MapsTo encode (A : Set (Finset V))
        ((((Finset.univ : Finset Bool) ×ˢ B) :
          Finset (Bool × Finset V)) : Set (Bool × Finset V)) := by
    intro I hIA
    have hI : IsMaximalIndependentOn G S I := by
      exact (mem_maximalIndependentSetsOn_iff G).1 hIA
    change encode I ∈ ((Finset.univ : Finset Bool) ×ˢ B)
    rw [Finset.mem_product]
    constructor
    · exact Finset.mem_univ _
    · by_cases hz : z ∈ I
      · rw [show encode I =
          (true, maximalIndependentExtension G (S.erase z) (I.erase z)) by
            simp [encode, hz]]
        simp only
        have hsub : I.erase z ⊆ S.erase z := by
          intro x hx
          have hxe := Finset.mem_erase.mp hx
          exact Finset.mem_erase.mpr ⟨hxe.1, hI.1 hxe.2⟩
        have hind : IsIndependent G (I.erase z) :=
          isIndependent_mono G hI.2.1 (Finset.erase_subset z I)
        exact (mem_maximalIndependentSetsOn_iff G).2
          (maximalIndependentExtension_spec G hsub hind).1
      · rw [show encode I = (false, I) by simp [encode, hz]]
        exact (mem_maximalIndependentSetsOn_iff G).2
          (maximalIndependentOn_erase_of_not_mem G hI hz)
  have hinj : (A : Set (Finset V)).InjOn encode := by
    intro I hIA J hJA heq
    have hI : IsMaximalIndependentOn G S I :=
      (mem_maximalIndependentSetsOn_iff G).1 hIA
    have hJ : IsMaximalIndependentOn G S J :=
      (mem_maximalIndependentSetsOn_iff G).1 hJA
    by_cases hi : z ∈ I
    · by_cases hj : z ∈ J
      · have hsecond := congrArg Prod.snd heq
        have hKIJ :
            maximalIndependentExtension G (S.erase z) (I.erase z) =
              maximalIndependentExtension G (S.erase z) (J.erase z) := by
          simpa [encode, hi, hj] using hsecond
        have hIsub : I.erase z ⊆ S.erase z := by
          intro x hx
          have hxe := Finset.mem_erase.mp hx
          exact Finset.mem_erase.mpr ⟨hxe.1, hI.1 hxe.2⟩
        have hJsub : J.erase z ⊆ S.erase z := by
          intro x hx
          have hxe := Finset.mem_erase.mp hx
          exact Finset.mem_erase.mpr ⟨hxe.1, hJ.1 hxe.2⟩
        have hIind : IsIndependent G (I.erase z) :=
          isIndependent_mono G hI.2.1 (Finset.erase_subset z I)
        have hJind : IsIndependent G (J.erase z) :=
          isIndependent_mono G hJ.2.1 (Finset.erase_subset z J)
        have hIspec :=
          maximalIndependentExtension_spec G hIsub hIind
        have hJspec :=
          maximalIndependentExtension_spec G hJsub hJind
        have hIrec :=
          erase_eq_inter_nonneighbors_of_extension G hI hi hIspec.1 hIspec.2
        have hJrec :=
          erase_eq_inter_nonneighbors_of_extension G hJ hj hJspec.1 hJspec.2
        have herase : I.erase z = J.erase z := by
          rw [hIrec, hJrec, hKIJ]
        calc
          I = insert z (I.erase z) := (Finset.insert_erase hi).symm
          _ = insert z (J.erase z) := congrArg (insert z) herase
          _ = J := Finset.insert_erase hj
      · exfalso
        have hfirst := congrArg Prod.fst heq
        simpa [encode, hi, hj] using hfirst
    · by_cases hj : z ∈ J
      · exfalso
        have hfirst := congrArg Prod.fst heq
        simpa [encode, hi, hj] using hfirst
      · have hsecond := congrArg Prod.snd heq
        simpa [encode, hi, hj] using hsecond
  have hcard :
      A.card ≤ ((Finset.univ : Finset Bool) ×ˢ B).card :=
    Finset.card_le_card_of_injOn encode hmaps hinj
  simpa [A, B, Finset.card_product, Nat.mul_comm] using hcard

end GreedyUniformity
