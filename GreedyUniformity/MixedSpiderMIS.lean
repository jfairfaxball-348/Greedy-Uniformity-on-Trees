import GreedyUniformity.MixedSpider

namespace GreedyUniformity

open MixedSpiderVertex

section MixedSpiderMIS

variable {k l : ℕ}

/-- The unique maximal independent set containing the centre. -/
noncomputable def mixedSpiderCenterSet (k l : ℕ) :
    Finset (MixedSpiderVertex k l) := by
  classical
  exact Finset.univ.filter fun v =>
    match v with
    | .center => True
    | .outer _ => True
    | _ => False

/-- A non-centre maximal-set candidate. The finset S records the arms on which
the inner vertex is chosen; all direct leaves are chosen, and all remaining
arms choose their outer vertex. -/
noncomputable def mixedSpiderNoncenterSet
    (S : Finset (Fin k)) : Finset (MixedSpiderVertex k l) := by
  classical
  exact Finset.univ.filter fun v =>
    match v with
    | .center => False
    | .inner i => i ∈ S
    | .outer i => i ∉ S
    | .leaf _ => True

@[simp] theorem center_mem_mixedSpiderCenterSet :
    (center : MixedSpiderVertex k l) ∈ mixedSpiderCenterSet k l := by
  simp [mixedSpiderCenterSet]

@[simp] theorem inner_not_mem_mixedSpiderCenterSet (i : Fin k) :
    inner i ∉ mixedSpiderCenterSet k l := by
  simp [mixedSpiderCenterSet]

@[simp] theorem outer_mem_mixedSpiderCenterSet (i : Fin k) :
    outer i ∈ mixedSpiderCenterSet k l := by
  simp [mixedSpiderCenterSet]

@[simp] theorem leaf_not_mem_mixedSpiderCenterSet (r : Fin l) :
    leaf r ∉ mixedSpiderCenterSet k l := by
  simp [mixedSpiderCenterSet]

@[simp] theorem center_not_mem_mixedSpiderNoncenterSet (S : Finset (Fin k)) :
    (center : MixedSpiderVertex k l) ∉ mixedSpiderNoncenterSet (l := l) S := by
  simp [mixedSpiderNoncenterSet]

@[simp] theorem inner_mem_mixedSpiderNoncenterSet_iff
    (S : Finset (Fin k)) (i : Fin k) :
    inner i ∈ mixedSpiderNoncenterSet (l := l) S ↔ i ∈ S := by
  simp [mixedSpiderNoncenterSet]

@[simp] theorem outer_mem_mixedSpiderNoncenterSet_iff
    (S : Finset (Fin k)) (i : Fin k) :
    outer i ∈ mixedSpiderNoncenterSet (l := l) S ↔ i ∉ S := by
  simp [mixedSpiderNoncenterSet]

@[simp] theorem leaf_mem_mixedSpiderNoncenterSet
    (S : Finset (Fin k)) (r : Fin l) :
    leaf r ∈ mixedSpiderNoncenterSet (l := l) S := by
  simp [mixedSpiderNoncenterSet]

@[simp] theorem mixedSpider_adj_outer_iff (x : MixedSpiderVertex k l) (i : Fin k) :
    (mixedSpider k l).Adj x (outer i) ↔ x = inner i := by
  cases x <;> simp [mixedSpider, mixedSpiderRel, eq_comm]

@[simp] theorem mixedSpider_adj_leaf_iff (x : MixedSpiderVertex k l) (r : Fin l) :
    (mixedSpider k l).Adj x (leaf r) ↔ x = center := by
  cases x <;> simp [mixedSpider, mixedSpiderRel]

@[simp] theorem mixedSpider_adj_inner_iff (x : MixedSpiderVertex k l) (i : Fin k) :
    (mixedSpider k l).Adj x (inner i) ↔ x = center ∨ x = outer i := by
  cases x <;> simp [mixedSpider, mixedSpiderRel, eq_comm]

theorem mixedSpiderCenterSet_independent :
    IsIndependent (mixedSpider k l) (mixedSpiderCenterSet k l) := by
  intro u hu v hv
  cases u <;> cases v <;>
    simp_all [mixedSpiderCenterSet, mixedSpider, mixedSpiderRel]

theorem mixedSpiderNoncenterSet_independent (S : Finset (Fin k)) :
    IsIndependent (mixedSpider k l) (mixedSpiderNoncenterSet (l := l) S) := by
  intro u hu v hv
  cases u <;> cases v <;>
    simp_all [mixedSpiderNoncenterSet, mixedSpider, mixedSpiderRel] <;> aesop

theorem mixedSpiderCenterSet_maximal :
    IsMaximalIndependent (mixedSpider k l) (mixedSpiderCenterSet k l) := by
  refine ⟨by simp, mixedSpiderCenterSet_independent, ?_⟩
  intro w _ hw
  cases w with
  | center =>
      exact (hw (by simp)).elim
  | inner i =>
      exact ⟨center, by simp, by simp⟩
  | outer i =>
      exact (hw (by simp)).elim
  | leaf r =>
      exact ⟨center, by simp, by simp⟩

theorem mixedSpiderNoncenterSet_maximal
    (hl : 0 < l) (S : Finset (Fin k)) :
    IsMaximalIndependent (mixedSpider k l) (mixedSpiderNoncenterSet (l := l) S) := by
  refine ⟨by simp, mixedSpiderNoncenterSet_independent S, ?_⟩
  intro w _ hw
  cases w with
  | center =>
      let r : Fin l := ⟨0, hl⟩
      exact ⟨leaf r, by simp, by simp⟩
  | inner i =>
      by_cases hi : i ∈ S
      · exact (hw (by simpa using hi)).elim
      · exact ⟨outer i, by simpa using hi, by simp⟩
  | outer i =>
      by_cases hi : i ∈ S
      · exact ⟨inner i, by simpa using hi, by simp⟩
      · exact (hw (by simpa using hi)).elim
  | leaf r =>
      exact (hw (by simp)).elim

theorem mixedSpiderNoncenterSet_injective :
    Function.Injective (mixedSpiderNoncenterSet (k := k) (l := l)) := by
  intro S T hST
  ext i
  have hmem := congrArg (fun I : Finset (MixedSpiderVertex k l) => inner i ∈ I) hST
  simpa using hmem

noncomputable def mixedSpiderNoncenterEmbedding :
    Finset (Fin k) ↪ Finset (MixedSpiderVertex k l) :=
  ⟨mixedSpiderNoncenterSet (k := k) (l := l),
    mixedSpiderNoncenterSet_injective (k := k) (l := l)⟩

/-- Structural classification of every maximal independent set of T_{k,l}.
The hypothesis l>0 is exactly the frozen mixed-spider regime. -/
theorem isMaximalIndependent_mixedSpider_iff
    (hl : 0 < l) (I : Finset (MixedSpiderVertex k l)) :
    IsMaximalIndependent (mixedSpider k l) I ↔
      I = mixedSpiderCenterSet k l ∨
        ∃ S : Finset (Fin k), I = mixedSpiderNoncenterSet (l := l) S := by
  constructor
  · intro hI
    by_cases hc : center ∈ I
    · left
      have hinner : ∀ i : Fin k, inner i ∉ I := by
        intro i hi
        exact hI.2.1 hc hi (by simp)
      have hleaf : ∀ r : Fin l, leaf r ∉ I := by
        intro r hr
        exact hI.2.1 hc hr (by simp)
      have houter : ∀ i : Fin k, outer i ∈ I := by
        intro i
        by_contra ho
        rcases hI.2.2 (by simp) ho with ⟨u, hu, hadj⟩
        have huEq : u = inner i := (mixedSpider_adj_outer_iff u i).1 hadj
        subst u
        exact hinner i hu
      ext w
      cases w with
      | center => simp [hc]
      | inner i => simp [hinner i]
      | outer i => simp [houter i]
      | leaf r => simp [hleaf r]
    · right
      let S : Finset (Fin k) := Finset.univ.filter fun i => inner i ∈ I
      have houter :
          ∀ i : Fin k, outer i ∈ I ↔ inner i ∉ I := by
        intro i
        constructor
        · intro ho hi
          exact hI.2.1 hi ho ((mixedSpider_adj_inner_outer_iff i i).2 rfl)
        · intro hi
          by_contra ho
          rcases hI.2.2 (by simp) ho with ⟨u, hu, hadj⟩
          have huEq : u = inner i := (mixedSpider_adj_outer_iff u i).1 hadj
          subst u
          exact hi hu
      have hleaf : ∀ r : Fin l, leaf r ∈ I := by
        intro r
        by_contra hr
        rcases hI.2.2 (by simp) hr with ⟨u, hu, hadj⟩
        have huEq : u = center := (mixedSpider_adj_leaf_iff u r).1 hadj
        subst u
        exact hc hu
      refine ⟨S, ?_⟩
      ext w
      cases w with
      | center => simp [hc]
      | inner i => simp [S]
      | outer i => simp [mixedSpiderNoncenterSet, S, houter i]
      | leaf r => simp [hleaf r]
  · rintro (rfl | ⟨S, rfl⟩)
    · exact mixedSpiderCenterSet_maximal
    · exact mixedSpiderNoncenterSet_maximal hl S

/-- The maximal independent sets are one centre set plus one non-centre set
for every subset of the k arms. -/
theorem maximalIndependentSets_mixedSpider_eq
    (hl : 0 < l) :
    maximalIndependentSets (mixedSpider k l) =
      insert (mixedSpiderCenterSet k l)
        ((Finset.univ : Finset (Finset (Fin k))).map
          (mixedSpiderNoncenterEmbedding (k := k) (l := l))) := by
  classical
  ext I
  simp [maximalIndependentSets, isMaximalIndependent_mixedSpider_iff hl,
    mixedSpiderNoncenterEmbedding, eq_comm]

/-- Frozen B1: T_{k,l} has exactly 2^k+1 maximal independent sets. -/
theorem mixedSpider_maximalIndependentSets_card
    (hl : 0 < l) :
    (maximalIndependentSets (mixedSpider k l)).card = 2 ^ k + 1 := by
  classical
  rw [maximalIndependentSets_mixedSpider_eq hl]
  have hnot :
      mixedSpiderCenterSet k l ∉
        (Finset.univ : Finset (Finset (Fin k))).map
          (mixedSpiderNoncenterEmbedding (k := k) (l := l)) := by
    intro hmem
    rcases Finset.mem_map.1 hmem with ⟨S, _, hEq⟩
    have hmemEq :=
      congrArg (fun I : Finset (MixedSpiderVertex k l) => center ∈ I) hEq
    simpa [mixedSpiderNoncenterEmbedding] using hmemEq
  rw [Finset.card_insert_of_notMem hnot]
  simp [mixedSpiderNoncenterEmbedding]

end MixedSpiderMIS

end GreedyUniformity
