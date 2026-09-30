module

public import GreedyUniformity.MixedSpiderTuned

public section

namespace GreedyUniformity

open MixedSpiderVertex

section MixedSpiderCertificates

variable {k l : ℕ}

/-- Exact finite-order conditions for a non-centre arm pattern. -/
def MixedSpiderNoncenterOrderCertificate
    (S : Finset (Fin k)) (order : List (MixedSpiderVertex k l)) : Prop :=
  IsVertexOrder order ∧
    (∀ i ∈ S, Precedes order (inner i) (outer i)) ∧
    (∀ i ∉ S, Precedes order (outer i) (inner i)) ∧
    ((∃ r : Fin l, Precedes order (leaf r) center) ∨
      ∃ i ∈ S, Precedes order (inner i) center)

/-- Exact finite-order conditions for the unique centre-containing output. -/
def MixedSpiderCenterOrderCertificate
    (order : List (MixedSpiderVertex k l)) : Prop :=
  IsVertexOrder order ∧
    (∀ r : Fin l, Precedes order center (leaf r)) ∧
    (∀ i : Fin k,
      Precedes order center (inner i) ∨
        Precedes order (outer i) (inner i))

theorem priorityCertificate_mixedSpiderNoncenter_iff
    (hl : 0 < l) (S : Finset (Fin k))
    (order : List (MixedSpiderVertex k l)) :
    PriorityCertificate (mixedSpider k l)
        (mixedSpiderNoncenterSet (l := l) S) order ↔
      MixedSpiderNoncenterOrderCertificate S order := by
  constructor
  · rintro ⟨horder, hmax, hprio⟩
    refine ⟨horder, ?_, ?_, ?_⟩
    · intro i hi
      have hout : outer i ∉ mixedSpiderNoncenterSet (l := l) S := by
        simpa using hi
      rcases hprio hout with ⟨u, hu, hadj, hprec⟩
      have huEq : u = inner i := (mixedSpider_adj_outer_iff u i).1 hadj
      simpa [huEq] using hprec
    · intro i hi
      have hin : inner i ∉ mixedSpiderNoncenterSet (l := l) S := by
        simpa using hi
      rcases hprio hin with ⟨u, hu, hadj, hprec⟩
      rcases (mixedSpider_adj_inner_iff u i).1 hadj with huEq | huEq
      · subst u
        simpa using hu
      · simpa [huEq] using hprec
    · have hc : (center : MixedSpiderVertex k l) ∉
          mixedSpiderNoncenterSet (l := l) S := by simp
      rcases hprio hc with ⟨u, hu, hadj, hprec⟩
      cases u with
      | center => simpa using hu
      | inner i =>
          right
          have hi : i ∈ S := by simpa using hu
          exact ⟨i, hi, hprec⟩
      | outer i =>
          exfalso
          exact (mixedSpider_not_adj_center_outer (k := k) (l := l) i)
            ((mixedSpider k l).adj_symm hadj)
      | leaf r =>
          left
          exact ⟨r, hprec⟩
  · rintro ⟨horder, hinner, houter, hcenter⟩
    refine ⟨horder, mixedSpiderNoncenterSet_maximal hl S, ?_⟩
    intro w hw
    cases w with
    | center =>
        rcases hcenter with ⟨r, hr⟩ | ⟨i, hi, hprec⟩
        · exact ⟨leaf r, by simp, by simp, hr⟩
        · exact ⟨inner i, by simpa using hi, by simp, hprec⟩
    | inner i =>
        by_cases hi : i ∈ S
        · exact (hw (by simpa using hi)).elim
        · exact ⟨outer i, by simpa using hi, by simp, houter i hi⟩
    | outer i =>
        by_cases hi : i ∈ S
        · exact ⟨inner i, by simpa using hi, by simp, hinner i hi⟩
        · exact (hw (by simpa using hi)).elim
    | leaf r =>
        exact (hw (by simp)).elim

theorem priorityCertificate_mixedSpiderCenter_iff
    (order : List (MixedSpiderVertex k l)) :
    PriorityCertificate (mixedSpider k l)
        (mixedSpiderCenterSet k l) order ↔
      MixedSpiderCenterOrderCertificate order := by
  constructor
  · rintro ⟨horder, hmax, hprio⟩
    refine ⟨horder, ?_, ?_⟩
    · intro r
      have hleaf : leaf r ∉ mixedSpiderCenterSet k l := by simp
      rcases hprio hleaf with ⟨u, hu, hadj, hprec⟩
      have huEq : u = center := (mixedSpider_adj_leaf_iff u r).1 hadj
      simpa [huEq] using hprec
    · intro i
      have hinner : inner i ∉ mixedSpiderCenterSet k l := by simp
      rcases hprio hinner with ⟨u, hu, hadj, hprec⟩
      rcases (mixedSpider_adj_inner_iff u i).1 hadj with huEq | huEq
      · left
        simpa [huEq] using hprec
      · right
        simpa [huEq] using hprec
  · rintro ⟨horder, hleaf, hinner⟩
    refine ⟨horder, mixedSpiderCenterSet_maximal, ?_⟩
    intro w hw
    cases w with
    | center =>
        exact (hw (by simp)).elim
    | inner i =>
        rcases hinner i with hci | hoi
        · exact ⟨center, by simp, by simp, hci⟩
        · exact ⟨outer i, by simp, by simp, hoi⟩
    | outer i =>
        exact (hw (by simp)).elim
    | leaf r =>
        exact ⟨center, by simp, by simp, hleaf r⟩

/-- Greedy-output form of the non-centre order certificate. -/
theorem greedyOutput_mixedSpiderNoncenter_iff
    (hl : 0 < l) (S : Finset (Fin k))
    {order : List (MixedSpiderVertex k l)} (horder : IsVertexOrder order) :
    greedyOutput (mixedSpider k l) order =
        mixedSpiderNoncenterSet (l := l) S ↔
      MixedSpiderNoncenterOrderCertificate S order := by
  rw [← priorityCertificate_iff_greedyOutput_eq (mixedSpider k l) horder]
  exact priorityCertificate_mixedSpiderNoncenter_iff hl S order

/-- Greedy-output form of the centre order certificate. -/
theorem greedyOutput_mixedSpiderCenter_iff
    {order : List (MixedSpiderVertex k l)} (horder : IsVertexOrder order) :
    greedyOutput (mixedSpider k l) order =
        mixedSpiderCenterSet k l ↔
      MixedSpiderCenterOrderCertificate order := by
  rw [← priorityCertificate_iff_greedyOutput_eq (mixedSpider k l) horder]
  exact priorityCertificate_mixedSpiderCenter_iff order

end MixedSpiderCertificates

end GreedyUniformity
