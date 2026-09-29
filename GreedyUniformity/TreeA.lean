import GreedyUniformity.Counting

namespace GreedyUniformity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Structural form of the diameter-end argument used in Frozen Theorem A.
For a longest path of length at least two in a tree, every neighbour of the
second vertex except the third path vertex is a leaf. -/
theorem tree_maximalPath_pendantStar
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length)
    (hlen : 2 ≤ p.length) :
    ∃ y z : V,
      G.Adj u y ∧ G.Adj y z ∧ u ≠ z ∧ G.degree u = 1 ∧
        ∀ w : V, G.Adj y w → w ≠ z → G.degree w = 1 := by
  have hnil : ¬ p.Nil := by
    intro h
    have hz := h.length_eq_zero
    lia
  have htailnil : ¬ p.tail.Nil := by
    intro h
    have hz := h.length_eq_zero
    have hlen' := p.length_tail_add_one hnil
    lia
  let y : V := p.snd
  let z : V := p.tail.snd
  have huy : G.Adj u y := by
    simpa [y] using p.adj_snd hnil
  have hyz : G.Adj y z := by
    simpa [y, z] using p.tail.adj_snd htailnil
  have hdeg_u : G.degree u = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨y, huy, ?_⟩
    intro w hadj
    apply hT.isAcyclic.eq_snd_of_adj_start hp hadj
    have hnot : ¬ (p.cons hadj.symm).IsPath := by
      intro hpath
      have hle := hmax _ _ _ hpath
      simp only [SimpleGraph.Walk.length_cons] at hle
      lia
    by_contra hw
    exact hnot (hp.cons hw)
  have hu_not_tail : u ∉ p.tail.support := by
    have hp' := hp
    rw [← p.cons_tail_eq hnil] at hp'
    exact (SimpleGraph.Walk.cons_isPath_iff _ _).1 hp' |>.2
  have huz : u ≠ z := by
    intro huz
    apply hu_not_tail
    have hzmem : z ∈ p.tail.support := by
      simpa [z] using p.tail.snd_mem_support
    simpa only [← huz] using hzmem
  refine ⟨y, z, huy, hyz, huz, hdeg_u, ?_⟩
  intro w hyw hwz
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  refine ⟨y, hyw.symm, ?_⟩
  intro t hwt
  by_cases hty : t = y
  · exact hty
  have hw_not_tail : w ∉ p.tail.support := by
    intro hwmem
    have heq :=
      hT.isAcyclic.eq_snd_of_adj_start hp.tail (by simpa [y] using hyw) hwmem
    exact hwz (by simpa [z] using heq)
  have hrpath : (p.tail.cons hyw.symm).IsPath := by
    exact hp.tail.cons hw_not_tail
  by_cases htmem : t ∈ (p.tail.cons hyw.symm).support
  · have heq :=
      hT.isAcyclic.eq_snd_of_adj_start hrpath hwt htmem
    simpa [y] using heq
  · have hspath : ((p.tail.cons hyw.symm).cons hwt.symm).IsPath := by
      exact hrpath.cons htmem
    have hle := hmax _ _ _ hspath
    have hlen' := p.length_tail_add_one hnil
    simp only [SimpleGraph.Walk.length_cons] at hle
    lia

end GreedyUniformity
