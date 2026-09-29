import GreedyUniformity.Bridge

namespace GreedyUniformity

/-- Canonical vertex type for the mixed spider T_{k,l}: one centre, k inner
arm vertices, k outer arm vertices, and l direct leaves. -/
abbrev MixedSpiderVertex (k l : ℕ) :=
  Unit ⊕ (Fin k ⊕ (Fin k ⊕ Fin l))

def mixedSpiderCenter {k l : ℕ} : MixedSpiderVertex k l :=
  Sum.inl ()

def mixedSpiderInner {k l : ℕ} (i : Fin k) : MixedSpiderVertex k l :=
  Sum.inr (Sum.inl i)

def mixedSpiderOuter {k l : ℕ} (i : Fin k) : MixedSpiderVertex k l :=
  Sum.inr (Sum.inr (Sum.inl i))

def mixedSpiderLeaf {k l : ℕ} (r : Fin l) : MixedSpiderVertex k l :=
  Sum.inr (Sum.inr (Sum.inr r))

/-- An oriented generating relation for the mixed spider. SimpleGraph.fromRel
adds the reverse directions and removes loops. -/
def mixedSpiderRel {k l : ℕ} :
    MixedSpiderVertex k l → MixedSpiderVertex k l → Prop
  | Sum.inl _, Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr (Sum.inl j)) => i = j
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inr _)) => True
  | _, _ => False

/-- The mixed spider T_{k,l}. -/
def mixedSpider (k l : ℕ) : SimpleGraph (MixedSpiderVertex k l) :=
  SimpleGraph.fromRel mixedSpiderRel

@[simp] theorem mixedSpider_adj_center_inner
    {k l : ℕ} (i : Fin k) :
    (mixedSpider k l).Adj mixedSpiderCenter (mixedSpiderInner i) := by
  simp [mixedSpider, mixedSpiderRel, mixedSpiderCenter, mixedSpiderInner]

@[simp] theorem mixedSpider_adj_inner_center
    {k l : ℕ} (i : Fin k) :
    (mixedSpider k l).Adj (mixedSpiderInner i) mixedSpiderCenter := by
  simpa [SimpleGraph.adj_comm] using
    (mixedSpider_adj_center_inner (k := k) (l := l) i)

@[simp] theorem mixedSpider_adj_inner_outer_iff
    {k l : ℕ} (i j : Fin k) :
    (mixedSpider k l).Adj (mixedSpiderInner i) (mixedSpiderOuter j) ↔ i = j := by
  simp [mixedSpider, mixedSpiderRel, mixedSpiderInner, mixedSpiderOuter]

@[simp] theorem mixedSpider_adj_outer_inner_iff
    {k l : ℕ} (i j : Fin k) :
    (mixedSpider k l).Adj (mixedSpiderOuter i) (mixedSpiderInner j) ↔ i = j := by
  rw [SimpleGraph.adj_comm]
  simpa [eq_comm] using
    (mixedSpider_adj_inner_outer_iff (k := k) (l := l) j i)

@[simp] theorem mixedSpider_adj_center_leaf
    {k l : ℕ} (r : Fin l) :
    (mixedSpider k l).Adj mixedSpiderCenter (mixedSpiderLeaf r) := by
  simp [mixedSpider, mixedSpiderRel, mixedSpiderCenter, mixedSpiderLeaf]

@[simp] theorem mixedSpider_adj_leaf_center
    {k l : ℕ} (r : Fin l) :
    (mixedSpider k l).Adj (mixedSpiderLeaf r) mixedSpiderCenter := by
  simpa [SimpleGraph.adj_comm] using
    (mixedSpider_adj_center_leaf (k := k) (l := l) r)

@[simp] theorem mixedSpider_not_adj_center_outer
    {k l : ℕ} (i : Fin k) :
    ¬ (mixedSpider k l).Adj mixedSpiderCenter (mixedSpiderOuter i) := by
  simp [mixedSpider, mixedSpiderRel, mixedSpiderCenter, mixedSpiderOuter]

@[simp] theorem mixedSpider_not_adj_inner_leaf
    {k l : ℕ} (i : Fin k) (r : Fin l) :
    ¬ (mixedSpider k l).Adj (mixedSpiderInner i) (mixedSpiderLeaf r) := by
  simp [mixedSpider, mixedSpiderRel, mixedSpiderInner, mixedSpiderLeaf]

@[simp] theorem mixedSpider_not_adj_outer_leaf
    {k l : ℕ} (i : Fin k) (r : Fin l) :
    ¬ (mixedSpider k l).Adj (mixedSpiderOuter i) (mixedSpiderLeaf r) := by
  simp [mixedSpider, mixedSpiderRel, mixedSpiderOuter, mixedSpiderLeaf]

theorem mixedSpiderVertex_card (k l : ℕ) :
    Fintype.card (MixedSpiderVertex k l) = 2 * k + l + 1 := by
  simp [MixedSpiderVertex]
  omega

end GreedyUniformity
