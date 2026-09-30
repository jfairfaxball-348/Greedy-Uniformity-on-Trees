module

public import GreedyUniformity.Bridge

@[expose] public section

namespace GreedyUniformity

/-- Canonical vertex type for the mixed spider T_{k,l}: one centre, k inner
arm vertices, k outer arm vertices, and l direct leaves. -/
inductive MixedSpiderVertex (k l : ℕ)
  | center
  | inner (i : Fin k)
  | outer (i : Fin k)
  | leaf (r : Fin l)
  deriving DecidableEq, Fintype

/-- An oriented generating relation for the mixed spider. SimpleGraph.fromRel
adds the reverse directions and removes loops. -/
def mixedSpiderRel {k l : ℕ} :
    MixedSpiderVertex k l → MixedSpiderVertex k l → Prop
  | .center, .inner _ => True
  | .inner i, .outer j => i = j
  | .center, .leaf _ => True
  | _, _ => False

/-- The mixed spider T_{k,l}. -/
def mixedSpider (k l : ℕ) : SimpleGraph (MixedSpiderVertex k l) :=
  SimpleGraph.fromRel mixedSpiderRel

@[simp] theorem mixedSpider_adj_center_inner
    {k l : ℕ} (i : Fin k) :
    (mixedSpider k l).Adj .center (.inner i) := by
  simp [mixedSpider, mixedSpiderRel]

@[simp] theorem mixedSpider_adj_inner_center
    {k l : ℕ} (i : Fin k) :
    (mixedSpider k l).Adj (.inner i) .center := by
  simpa [SimpleGraph.adj_comm] using
    (mixedSpider_adj_center_inner (k := k) (l := l) i)

@[simp] theorem mixedSpider_adj_inner_outer_iff
    {k l : ℕ} (i j : Fin k) :
    (mixedSpider k l).Adj (.inner i) (.outer j) ↔ i = j := by
  simp [mixedSpider, mixedSpiderRel]

@[simp] theorem mixedSpider_adj_outer_inner_iff
    {k l : ℕ} (i j : Fin k) :
    (mixedSpider k l).Adj (.outer i) (.inner j) ↔ i = j := by
  rw [SimpleGraph.adj_comm]
  simpa [eq_comm] using
    (mixedSpider_adj_inner_outer_iff (k := k) (l := l) j i)

@[simp] theorem mixedSpider_adj_center_leaf
    {k l : ℕ} (r : Fin l) :
    (mixedSpider k l).Adj .center (.leaf r) := by
  simp [mixedSpider, mixedSpiderRel]

@[simp] theorem mixedSpider_adj_leaf_center
    {k l : ℕ} (r : Fin l) :
    (mixedSpider k l).Adj (.leaf r) .center := by
  simpa [SimpleGraph.adj_comm] using
    (mixedSpider_adj_center_leaf (k := k) (l := l) r)

@[simp] theorem mixedSpider_not_adj_center_outer
    {k l : ℕ} (i : Fin k) :
    ¬ (mixedSpider k l).Adj .center (.outer i) := by
  simp [mixedSpider, mixedSpiderRel]

@[simp] theorem mixedSpider_not_adj_inner_leaf
    {k l : ℕ} (i : Fin k) (r : Fin l) :
    ¬ (mixedSpider k l).Adj (.inner i) (.leaf r) := by
  simp [mixedSpider, mixedSpiderRel]

@[simp] theorem mixedSpider_not_adj_outer_leaf
    {k l : ℕ} (i : Fin k) (r : Fin l) :
    ¬ (mixedSpider k l).Adj (.outer i) (.leaf r) := by
  simp [mixedSpider, mixedSpiderRel]

/-- Explicit constructor-level equivalence used for cardinal arithmetic. -/
def mixedSpiderVertexEquiv (k l : ℕ) :
    MixedSpiderVertex k l ≃ Unit ⊕ (Fin k ⊕ (Fin k ⊕ Fin l)) where
  toFun
    | .center => Sum.inl ()
    | .inner i => Sum.inr (Sum.inl i)
    | .outer i => Sum.inr (Sum.inr (Sum.inl i))
    | .leaf r => Sum.inr (Sum.inr (Sum.inr r))
  invFun
    | Sum.inl _ => .center
    | Sum.inr (Sum.inl i) => .inner i
    | Sum.inr (Sum.inr (Sum.inl i)) => .outer i
    | Sum.inr (Sum.inr (Sum.inr r)) => .leaf r
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with x | x
    · cases x
      rfl
    · rcases x with x | x
      · rfl
      · rcases x with x | x <;> rfl

theorem mixedSpiderVertex_card (k l : ℕ) :
    Fintype.card (MixedSpiderVertex k l) = 2 * k + l + 1 := by
  calc
    Fintype.card (MixedSpiderVertex k l) =
        Fintype.card (Unit ⊕ (Fin k ⊕ (Fin k ⊕ Fin l))) :=
      Fintype.card_congr (mixedSpiderVertexEquiv k l)
    _ = 2 * k + l + 1 := by
      simp
      omega

end GreedyUniformity
