/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.CenterWeight
import Kourovka.Paths

namespace Kourovka
namespace ProductPaths

variable {A B : Type*} [Group A] [Group B]

/-- A child range inside its parent range, before a surjective change of input. -/
def branch (k : A × B →* A × B) (i : Bool) : A × B →* k.range :=
  k.rangeRestrict.comp (axis i)

theorem branch_commute (k : A × B →* A × B)
    (p : (branch k false).range) (q : (branch k true).range) :
    Commute (p : k.range) (q : k.range) := by
  obtain ⟨x, hx⟩ := p.property
  obtain ⟨y, hy⟩ := q.property
  rw [← hx, ← hy]
  exact (axes_commute x y).map k.rangeRestrict

theorem branch_cover (k : A × B →* A × B) (g : k.range) :
    ∃ p : (branch k false).range, ∃ q : (branch k true).range,
      (p : k.range) * q = g := by
  obtain ⟨x, hx⟩ := k.rangeRestrict_surjective g
  refine ⟨⟨branch k false x, ⟨x, rfl⟩⟩, ⟨branch k true x, ⟨x, rfl⟩⟩, ?_⟩
  change k.rangeRestrict (axis false x) * k.rangeRestrict (axis true x) = g
  rw [← map_mul, axis_product, hx]

private theorem range_comp_surjective {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (hf : Function.Surjective f) :
    (g.comp f).range = g.range := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨f x, rfl⟩
  · rintro z ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, rfl⟩

/-- A surjective input map leaves each child range unchanged. -/
noncomputable def branchEquiv (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (i : Bool) :
    (branch (path f w) i).range ≃* (path f (w ++ [i])).range :=
  (CenterWeight.rangeCompEquiv (branch (path f w) i) (path f w).range.subtype
    Subtype.val_injective).trans (MulEquiv.subgroupCongr (by
      change ((path f w).comp (axis i)).range = (path f (w ++ [i])).range
      rw [path_append]
      change ((path f w).comp (axis i)).range =
        (((path f w).comp (axis i)).comp f).range
      exact (range_comp_surjective f ((path f w).comp (axis i)) hf).symm))

noncomputable def pathWeight (f : A × B →* A × B) (w : List Bool) : ℕ :=
  CenterWeight.weight (path f w).range

/-- The root budget is an invariant of the product, independent of the endomorphism. -/
theorem pathWeight_nil (f : A × B →* A × B) :
    pathWeight f [] = CenterWeight.weight (A × B) :=
  (CenterWeight.weight_congr
    (MonoidHom.ofInjective (f := MonoidHom.id (A × B)) Function.injective_id)).symm

/-- The finite budget splits between the two children of every path. -/
theorem children_weight_le [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f) (w : List Bool) :
    pathWeight f (w ++ [false]) + pathWeight f (w ++ [true]) ≤ pathWeight f w := by
  have h := CenterWeight.split (branch (path f w) false).range
    (branch (path f w) true).range (branch_commute (path f w)) (branch_cover (path f w))
  rw [CenterWeight.weight_congr (branchEquiv f hf w false),
    CenterWeight.weight_congr (branchEquiv f hf w true)] at h
  exact h

/-- A nonabelian path uses at least one unit of the finite budget. -/
theorem pathWeight_pos [Group.FG A] [Group.FG B] [IsSolvable A] [IsSolvable B]
    (f : A × B →* A × B) (w : List Bool) (h : Nonabelian f w) :
    0 < pathWeight f w := by
  obtain ⟨x, y, hxy⟩ := h
  apply CenterWeight.weight_pos
  refine ⟨(path f w).rangeRestrict x, (path f w).rangeRestrict y, ?_⟩
  intro hc
  exact hxy (hc.map (path f w).range.subtype)

end ProductPaths
end Kourovka
