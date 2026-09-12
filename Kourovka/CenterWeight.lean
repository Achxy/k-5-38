/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.SolvableWeight
import Kourovka.CentralProducts

namespace Kourovka
namespace CenterWeight

variable {G H : Type*} [Group G] [Group H]

/-- Isomorphisms induce isomorphisms of quotients by the center. -/
def quotientCongr (e : G ≃* H) : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro y hy
      refine ⟨e.symm y, (Subgroup.centerCongr e.symm ⟨y, hy⟩).property, ?_⟩
      exact e.apply_symm_apply y)

/-- A finite branching budget for commuting nonabelian factors. -/
noncomputable def weight (G : Type*) [Group G] : ℕ :=
  SolvableWeight.weight (G ⧸ Subgroup.center G)

theorem weight_congr (e : G ≃* H) : weight G = weight H :=
  SolvableWeight.weight_congr _ _ (quotientCongr e)

theorem quotient_nontrivial (h : ∃ x y : G, ¬ Commute x y) :
    Nontrivial (G ⧸ Subgroup.center G) := by
  by_contra hn
  letI : Subsingleton (G ⧸ Subgroup.center G) := not_nontrivial_iff_subsingleton.mp hn
  obtain ⟨x, y, hxy⟩ := h
  have hx : x ∈ Subgroup.center G :=
    (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem weight_pos [Group.FG G] [IsSolvable G]
    (h : ∃ x y : G, ¬ Commute x y) : 0 < weight G := by
  letI := quotient_nontrivial h
  exact SolvableWeight.weight_pos _

/-- A commuting product splits its branching budget among its factors. -/
theorem split (P Q : Subgroup G) [Group.FG P] [Group.FG Q]
    (hc : ∀ p : P, ∀ q : Q, Commute (p : G) (q : G))
    (hcover : ∀ g : G, ∃ p : P, ∃ q : Q, (p : G) * q = g) :
    weight P + weight Q ≤ weight G := by
  have h := SolvableWeight.weight_add_le (P ⧸ Subgroup.center P) (Q ⧸ Subgroup.center Q)
  rw [SolvableWeight.weight_congr _ _ (CentralProducts.quotientEquiv P Q hc hcover)] at h
  exact h

/-- Injective postcomposition preserves the isomorphism type of a homomorphism's range. -/
noncomputable def rangeCompEquiv {K : Type*} [Group K] (f : G →* H) (g : H →* K)
    (hg : Function.Injective g) : f.range ≃* (g.comp f).range :=
  (f.range.equivMapOfInjective g hg).trans
    (MulEquiv.subgroupCongr (MonoidHom.map_range g f))

end CenterWeight
end Kourovka
