/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags

namespace Kourovka
namespace SolvableWeight

variable (G H : Type*) [Group G] [Group H]

/-- Abelianization preserves the direct product. -/
def abelianizationProd : Abelianization (G × H) ≃*
    Abelianization G × Abelianization H where
  toFun := Abelianization.lift
    ((Abelianization.of.comp (MonoidHom.fst G H)).prod
      (Abelianization.of.comp (MonoidHom.snd G H)))
  invFun := (Abelianization.map (MonoidHom.inl G H)).coprod
    (Abelianization.map (MonoidHom.inr G H))
  left_inv x := by
    obtain ⟨⟨g, h⟩, rfl⟩ := QuotientGroup.mk_surjective x
    change Abelianization.of (g, (1 : H)) * Abelianization.of ((1 : G), h) =
      Abelianization.of (g, h)
    rw [← map_mul]
    simp
  right_inv x := by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.1
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective x.2
    rcases x with ⟨x, y⟩
    dsimp at hg hh
    subst x y
    change Abelianization.lift
      ((Abelianization.of.comp (MonoidHom.fst G H)).prod
        (Abelianization.of.comp (MonoidHom.snd G H)))
      (Abelianization.of (g, (1 : H)) * Abelianization.of ((1 : G), h)) = _
    rw [← map_mul]
    change (Abelianization.of (g * 1), Abelianization.of (1 * h)) = _
    simp only [mul_one, one_mul]
    rfl
  map_mul' x y := map_mul _ x y

instance abelianizationFG [Group.FG G] : Group.FG (Abelianization G) :=
  Group.fg_of_surjective (f := Abelianization.of) QuotientGroup.mk_surjective

instance abelianizationModuleFinite [Group.FG G] :
    Module.Finite ℤ (Additive (Abelianization G)) :=
  Module.Finite.iff_addGroup_fg.mpr inferInstance

/-- A nontrivial soluble group has nontrivial abelianization. -/
theorem abelianization_nontrivial [IsSolvable G] [Nontrivial G] :
    Nontrivial (Abelianization G) := by
  by_contra h
  letI : Subsingleton (Abelianization G) := not_nontrivial_iff_subsingleton.mp h
  have hp : commutator G = ⊤ := by
    rw [← Abelianization.ker_of]
    apply top_unique
    intro g _
    exact Subsingleton.elim _ _
  letI : Subsingleton G := subsingleton_of_solvable_perfect hp
  exact not_subsingleton G inferInstance

/-- A finite measure for the number of nontrivial soluble direct factors. -/
noncomputable def weight : ℕ := AbelianWeight.weight (Additive (Abelianization G))

theorem weight_congr (e : G ≃* H) : weight G = weight H :=
  AbelianWeight.weight_congr _ _ e.abelianizationCongr.toAdditive

theorem weight_pos [Group.FG G] [IsSolvable G] [Nontrivial G] : 0 < weight G := by
  letI := abelianization_nontrivial G
  exact AbelianWeight.weight_pos _

/-- Direct factors consume at least their own positive measure. -/
theorem weight_add_le [Group.FG G] [Group.FG H] :
    weight G + weight H ≤ weight (G × H) := by
  have h := AbelianWeight.weight_add_le (Additive (Abelianization G))
    (Additive (Abelianization H))
  have he := AbelianWeight.weight_congr _ _
    ((abelianizationProd G H).toAdditive.trans
      (AddEquiv.prodAdditive (Abelianization G) (Abelianization H)))
  change _ ≤ AbelianWeight.weight (Additive (Abelianization (G × H)))
  rw [he]
  exact h

end SolvableWeight
end Kourovka
