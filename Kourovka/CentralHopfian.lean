/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.DiagonalCongruence
import Kourovka.CentralProductPowers
import Kourovka.EventualCentrality

namespace Kourovka

variable {A B : Type*} [Group A] [Group B]

theorem diagonalLeft_center (f : A × B →* A × B) (hf : Function.Surjective f)
    {z : A} (hz : z ∈ Subgroup.center A) : diagonalLeft f z ∈ Subgroup.center A :=
  ProductHom.left_center ((MonoidHom.fst A B).comp f) (Prod.fst_surjective.comp hf) hz

theorem diagonalRight_center (f : A × B →* A × B) (hf : Function.Surjective f)
    {z : B} (hz : z ∈ Subgroup.center B) : diagonalRight f z ∈ Subgroup.center B :=
  ProductHom.right_center ((MonoidHom.snd A B).comp f) (Prod.snd_surjective.comp hf) hz

theorem diagonalLeft_mul_center_surjective (f : A × B →* A × B)
    (hf : Function.Surjective f) (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A) :
    ∀ y, ∃ x z, z ∈ Subgroup.center A ∧ diagonalLeft f x * z = y := by
  intro y
  obtain ⟨a, b, hab⟩ := ProductHom.row_surjective ((MonoidHom.fst A B).comp f)
    (Prod.fst_surjective.comp hf) y
  exact ⟨a, (f (1, b)).1, h12 b, hab⟩

theorem diagonalRight_mul_center_surjective (f : A × B →* A × B)
    (hf : Function.Surjective f) (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) :
    ∀ y, ∃ x z, z ∈ Subgroup.center B ∧ diagonalRight f x * z = y := by
  intro y
  let row := (MonoidHom.snd A B).comp f
  obtain ⟨a, b, hab⟩ := ProductHom.row_surjective row (Prod.snd_surjective.comp hf) y
  refine ⟨b, (f (a, 1)).2, h21 a, ?_⟩
  change ProductHom.right row b * ProductHom.left row a = y
  rw [← (ProductHom.commute row a b).eq]
  exact hab

/-- Injectivity of one positive iterate implies injectivity of the original function. -/
theorem injective_of_positive_iterate {X : Type*} (f : X → X) {n : ℕ}
    (hn : 0 < n) (hi : Function.Injective f^[n]) : Function.Injective f := by
  intro x y hxy
  apply hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hxy]

/-- Central mixing cannot destroy Hopficity of finitely generated factors. -/
theorem injective_of_central_offDiagonal_hopfian [Group.FG A] [Group.FG B]
    (hA : IsHopfian A) (hB : IsHopfian B)
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) : Function.Injective f := by
  obtain ⟨dA, hdA, hmodA⟩ := CentralLattice.exists_group_correction_modulus (G := A)
  obtain ⟨dB, hdB, hmodB⟩ := CentralLattice.exists_group_correction_modulus (G := B)
  obtain ⟨n, hn, hcongA, hcongB⟩ := exists_diagonal_congruence_iterate f hf dA dB hdA hdB
  let F := ProductPaths.iterateHom f n
  have hF : Function.Surjective F := ProductPaths.iterateHom_surjective f hf n
  obtain ⟨hF12, hF21⟩ := CentralProductPowers.iterate_central_offDiagonal f hf h12 h21 n
  obtain ⟨hderA, hderB⟩ := CentralProductPowers.diagonal_surjective_on_derived F hF hF12 hF21
  obtain ⟨cA, hcA⟩ := hmodA (diagonalLeft F)
    (fun _ hz => diagonalLeft_center F hF hz)
    (diagonalLeft_mul_center_surjective F hF hF12) hcongA hderA
  obtain ⟨cB, hcB⟩ := hmodB (diagonalRight F)
    (fun _ hz => diagonalRight_center F hF hz)
    (diagonalRight_mul_center_surjective F hF hF21) hcongB hderB
  have hiA := centralCorrection_injective_on_derived hA (diagonalLeft F) cA hcA
  have hiB := centralCorrection_injective_on_derived hB (diagonalRight F) cB hcB
  have hiF := injective_of_central_offDiagonal F hF hF12 hF21 hiA hiB
  exact injective_of_positive_iterate f hn hiF

/-- The direct product of two finitely generated soluble Hopfian groups is Hopfian. -/
theorem directProduct_isHopfian [Group.FG A] [Group.FG B] [IsSolvable A] [IsSolvable B]
    (hA : IsHopfian A) (hB : IsHopfian B) : IsHopfian (A × B) := by
  intro f hf
  obtain ⟨m, hm, h12, h21⟩ := exists_central_offDiagonal_iterate f hf
  have hi := injective_of_central_offDiagonal_hopfian hA hB (ProductPaths.iterateHom f m)
    (ProductPaths.iterateHom_surjective f hf m) h12 h21
  exact injective_of_positive_iterate f hm hi

end Kourovka
