/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Hopfian
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.Linarith

namespace Kourovka
namespace AbelianWeight

variable (M N : Type*) [AddCommGroup M] [AddCommGroup N]

instance torsionFinite [Module.Finite ℤ M] : Finite (Submodule.torsion ℤ M) :=
  Module.finite_of_fg_torsion _ (Submodule.torsion_isTorsion (R := ℤ) (M := M))

/-- A finite natural-number measure detecting every nonzero finitely generated abelian group. -/
noncomputable def weight : ℕ :=
  Module.finrank ℤ M + Nat.card (Submodule.torsion ℤ M) - 1

/-- Torsion in a product is the product of the torsion subgroups. -/
def torsionProdEquiv : Submodule.torsion ℤ (M × N) ≃
    (Submodule.torsion ℤ M) × (Submodule.torsion ℤ N) where
  toFun x :=
    (⟨x.val.1, by
      obtain ⟨r, hr⟩ := x.property
      exact ⟨r, congrArg Prod.fst hr⟩⟩,
     ⟨x.val.2, by
      obtain ⟨r, hr⟩ := x.property
      exact ⟨r, congrArg Prod.snd hr⟩⟩)
  invFun x := ⟨(x.1.val, x.2.val), by
    obtain ⟨r, hr⟩ := x.1.property
    obtain ⟨s, hs⟩ := x.2.property
    refine ⟨r * s, ?_⟩
    apply Prod.ext
    · change (r * s) • x.1.val = 0
      rw [mul_comm r s, mul_smul, hr, smul_zero]
    · change (r * s) • x.2.val = 0
      rw [mul_smul, hs, smul_zero]⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- Group isomorphisms restrict to the torsion subgroups. -/
def torsionCongr (e : M ≃+ N) : Submodule.torsion ℤ M ≃ Submodule.torsion ℤ N where
  toFun x := ⟨e x, by
    obtain ⟨r, hr⟩ := x.property
    refine ⟨r, ?_⟩
    change (r : ℤ) • (x : M) = 0 at hr
    change (r : ℤ) • e x = 0
    rw [← map_zsmul, hr, map_zero]⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨r, hr⟩ := y.property
    refine ⟨r, ?_⟩
    change (r : ℤ) • (y : N) = 0 at hr
    change (r : ℤ) • e.symm y = 0
    rw [← map_zsmul, hr, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)

theorem weight_congr (e : M ≃+ N) : weight M = weight N := by
  unfold weight
  rw [e.toIntLinearEquiv.finrank_eq, Nat.card_congr (torsionCongr M N e)]

theorem finrank_add_le [Module.Finite ℤ M] [Module.Finite ℤ N] :
    Module.finrank ℤ M + Module.finrank ℤ N ≤ Module.finrank ℤ (M × N) := by
  have h := lift_rank_add_lift_rank_le_rank_prod ℤ M N
  rw [← Module.finrank_eq_rank ℤ M, ← Module.finrank_eq_rank ℤ N,
    ← Module.finrank_eq_rank ℤ (M × N)] at h
  simpa only [Cardinal.lift_natCast, ← Nat.cast_add, Nat.cast_le] using h

/-- The measure is superadditive under direct products. -/
theorem weight_add_le [Module.Finite ℤ M] [Module.Finite ℤ N] :
    weight M + weight N ≤ weight (M × N) := by
  have hM : 0 < Nat.card (Submodule.torsion ℤ M) := Nat.card_pos
  have hN : 0 < Nat.card (Submodule.torsion ℤ N) := Nat.card_pos
  have hr := finrank_add_le M N
  have hc : Nat.card (Submodule.torsion ℤ (M × N)) =
      Nat.card (Submodule.torsion ℤ M) * Nat.card (Submodule.torsion ℤ N) := by
    rw [Nat.card_congr (torsionProdEquiv M N), Nat.card_prod]
  unfold weight
  rw [hc]
  have hp : Nat.card (Submodule.torsion ℤ M) + Nat.card (Submodule.torsion ℤ N) ≤
      Nat.card (Submodule.torsion ℤ M) * Nat.card (Submodule.torsion ℤ N) + 1 := by
    nlinarith [Nat.zero_le ((Nat.card (Submodule.torsion ℤ M) - 1) *
      (Nat.card (Submodule.torsion ℤ N) - 1))]
  omega

/-- Every nontrivial finitely generated abelian group has positive measure. -/
theorem weight_pos [Module.Finite ℤ M] [Nontrivial M] : 0 < weight M := by
  have hc : 0 < Nat.card (Submodule.torsion ℤ M) := Nat.card_pos
  by_cases hr : Module.finrank ℤ M = 0
  · have ht : Module.IsTorsion ℤ M := (Module.finrank_eq_zero_iff_isTorsion (R := ℤ) (M := M)).mp hr
    have hs : Function.Surjective ((Submodule.torsion ℤ M).subtype) := by
      intro x
      exact ⟨⟨x, @ht x⟩, rfl⟩
    letI : Nontrivial (Submodule.torsion ℤ M) := hs.nontrivial
    have hcard : 1 < Nat.card (Submodule.torsion ℤ M) := Finite.one_lt_card
    unfold weight
    omega
  · unfold weight
    omega

end AbelianWeight
end Kourovka
