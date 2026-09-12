/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.CentralLattice
import Kourovka.CentralPeriod
import Kourovka.PathExpansion

namespace Kourovka

variable {G A B : Type*} [Group G] [Group A] [Group B]

def diagonalLeft (f : A × B →* A × B) : A →* A :=
  (MonoidHom.fst A B).comp (ProductHom.left f)

def diagonalRight (f : A × B →* A × B) : B →* B :=
  (MonoidHom.snd A B).comp (ProductHom.right f)

theorem abelianMap_iterate_of (f : G →* G) (n : ℕ) (x : G) :
    (CentralLattice.abelianMap f)^[n] (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (f^[n] x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

/-- One common positive power satisfies independently chosen congruences on both diagonal maps. -/
theorem exists_diagonal_congruence_iterate [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (dA dB : ℤ) (hdA : dA ≠ 0) (hdB : dB ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      (∀ x : Additive (Abelianization A), ∃ y,
        CentralLattice.abelianMap (diagonalLeft (ProductPaths.iterateHom f n)) x - x = dA • y) ∧
      (∀ x : Additive (Abelianization B), ∃ y,
        CentralLattice.abelianMap (diagonalRight (ProductPaths.iterateHom f n)) x - x = dB • y) := by
  let M := Additive (Abelianization (A × B))
  have hfab : Function.Surjective (CentralLattice.abelianMap f) := abelianization_map_surjective f hf
  obtain ⟨n, hn, hcong⟩ := CentralPeriod.exists_iterate_congr M
    (CentralLattice.abelianMap f) hfab (dA * dB) (mul_ne_zero hdA hdB)
  refine ⟨n, hn, ?_, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    let p : M →ₗ[ℤ] Additive (Abelianization A) :=
      (Abelianization.map (MonoidHom.fst A B)).toAdditive.toIntLinearMap
    obtain ⟨y, hy⟩ := hcong (Additive.ofMul (Abelianization.of (a, (1 : B))))
    have hp := congrArg p hy
    rw [map_sub, map_smul, abelianMap_iterate_of] at hp
    change CentralLattice.abelianMap (diagonalLeft (ProductPaths.iterateHom f n))
      (Additive.ofMul (Abelianization.of a)) - Additive.ofMul (Abelianization.of a) =
        (dA * dB) • p y at hp
    refine ⟨dB • p y, ?_⟩
    rw [← mul_smul]
    exact hp
  · intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    let p : M →ₗ[ℤ] Additive (Abelianization B) :=
      (Abelianization.map (MonoidHom.snd A B)).toAdditive.toIntLinearMap
    obtain ⟨y, hy⟩ := hcong (Additive.ofMul (Abelianization.of ((1 : A), b)))
    have hp := congrArg p hy
    rw [map_sub, map_smul, abelianMap_iterate_of] at hp
    change CentralLattice.abelianMap (diagonalRight (ProductPaths.iterateHom f n))
      (Additive.ofMul (Abelianization.of b)) - Additive.ofMul (Abelianization.of b) =
        (dA * dB) • p y at hp
    refine ⟨dA • p y, ?_⟩
    rw [← mul_smul, mul_comm dB dA]
    exact hp

end Kourovka
