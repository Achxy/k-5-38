/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.AbelianWeight
import Kourovka.FinitePaths

namespace Kourovka.CentralPeriod

variable (M : Type*) [AddCommGroup M]

/-- The subgroup of multiples of a fixed integer. -/
def multiples (d : ℤ) : Submodule ℤ M :=
  LinearMap.range (d • (LinearMap.id : M →ₗ[ℤ] M))

theorem multiples_quotient_finite [Module.Finite ℤ M] (d : ℤ) (hd : d ≠ 0) :
    Finite (M ⧸ multiples M d) := by
  apply Module.finite_of_fg_torsion
  intro x
  obtain ⟨x, rfl⟩ := (multiples M d).mkQ_surjective x
  refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
  change d • (multiples M d).mkQ x = 0
  rw [← map_smul]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨x, rfl⟩

def quotientMap (f : M →ₗ[ℤ] M) (d : ℤ) :
    M ⧸ multiples M d →ₗ[ℤ] M ⧸ multiples M d :=
  (multiples M d).mapQ (multiples M d) f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (f.map_smul d y).symm⟩)

theorem quotientMap_surjective (f : M →ₗ[ℤ] M) (hf : Function.Surjective f) (d : ℤ) :
    Function.Surjective (quotientMap M f d) := by
  intro y
  obtain ⟨y, rfl⟩ := (multiples M d).mkQ_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨(multiples M d).mkQ x, rfl⟩

theorem quotientMap_iterate (f : M →ₗ[ℤ] M) (d : ℤ) (n : ℕ) (x : M) :
    (quotientMap M f d)^[n] ((multiples M d).mkQ x) = (multiples M d).mkQ (f^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

/-- A surjection of a finite type has a positive iterate equal to the identity. -/
theorem exists_identity_iterate {X : Type*} [Finite X] (f : X → X)
    (hf : Function.Surjective f) : ∃ n : ℕ, 0 < n ∧ f^[n] = id := by
  have hi : Function.Injective f := Finite.injective_iff_surjective.mpr hf
  obtain ⟨n, hn, he⟩ := FinitePaths.exists_idempotent_iterate f
  refine ⟨n, hn, funext fun x => ?_⟩
  apply hi.iterate n
  have h := congrFun he x
  simpa only [two_mul, Function.iterate_add_apply, id_eq] using h

/-- A positive power of a surjective endomorphism is the identity modulo every nonzero modulus. -/
theorem exists_iterate_congr [Module.Finite ℤ M] (f : M →ₗ[ℤ] M)
    (hf : Function.Surjective f) (d : ℤ) (hd : d ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : M, ∃ y : M, f^[n] x - x = d • y := by
  letI := multiples_quotient_finite M d hd
  obtain ⟨n, hn, he⟩ := exists_identity_iterate (quotientMap M f d)
    (quotientMap_surjective M f hf d)
  refine ⟨n, hn, ?_⟩
  intro x
  have hq := congrFun he ((multiples M d).mkQ x)
  rw [quotientMap_iterate] at hq
  have hz : (multiples M d).mkQ (f^[n] x - x) = 0 := by
    rw [map_sub, hq]
    exact sub_self _
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  exact ⟨y, hy.symm⟩

end Kourovka.CentralPeriod
