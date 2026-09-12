/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.PathExpansion
import Kourovka.DerivedReduction

namespace Kourovka.CentralProductPowers

open ProductPaths

variable {A B : Type*} [Group A] [Group B]

/-- Central off-diagonal entries remain central under every iterate. -/
theorem iterate_central_offDiagonal (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) (n : ℕ) :
    (∀ b, (iterateHom f n (1, b)).1 ∈ Subgroup.center A) ∧
    (∀ a, (iterateHom f n (a, 1)).2 ∈ Subgroup.center B) := by
  have hA : ∀ {a : A}, a ∈ Subgroup.center A →
      (f (a, 1)).1 ∈ Subgroup.center A := fun ha =>
    ProductHom.left_center ((MonoidHom.fst A B).comp f) (Prod.fst_surjective.comp hf) ha
  have hB : ∀ {b : B}, b ∈ Subgroup.center B →
      (f (1, b)).2 ∈ Subgroup.center B := fun hb =>
    ProductHom.right_center ((MonoidHom.snd A B).comp f) (Prod.snd_surjective.comp hf) hb
  induction n with
  | zero => exact ⟨fun _ => (Subgroup.center A).one_mem,
      fun _ => (Subgroup.center B).one_mem⟩
  | succ n ih =>
      constructor
      · intro b
        change (f^[n + 1] (1, b)).1 ∈ Subgroup.center A
        rw [Function.iterate_succ_apply']
        have he := congrArg Prod.fst (ProductHom.decompose f
          (f^[n] (1, b)).1 (f^[n] (1, b)).2)
        rw [he]
        exact (Subgroup.center A).mul_mem (hA (ih.1 b)) (h12 _)
      · intro a
        change (f^[n + 1] (a, 1)).2 ∈ Subgroup.center B
        rw [Function.iterate_succ_apply']
        have he := congrArg Prod.snd (ProductHom.decompose f
          (f^[n] (a, 1)).1 (f^[n] (a, 1)).2)
        rw [he]
        exact (Subgroup.center B).mul_mem (h21 _) (hB (ih.2 a))

/-- A surjective product map with central off-diagonal entries maps each derived
factor onto itself through its diagonal entry. -/
theorem diagonal_surjective_on_derived (f : A × B →* A × B)
    (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) :
    (∀ y ∈ commutator A, ∃ x ∈ commutator A, (f (x, 1)).1 = y) ∧
    (∀ y ∈ commutator B, ∃ x ∈ commutator B, (f (1, x)).2 = y) := by
  have heq : commutator (A × B) = (commutator A).prod (commutator B) := by
    simpa only [commutator_def, Subgroup.top_prod_top] using
      Subgroup.commutator_prod_prod (⊤ : Subgroup A) ⊤ (⊤ : Subgroup B) ⊤
  have hsurj : ∀ y ∈ commutator (A × B),
      ∃ x ∈ commutator (A × B), f x = y := by
    intro y hy
    have hmap := (derivedSeries_le_map_derivedSeries hf 1) hy
    exact hmap
  constructor
  · intro y hy
    obtain ⟨⟨x, z⟩, hxz, he⟩ := hsurj (y, 1) (by
      rw [heq]
      exact ⟨hy, (commutator B).one_mem⟩)
    rw [heq] at hxz
    have hz : (f (1, z)).1 = 1 := central_map_kills_commutator
      ((MonoidHom.fst A B).comp (ProductHom.right f)) h12 hxz.2
    refine ⟨x, hxz.1, ?_⟩
    have h := congrArg Prod.fst (ProductHom.decompose f x z)
    simp only [he, Prod.fst_mul, ProductHom.left_apply, ProductHom.right_apply, hz, mul_one] at h
    exact h.symm
  · intro y hy
    obtain ⟨⟨x, z⟩, hxz, he⟩ := hsurj (1, y) (by
      rw [heq]
      exact ⟨(commutator A).one_mem, hy⟩)
    rw [heq] at hxz
    have hx : (f (x, 1)).2 = 1 := central_map_kills_commutator
      ((MonoidHom.snd A B).comp (ProductHom.left f)) h21 hxz.1
    refine ⟨z, hxz.2, ?_⟩
    have h := congrArg Prod.snd (ProductHom.decompose f x z)
    simp only [he, Prod.snd_mul, ProductHom.left_apply, ProductHom.right_apply, hx, one_mul] at h
    exact h.symm

end Kourovka.CentralProductPowers
