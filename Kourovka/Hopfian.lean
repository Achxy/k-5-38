/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fintype.Card

namespace Kourovka

/-- Every surjective endomorphism is injective. -/
def IsHopfian (G : Type*) [Group G] : Prop :=
  ∀ f : G →* G, Function.Surjective f → Function.Injective f

variable {G H : Type*} [Group G] [Group H]

theorem IsHopfian.of_mulEquiv (hG : IsHopfian G) (e : G ≃* H) : IsHopfian H := by
  intro f hf
  let g := e.symm.toMonoidHom.comp (f.comp e.toMonoidHom)
  have hg : Function.Surjective g :=
    e.symm.surjective.comp (hf.comp e.surjective)
  have hi := hG g hg
  intro x y hxy
  apply e.symm.injective
  apply hi
  simpa [g] using congrArg e.symm hxy

theorem isHopfian_of_finite [Finite G] : IsHopfian G := by
  intro f hf
  exact Finite.injective_iff_surjective.mpr hf

theorem isHopfian_of_commGroup (A : Type*) [CommGroup A] [Group.FG A] :
    IsHopfian A := by
  intro f hf
  letI : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  exact IsNoetherian.injective_of_surjective_endomorphism f.toAdditive.toIntLinearMap hf

theorem abelianization_map_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (Abelianization.map f) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Abelianization.of x, rfl⟩

theorem ker_le_commutator_of_surjective [Group.FG G] (f : G →* G)
    (hf : Function.Surjective f) : f.ker ≤ commutator G := by
  letI : Group.FG (Abelianization G) :=
    Group.fg_of_surjective (f := Abelianization.of) QuotientGroup.mk_surjective
  have hi := isHopfian_of_commGroup (Abelianization G)
    (Abelianization.map f) (abelianization_map_surjective f hf)
  intro x hx
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  apply hi
  simpa using congrArg (Abelianization.of : G → Abelianization G) hx

/-- A soluble perfect group is trivial. -/
theorem subsingleton_of_solvable_perfect [IsSolvable G]
    (h : commutator G = ⊤) : Subsingleton G := by
  by_contra hn
  letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hn
  exact (ne_of_lt (IsSolvable.commutator_lt_top_of_nontrivial G)) h

end Kourovka
