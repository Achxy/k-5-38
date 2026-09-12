/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.MixedPaths
import Kourovka.CenterQuotients

namespace Kourovka

variable {A B : Type*} [Group A] [Group B]

/-- An off-diagonal image killed modulo the product center must itself be central. -/
theorem first_offDiagonal_central_of_killed [Group.FG A] [Group.FG B] [IsSolvable A]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (hk : ∀ b : B, f ((f (1, b)).1, 1) ∈ Subgroup.center (A × B)) :
    ∀ b : B, (f (1, b)).1 ∈ Subgroup.center A := by
  let row : A × B →* A := (MonoidHom.fst A B).comp f
  let P := (ProductHom.left row).range
  let Q := (ProductHom.right row).range
  have hrow : Function.Surjective row := Prod.fst_surjective.comp hf
  have hc : ∀ p : P, ∀ q : Q, Commute (p : A) (q : A) := by
    rintro ⟨p, a, rfl⟩ ⟨q, b, rfl⟩
    exact ProductHom.commute row a b
  have hcover : ∀ a : A, ∃ p : P, ∃ q : Q, (p : A) * q = a := by
    intro a
    obtain ⟨x, y, hxy⟩ := ProductHom.row_surjective row hrow a
    exact ⟨(ProductHom.left row).rangeRestrict x, (ProductHom.right row).rangeRestrict y, hxy⟩
  let E := CentralProducts.quotientEquiv P Q hc hcover
  let U := P ⧸ Subgroup.center P
  let T := Q ⧸ Subgroup.center Q
  let V := B ⧸ Subgroup.center B
  let D : (U × T) × V ≃* (A × B) ⧸ Subgroup.center (A × B) :=
    (E.prodCongr (MulEquiv.refl V)).trans CenterQuotients.productEquiv
  let i : T →* (A × B) ⧸ Subgroup.center (A × B) :=
    D.toMonoidHom.comp ((MonoidHom.inl (U × T) V).comp (MonoidHom.inr U T))
  let r : (A × B) ⧸ Subgroup.center (A × B) →* T :=
    (MonoidHom.snd U T).comp ((MonoidHom.fst (U × T) V).comp D.symm.toMonoidHom)
  have hri : ∀ t, r (i t) = t := by
    intro t
    change (D.symm (D ((1, t), 1))).1.2 = t
    rw [D.symm_apply_apply]
  have hi (q : Q) : i (QuotientGroup.mk q) = QuotientGroup.mk ((q : A), (1 : B)) := by
    change CenterQuotients.productEquiv (A := A) (B := B) (E (1, QuotientGroup.mk q), 1) = _
    have he : E (1, QuotientGroup.mk q) = QuotientGroup.mk (q : A) := by
      change CentralProducts.quotientMultiply P Q hc hcover (1, QuotientGroup.mk q) = _
      change CentralProducts.leftQuotient P Q hc hcover 1 *
        CentralProducts.rightQuotient P Q hc hcover (QuotientGroup.mk q) = _
      rw [map_one, one_mul]
      rfl
    rw [he]
    simpa only [map_one] using CenterQuotients.productEquiv_mk (q : A) (1 : B)
  have hkill : ∀ t, CenterQuotients.quotientMap f hf (i t) = 1 := by
    intro t
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective t
    rw [hi]
    change QuotientGroup.mk (f ((q : A), (1 : B))) = (1 : (A × B) ⧸ Subgroup.center (A × B))
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨b, hb⟩ := q.property
    change (f (1, b)).1 = (q : A) at hb
    rw [← hb]
    exact hk b
  have ht := CenterQuotients.retract_trivial_of_killed
    (CenterQuotients.quotientMap f hf) (CenterQuotients.quotientMap_surjective f hf) i r hri hkill
  intro b
  let q : Q := (ProductHom.right row).rangeRestrict b
  have hq : q ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff q).mp (ht (QuotientGroup.mk q))
  exact CentralProducts.right_center P Q hc hcover hq

/-- The symmetric off-diagonal image satisfies the same conclusion. -/
theorem second_offDiagonal_central_of_killed [Group.FG A] [Group.FG B] [IsSolvable B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (hk : ∀ a : A, f (1, (f (a, 1)).2) ∈ Subgroup.center (A × B)) :
    ∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B := by
  let e : A × B ≃* B × A := MulEquiv.prodComm
  let g : B × A →* B × A := e.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have hg : Function.Surjective g := e.surjective.comp (hf.comp e.symm.surjective)
  have hkg : ∀ a : A, g ((g (1, a)).1, 1) ∈ Subgroup.center (B × A) := by
    intro a
    exact (Subgroup.centerCongr e ⟨f (1, (f (a, 1)).2), hk a⟩).property
  exact first_offDiagonal_central_of_killed g hg hkg

/-- A surjective endomorphism of a product of finitely generated soluble groups has
    a positive iterate whose off-diagonal components are central. -/
theorem exists_central_offDiagonal_iterate [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧
      (∀ b : B, (ProductPaths.iterateHom f m (1, b)).1 ∈ Subgroup.center A) ∧
      (∀ a : A, (ProductPaths.iterateHom f m (a, 1)).2 ∈ Subgroup.center B) := by
  obtain ⟨m, hm, hmix⟩ := ProductPaths.mixed_iterate_central f hf
  let F := ProductPaths.iterateHom f m
  have hF : Function.Surjective F := ProductPaths.iterateHom_surjective f hf m
  have hk1 : ∀ b : B, F ((F (1, b)).1, 1) ∈ Subgroup.center (A × B) := by
    intro b
    exact hmix false true (by decide) (1, b)
  have hk2 : ∀ a : A, F (1, (F (a, 1)).2) ∈ Subgroup.center (A × B) := by
    intro a
    exact hmix true false (by decide) (a, 1)
  exact ⟨m, hm, first_offDiagonal_central_of_killed F hF hk1,
    second_offDiagonal_central_of_killed F hF hk2⟩

end Kourovka
