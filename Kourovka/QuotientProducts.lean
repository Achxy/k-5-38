/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.EventualCentrality

namespace Kourovka
variable {A B : Type*} [Group A] [Group B]

/-- Central off-diagonal images give a product of epimorphisms on the center quotients. -/
theorem quotient_product_of_central_offDiagonal (f : A × B →* A × B)
    (hf : Function.Surjective f)
    (h12 : ∀ b : B, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B) :
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap f hf (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by
  let E := CenterQuotients.productEquiv (A := A) (B := B)
  let H := E.symm.toMonoidHom.comp ((CenterQuotients.quotientMap f hf).comp E.toMonoidHom)
  have hH : Function.Surjective H :=
    E.symm.surjective.comp ((CenterQuotients.quotientMap_surjective f hf).comp E.surjective)
  have hrep (a : A) (b : B) :
      H (QuotientGroup.mk a, QuotientGroup.mk b) =
        (QuotientGroup.mk (f (a, b)).1, QuotientGroup.mk (f (a, b)).2) := by
    apply E.injective
    change E (E.symm (CenterQuotients.quotientMap f hf
      (E (QuotientGroup.mk a, QuotientGroup.mk b)))) = _
    rw [E.apply_symm_apply]
    change CenterQuotients.quotientMap f hf
      (CenterQuotients.productEquiv (QuotientGroup.mk a, QuotientGroup.mk b)) =
      CenterQuotients.productEquiv (QuotientGroup.mk (f (a, b)).1, QuotientGroup.mk (f (a, b)).2)
    rw [CenterQuotients.productEquiv_mk, CenterQuotients.productEquiv_mk]
    rfl
  let u := (MonoidHom.fst (A ⧸ Subgroup.center A) (B ⧸ Subgroup.center B)).comp
    (H.comp (MonoidHom.inl (A ⧸ Subgroup.center A) (B ⧸ Subgroup.center B)))
  let v := (MonoidHom.snd (A ⧸ Subgroup.center A) (B ⧸ Subgroup.center B)).comp
    (H.comp (MonoidHom.inr (A ⧸ Subgroup.center A) (B ⧸ Subgroup.center B)))
  have hleft (x : A ⧸ Subgroup.center A) : H (x, 1) = (u x, 1) := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    apply Prod.ext
    · rfl
    · have he := congrArg Prod.snd (hrep a 1)
      simpa only [QuotientGroup.mk_one, (QuotientGroup.eq_one_iff _).mpr (h21 a)] using he
  have hright (y : B ⧸ Subgroup.center B) : H (1, y) = (1, v y) := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    apply Prod.ext
    · have he := congrArg Prod.fst (hrep 1 b)
      simpa only [QuotientGroup.mk_one, (QuotientGroup.eq_one_iff _).mpr (h12 b)] using he
    · rfl
  have hprod (x : A ⧸ Subgroup.center A) (y : B ⧸ Subgroup.center B) :
      H (x, y) = (u x, v y) := by
    calc
      H (x, y) = H ((x, 1) * (1, y)) := by simp
      _ = H (x, 1) * H (1, y) := H.map_mul _ _
      _ = (u x, v y) := by rw [hleft, hright]; simp
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a, b⟩, he⟩ := hH (x, 1)
    exact ⟨a, congrArg Prod.fst ((hprod a b).symm.trans he)⟩
  · intro y
    obtain ⟨⟨a, b⟩, he⟩ := hH (1, y)
    exact ⟨b, congrArg Prod.snd ((hprod a b).symm.trans he)⟩
  · intro x y
    have he := congrArg E (hprod x y)
    change E (E.symm (CenterQuotients.quotientMap f hf (E (x, y)))) = E (u x, v y) at he
    simpa only [E.apply_symm_apply] using he

/-- On the center quotient, preservation of the two factors is equivalent to central mixing. -/
theorem central_offDiagonal_iff_quotient_product (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ((∀ b : B, (f (1, b)).1 ∈ Subgroup.center A) ∧
      (∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B)) ↔
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap f hf (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by
  constructor
  · rintro ⟨h12, h21⟩
    exact quotient_product_of_central_offDiagonal f hf h12 h21
  · rintro ⟨u, v, _, _, h⟩
    let E := CenterQuotients.productEquiv (A := A) (B := B)
    have hmk (a : A) (b : B) : E.symm (QuotientGroup.mk (a, b)) =
        (QuotientGroup.mk a, QuotientGroup.mk b) := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact (CenterQuotients.productEquiv_mk a b).symm
    constructor
    · intro b
      have he := h (QuotientGroup.mk (1 : A)) (QuotientGroup.mk b)
      rw [CenterQuotients.productEquiv_mk] at he
      change QuotientGroup.mk (f (1, b)) = E (u (QuotientGroup.mk 1), v (QuotientGroup.mk b)) at he
      have ht := congrArg E.symm he
      rw [hmk, E.symm_apply_apply] at ht
      apply (QuotientGroup.eq_one_iff _).mp
      simpa only [QuotientGroup.mk_one, map_one] using congrArg Prod.fst ht
    · intro a
      have he := h (QuotientGroup.mk a) (QuotientGroup.mk (1 : B))
      rw [CenterQuotients.productEquiv_mk] at he
      change QuotientGroup.mk (f (a, 1)) = E (u (QuotientGroup.mk a), v (QuotientGroup.mk 1)) at he
      have ht := congrArg E.symm he
      rw [hmk, E.symm_apply_apply] at ht
      apply (QuotientGroup.eq_one_iff _).mp
      simpa only [QuotientGroup.mk_one, map_one] using congrArg Prod.snd ht

/-- One factorial power induces a product of epimorphisms on the two center quotients. -/
theorem factorial_quotient_product [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    ∃ (u : A ⧸ Subgroup.center A →* A ⧸ Subgroup.center A)
      (v : B ⧸ Subgroup.center B →* B ⧸ Subgroup.center B),
      Function.Surjective u ∧ Function.Surjective v ∧
      ∀ x y, CenterQuotients.quotientMap (ProductPaths.iterateHom f m)
        (ProductPaths.iterateHom_surjective f hf m) (CenterQuotients.productEquiv (x, y)) =
        CenterQuotients.productEquiv (u x, v y) := by
  obtain ⟨h12, h21⟩ := central_offDiagonal_factorial_iterate f hf
  exact quotient_product_of_central_offDiagonal _ (ProductPaths.iterateHom_surjective f hf _) h12 h21

end Kourovka
