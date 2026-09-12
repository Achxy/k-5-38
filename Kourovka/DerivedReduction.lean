/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Components

namespace Kourovka

variable {G A B : Type*} [Group G] [Group A] [Group B]

/-- Surjectivity on the derived subgroup and on abelianization implies surjectivity. -/
theorem surjective_of_derived_and_abelianization (f : G →* G)
    (hder : ∀ y ∈ commutator G, ∃ x ∈ commutator G, f x = y)
    (hab : Function.Surjective (Abelianization.map f)) : Function.Surjective f := by
  intro y
  obtain ⟨z, hz⟩ := hab (Abelianization.of y)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  change Abelianization.of (f x) = Abelianization.of y at hz
  have hmem : y * (f x)⁻¹ ∈ commutator G := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hz, mul_inv_cancel]
  obtain ⟨w, _, hw⟩ := hder _ hmem
  exact ⟨w * x, by simp [hw]⟩

/-- A correction through the center leaves surjectivity on the derived subgroup intact. -/
theorem centralCorrection_surjective (u : G →* G) (h : G →* Subgroup.center G)
    (hder : ∀ y ∈ commutator G, ∃ x ∈ commutator G, u x = y)
    (hab : Function.Surjective (Abelianization.map (centralCorrection u h))) :
    Function.Surjective (centralCorrection u h) := by
  apply surjective_of_derived_and_abelianization _ _ hab
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hder y hy
  exact ⟨x, hx, (centralCorrection_eq_on_commutator u h hx).trans hxy⟩

/-- Once a correction is surjective, Hopficity makes the original map injective on the derived group. -/
theorem centralCorrection_injective_on_derived (hG : IsHopfian G)
    (u : G →* G) (h : G →* Subgroup.center G)
    (hsurj : Function.Surjective (centralCorrection u h)) :
    Set.InjOn u (commutator G) := by
  intro x hx y hy heq
  apply hG (centralCorrection u h) hsurj
  simpa only [centralCorrection_eq_on_commutator u h hx,
    centralCorrection_eq_on_commutator u h hy] using heq

/-- The kernel of a surjective product endomorphism lies in the product of derived subgroups. -/
theorem product_kernel_le_derived [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f) :
    f.ker ≤ (commutator A).prod (commutator B) := by
  have h := ker_le_commutator_of_surjective f hf
  have heq : commutator (A × B) = (commutator A).prod (commutator B) := by
    simpa only [commutator_def, Subgroup.top_prod_top] using
      Subgroup.commutator_prod_prod (⊤ : Subgroup A) ⊤ (⊤ : Subgroup B) ⊤
  exact h.trans_eq heq

/-- Central off-diagonal entries vanish on the derived factors, where the diagonal entries suffice. -/
theorem injective_of_central_offDiagonal [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B)
    (h11 : Set.InjOn (fun a => (f (a, 1)).1) (commutator A))
    (h22 : Set.InjOn (fun b => (f (1, b)).2) (commutator B)) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨a, b⟩ := x
  have hd := product_kernel_le_derived f hf hx
  have hA : a ∈ commutator A := hd.1
  have hB : b ∈ commutator B := hd.2
  let f12 : B →* A := (MonoidHom.fst A B).comp (ProductHom.right f)
  let f21 : A →* B := (MonoidHom.snd A B).comp (ProductHom.left f)
  have hv12 : (f (1, b)).1 = 1 := central_map_kills_commutator f12 h12 hB
  have hv21 : (f (a, 1)).2 = 1 := central_map_kills_commutator f21 h21 hA
  have hdecomp := ProductHom.decompose f a b
  have hx' : f (a, b) = 1 := hx
  have hleft : (f (a, 1)).1 = 1 := by
    have := congrArg Prod.fst hdecomp
    simp only [hx', Prod.fst_one, Prod.fst_mul, ProductHom.left_apply,
      ProductHom.right_apply, hv12, mul_one] at this
    exact this.symm
  have hright : (f (1, b)).2 = 1 := by
    have := congrArg Prod.snd hdecomp
    simp only [hx', Prod.snd_one, Prod.snd_mul, ProductHom.left_apply,
      ProductHom.right_apply, hv21, one_mul] at this
    exact this.symm
  have ha : a = 1 := h11 hA (commutator A).one_mem (by
    change (f (a, 1)).1 = (f (1 : A × B)).1
    simpa only [map_one, Prod.fst_one] using hleft)
  have hb : b = 1 := h22 hB (commutator B).one_mem (by
    change (f (1, b)).2 = (f (1 : A × B)).2
    simpa only [map_one, Prod.snd_one] using hright)
  exact Prod.ext ha hb

end Kourovka
