/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.CenterWeight

namespace Kourovka
namespace CenterQuotients

variable {A B G H T : Type*} [Group A] [Group B] [Group G] [Group H] [Group T]

theorem center_product_iff (a : A) (b : B) :
    (a, b) ∈ Subgroup.center (A × B) ↔ a ∈ Subgroup.center A ∧ b ∈ Subgroup.center B := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h
    exact ⟨fun x => congrArg Prod.fst (h (x, 1)),
      fun y => congrArg Prod.snd (h (1, y))⟩
  · rintro ⟨ha, hb⟩ ⟨x, y⟩
    exact Prod.ext (ha x) (hb y)

/-- A surjective homomorphism sends the center into the center. -/
theorem map_center (f : G →* H) (hf : Function.Surjective f)
    {z : G} (hz : z ∈ Subgroup.center G) : f z ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]

def quotientMap (f : G →* H) (hf : Function.Surjective f) :
    G ⧸ Subgroup.center G →* H ⧸ Subgroup.center H :=
  QuotientGroup.map _ _ f (fun _ hz => map_center f hf hz)

theorem quotientMap_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (quotientMap f hf) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨QuotientGroup.mk x, rfl⟩

def quotientInl : A ⧸ Subgroup.center A →* (A × B) ⧸ Subgroup.center (A × B) :=
  QuotientGroup.map _ _ (MonoidHom.inl A B)
    (fun _ ha => (center_product_iff _ _).mpr ⟨ha, (Subgroup.center B).one_mem⟩)

def quotientInr : B ⧸ Subgroup.center B →* (A × B) ⧸ Subgroup.center (A × B) :=
  QuotientGroup.map _ _ (MonoidHom.inr A B)
    (fun _ hb => (center_product_iff _ _).mpr ⟨(Subgroup.center A).one_mem, hb⟩)

theorem quotientInl_commute_quotientInr (a : A ⧸ Subgroup.center A)
    (b : B ⧸ Subgroup.center B) : Commute (quotientInl a) (quotientInr b) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply Commute.map _ (QuotientGroup.mk' (Subgroup.center (A × B)))
  change (a, (1 : B)) * ((1 : A), b) = (1, b) * (a, 1)
  simp

def quotientProduct : (A ⧸ Subgroup.center A) × (B ⧸ Subgroup.center B) →*
    (A × B) ⧸ Subgroup.center (A × B) :=
  quotientInl.noncommCoprod quotientInr quotientInl_commute_quotientInr

@[simp] theorem quotientProduct_mk (a : A) (b : B) :
    quotientProduct (QuotientGroup.mk a, QuotientGroup.mk b) = QuotientGroup.mk (a, b) := by
  change (QuotientGroup.mk' (Subgroup.center (A × B))) (a, 1) *
    (QuotientGroup.mk' (Subgroup.center (A × B))) (1, b) = _
  rw [← map_mul]
  simp

theorem quotientProduct_bijective : Function.Bijective (quotientProduct (A := A) (B := B)) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    rintro ⟨a, b⟩ hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    change quotientProduct (QuotientGroup.mk a, QuotientGroup.mk b) = 1 at hab
    rw [quotientProduct_mk] at hab
    obtain ⟨ha, hb⟩ := (center_product_iff a b).mp ((QuotientGroup.eq_one_iff _).mp hab)
    exact Prod.ext ((QuotientGroup.eq_one_iff _).mpr ha) ((QuotientGroup.eq_one_iff _).mpr hb)
  · intro z
    obtain ⟨⟨a, b⟩, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨(QuotientGroup.mk a, QuotientGroup.mk b), quotientProduct_mk a b⟩

/-- The quotient by the product center is the product of the center quotients. -/
noncomputable def productEquiv :
    (A ⧸ Subgroup.center A) × (B ⧸ Subgroup.center B) ≃*
      (A × B) ⧸ Subgroup.center (A × B) :=
  MulEquiv.ofBijective quotientProduct quotientProduct_bijective

@[simp] theorem productEquiv_mk (a : A) (b : B) :
    productEquiv (QuotientGroup.mk a, QuotientGroup.mk b) = QuotientGroup.mk (a, b) :=
  quotientProduct_mk a b

/-- A soluble retract killed by a surjective endomorphism of a finitely generated group is trivial. -/
theorem retract_trivial_of_killed [Group.FG G] [IsSolvable T]
    (f : G →* G) (hf : Function.Surjective f) (i : T →* G) (r : G →* T)
    (hri : ∀ t, r (i t) = t) (hkill : ∀ t, f (i t) = 1) : ∀ t : T, t = 1 := by
  have hr : Function.Surjective r := fun t => ⟨i t, hri t⟩
  have hmap : (commutator G).map r = commutator T := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hr, commutator_def]
  have ht : commutator T = ⊤ := by
    apply top_unique
    intro t _
    rw [← hmap]
    exact ⟨i t, ker_le_commutator_of_surjective f hf (hkill t), hri t⟩
  letI : Subsingleton T := subsingleton_of_solvable_perfect ht
  exact fun t => Subsingleton.elim t 1

end CenterQuotients
end Kourovka
