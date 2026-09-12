/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Components
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Kourovka
namespace CentralProducts

variable {G : Type*} [Group G] (P Q : Subgroup G)
    (hc : ∀ p : P, ∀ q : Q, Commute (p : G) (q : G))

/-- Multiplication of commuting subgroups. -/
def multiply : P × Q →* G := P.subtype.noncommCoprod Q.subtype hc

@[simp] theorem multiply_apply (p : P) (q : Q) : multiply P Q hc (p, q) = p * q := rfl

theorem multiply_surjective (hcover : ∀ g : G, ∃ p : P, ∃ q : Q, (p : G) * q = g) :
    Function.Surjective (multiply P Q hc) := by
  intro g
  obtain ⟨p, q, h⟩ := hcover g
  exact ⟨(p, q), h⟩

variable (hcover : ∀ g : G, ∃ p : P, ∃ q : Q, (p : G) * q = g)

include P Q hc hcover in
theorem left_center {p : P} (hp : p ∈ Subgroup.center P) :
    (p : G) ∈ Subgroup.center G := by
  simpa only [ProductHom.left_apply, multiply_apply, OneMemClass.coe_one, mul_one] using
    ProductHom.left_center (multiply P Q hc) (multiply_surjective P Q hc hcover) hp

include P Q hc hcover in
theorem right_center {q : Q} (hq : q ∈ Subgroup.center Q) :
    (q : G) ∈ Subgroup.center G := by
  simpa only [ProductHom.right_apply, multiply_apply, OneMemClass.coe_one, one_mul] using
    ProductHom.right_center (multiply P Q hc) (multiply_surjective P Q hc hcover) hq

include hc in
/-- A central product element has central components in their own factors. -/
theorem components_central {p : P} {q : Q}
    (hpq : (p : G) * q ∈ Subgroup.center G) :
    p ∈ Subgroup.center P ∧ q ∈ Subgroup.center Q := by
  have hh := Subgroup.mem_center_iff.mp hpq
  constructor
  · rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    change (a : G) * p = p * a
    apply mul_right_cancel (b := (q : G))
    calc
      ((a : G) * p) * q = a * ((p : G) * q) := mul_assoc _ _ _
      _ = ((p : G) * q) * a := hh a
      _ = (p : G) * ((q : G) * a) := mul_assoc _ _ _
      _ = (p : G) * ((a : G) * q) := by rw [(hc a q).eq]
      _ = ((p : G) * a) * q := (mul_assoc _ _ _).symm
  · rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    change (b : G) * q = q * b
    apply mul_left_cancel (a := (p : G))
    calc
      (p : G) * ((b : G) * q) = ((p : G) * b) * q := (mul_assoc _ _ _).symm
      _ = ((b : G) * p) * q := by rw [(hc p b).eq]
      _ = (b : G) * ((p : G) * q) := mul_assoc _ _ _
      _ = ((p : G) * q) * b := hh b
      _ = (p : G) * ((q : G) * b) := mul_assoc _ _ _

/-- The left quotient factor embeds in the quotient by the ambient center. -/
def leftQuotient : P ⧸ Subgroup.center P →* G ⧸ Subgroup.center G :=
  QuotientGroup.map (Subgroup.center P) (Subgroup.center G) P.subtype
    (fun _ hp => left_center P Q hc hcover hp)

/-- The right quotient factor embeds in the quotient by the ambient center. -/
def rightQuotient : Q ⧸ Subgroup.center Q →* G ⧸ Subgroup.center G :=
  QuotientGroup.map (Subgroup.center Q) (Subgroup.center G) Q.subtype
    (fun _ hq => right_center P Q hc hcover hq)

theorem quotient_commute (p : P ⧸ Subgroup.center P) (q : Q ⧸ Subgroup.center Q) :
    Commute (leftQuotient P Q hc hcover p) (rightQuotient P Q hc hcover q) := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  exact (hc p q).map (QuotientGroup.mk' (Subgroup.center G))

/-- Canonical multiplication after quotienting each factor by its center. -/
def quotientMultiply : (P ⧸ Subgroup.center P) × (Q ⧸ Subgroup.center Q) →*
    G ⧸ Subgroup.center G :=
  (leftQuotient P Q hc hcover).noncommCoprod (rightQuotient P Q hc hcover)
    (quotient_commute P Q hc hcover)

theorem quotientMultiply_bijective : Function.Bijective (quotientMultiply P Q hc hcover) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    rintro ⟨p, q⟩ hpq
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
    have h : (p : G) * q ∈ Subgroup.center G := by
      change (QuotientGroup.mk' (Subgroup.center G)) (p : G) *
        (QuotientGroup.mk' (Subgroup.center G)) (q : G) = 1 at hpq
      rw [← map_mul] at hpq
      exact (QuotientGroup.eq_one_iff _).mp hpq
    obtain ⟨hp, hq⟩ := components_central P Q hc h
    exact Prod.ext ((QuotientGroup.eq_one_iff _).mpr hp) ((QuotientGroup.eq_one_iff _).mpr hq)
  · intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨p, q, rfl⟩ := hcover g
    exact ⟨(QuotientGroup.mk p, QuotientGroup.mk q),
      ((QuotientGroup.mk' (Subgroup.center G)).map_mul (p : G) (q : G)).symm⟩

/-- Quotienting by the center turns a commuting product into a direct product. -/
noncomputable def quotientEquiv :
    (P ⧸ Subgroup.center P) × (Q ⧸ Subgroup.center Q) ≃* G ⧸ Subgroup.center G :=
  MulEquiv.ofBijective (quotientMultiply P Q hc hcover) (quotientMultiply_bijective P Q hc hcover)

end CentralProducts

variable {G : Type*} [Group G]

/-- A soluble retract contained in the derived subgroup is trivial. -/
theorem retract_eq_bot_of_le_commutator [IsSolvable G] (T : Subgroup G)
    (r : G →* T) (hr : ∀ t : T, r t = t) (hT : T ≤ commutator G) : T = ⊥ := by
  have hsurj : Function.Surjective r := fun t => ⟨t, hr t⟩
  have hmap : (commutator G).map r = commutator T := by
    rw [map_commutator_eq, (MonoidHom.range_eq_top.mpr hsurj), commutator_def]
  have hperfect : commutator T = ⊤ := by
    apply top_unique
    intro t _
    rw [← hmap]
    exact ⟨t, hT t.property, hr t⟩
  letI : Subsingleton T := subsingleton_of_solvable_perfect hperfect
  exact T.eq_bot_of_subsingleton

end Kourovka
