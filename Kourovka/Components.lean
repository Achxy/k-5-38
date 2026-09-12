/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod

namespace Kourovka

variable {A B K : Type*} [Group A] [Group B] [Group K]

namespace ProductHom

def left (f : A × B →* K) : A →* K := f.comp (MonoidHom.inl A B)

def right (f : A × B →* K) : B →* K := f.comp (MonoidHom.inr A B)

@[simp] theorem left_apply (f : A × B →* K) (a : A) : left f a = f (a, 1) := rfl
@[simp] theorem right_apply (f : A × B →* K) (b : B) : right f b = f (1, b) := rfl

theorem decompose (f : A × B →* K) (a : A) (b : B) :
    f (a, b) = left f a * right f b := by
  simpa using f.map_mul (a, 1) (1, b)

theorem commute (f : A × B →* K) (a : A) (b : B) :
    Commute (left f a) (right f b) := by
  change f (a, 1) * f (1, b) = f (1, b) * f (a, 1)
  rw [← map_mul, ← map_mul]
  simp

theorem row_surjective (f : A × B →* K) (hf : Function.Surjective f) (k : K) :
    ∃ a b, left f a * right f b = k := by
  obtain ⟨⟨a, b⟩, hk⟩ := hf k
  exact ⟨a, b, (decompose f a b).symm.trans hk⟩

theorem left_center (f : A × B →* K) (hf : Function.Surjective f)
    {a : A} (ha : a ∈ Subgroup.center A) : left f a ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at ha ⊢
  intro k
  obtain ⟨⟨x, y⟩, rfl⟩ := hf k
  change f (x, y) * f (a, 1) = f (a, 1) * f (x, y)
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul, ha x]

theorem right_center (f : A × B →* K) (hf : Function.Surjective f)
    {b : B} (hb : b ∈ Subgroup.center B) : right f b ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at hb ⊢
  intro k
  obtain ⟨⟨x, y⟩, rfl⟩ := hf k
  change f (x, y) * f (1, b) = f (1, b) * f (x, y)
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul, hb y]

end ProductHom

/-- A homomorphism with central image vanishes on the derived subgroup. -/
theorem central_map_kills_commutator (f : A →* B)
    (hf : ∀ a, f a ∈ Subgroup.center B) : commutator A ≤ f.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (hf b) (f a))

/-- Multiplying a homomorphism by a central homomorphism is a homomorphism. -/
def centralCorrection (u : A →* A) (h : A →* Subgroup.center A) : A →* A where
  toFun a := u a * h a
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, Subgroup.coe_mul]
    have hc := Subgroup.mem_center_iff.mp (h a).property (u b)
    calc
      (u a * u b) * (↑(h a) * ↑(h b)) = u a * (u b * ↑(h a)) * ↑(h b) := by
        simp only [mul_assoc]
      _ = u a * (↑(h a) * u b) * ↑(h b) := by rw [hc]
      _ = (u a * ↑(h a)) * (u b * ↑(h b)) := by simp only [mul_assoc]

theorem centralCorrection_eq_on_commutator (u : A →* A) (h : A →* Subgroup.center A)
    {a : A} (ha : a ∈ commutator A) : centralCorrection u h a = u a := by
  have hc : (Subgroup.center A).subtype.comp h a = 1 :=
    central_map_kills_commutator ((Subgroup.center A).subtype.comp h)
      (fun x => (h x).property) ha
  change u a * ↑(h a) = u a
  change ↑(h a) = (1 : A) at hc
  rw [hc, mul_one]

end Kourovka
