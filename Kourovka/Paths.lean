/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Components
import Mathlib.Data.List.Basic

namespace Kourovka
namespace ProductPaths

variable {A B : Type*} [Group A] [Group B]

/-- The two canonical projections, viewed as endomorphisms of the full product. -/
def axis : Bool → (A × B →* A × B)
  | false => (MonoidHom.inl A B).comp (MonoidHom.fst A B)
  | true => (MonoidHom.inr A B).comp (MonoidHom.snd A B)

@[simp] theorem axis_false (x : A × B) : axis false x = (x.1, 1) := rfl
@[simp] theorem axis_true (x : A × B) : axis true x = (1, x.2) := rfl

theorem axis_product (x : A × B) : axis false x * axis true x = x := by
  ext <;> simp

theorem axes_commute (x y : A × B) : Commute (axis false x) (axis true y) := by
  change (x.1, (1 : B)) * (1, y.2) = (1, y.2) * (x.1, 1)
  simp

/-- A path is a composition of projected copies of the product endomorphism. -/
def path (f : A × B →* A × B) : List Bool → (A × B →* A × B)
  | [] => MonoidHom.id _
  | i :: is => (axis i).comp (f.comp (path f is))

@[simp] theorem path_nil (f : A × B →* A × B) (x : A × B) : path f [] x = x := rfl
@[simp] theorem path_cons (f : A × B →* A × B) (i : Bool) (is : List Bool) (x : A × B) :
    path f (i :: is) x = axis i (f (path f is x)) := rfl

theorem path_append (f : A × B →* A × B) (u v : List Bool) :
    path f (u ++ v) = (path f u).comp (path f v) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, path, ih]; rfl

theorem children_commute (f : A × B →* A × B) (w : List Bool) (x y : A × B) :
    Commute (path f (w ++ [false]) x) (path f (w ++ [true]) y) := by
  simp only [path_append, MonoidHom.comp_apply, path_cons, path_nil]
  exact (axes_commute (f x) (f y)).map (path f w)

/-- Distinct paths at one level have commuting images. -/
theorem level_commute (f : A × B →* A × B) :
    ∀ (u v : List Bool), u.length = v.length → u ≠ v →
      ∀ x y : A × B, Commute (path f u x) (path f v y) := by
  intro u
  induction u with
  | nil =>
      intro v hlen hne
      have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
      exact (hne hv.symm).elim
  | cons i u ih =>
      intro v hlen hne x y
      cases v with
      | nil => simp at hlen
      | cons j v =>
          have huv : u.length = v.length := by simpa using hlen
          cases i <;> cases j
          · have hne' : u ≠ v := fun h => hne (by rw [h])
            exact ((ih v huv hne' x y).map f).map (axis false)
          · exact axes_commute (f (path f u x)) (f (path f v y))
          · exact (axes_commute (f (path f v y)) (f (path f u x))).symm
          · have hne' : u ≠ v := fun h => hne (by rw [h])
            exact ((ih v huv hne' x y).map f).map (axis true)

/-- The two child images multiply onto the parent image. -/
theorem children_cover (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (x : A × B) :
    ∃ y z, path f (w ++ [false]) y * path f (w ++ [true]) z = path f w x := by
  obtain ⟨y, hy⟩ := hf x
  refine ⟨y, y, ?_⟩
  simp only [path_append, MonoidHom.comp_apply, path_cons, path_nil]
  rw [← map_mul, axis_product, hy]

/-- A path has nonabelian image, expressed directly by two noncommuting values. -/
def Nonabelian (f : A × B →* A × B) (w : List Bool) : Prop :=
  ∃ x y, ¬ Commute (path f w x) (path f w y)

theorem nonabelian_prefix (f : A × B →* A × B) (u v : List Bool)
    (h : Nonabelian f (u ++ v)) : Nonabelian f u := by
  obtain ⟨x, y, h⟩ := h
  exact ⟨path f v x, path f v y, by simpa only [path_append, MonoidHom.comp_apply] using h⟩

theorem nonabelian_suffix (f : A × B →* A × B) (u v : List Bool)
    (h : Nonabelian f (u ++ v)) : Nonabelian f v := by
  obtain ⟨x, y, h⟩ := h
  refine ⟨x, y, ?_⟩
  intro hc
  apply h
  simpa only [path_append, MonoidHom.comp_apply] using hc.map (path f u)

/-- A nonabelian path has a nonabelian right extension. -/
theorem nonabelian_child (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) :
    Nonabelian f (w ++ [false]) ∨ Nonabelian f (w ++ [true]) := by
  classical
  by_contra hn
  have hfalse : ∀ x y, Commute (path f (w ++ [false]) x) (path f (w ++ [false]) y) := by
    intro x y
    by_contra hxy
    exact hn (Or.inl ⟨x, y, hxy⟩)
  have htrue : ∀ x y, Commute (path f (w ++ [true]) x) (path f (w ++ [true]) y) := by
    intro x y
    by_contra hxy
    exact hn (Or.inr ⟨x, y, hxy⟩)
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨a, b, hab⟩ := children_cover f hf w x
  obtain ⟨c, d, hcd⟩ := children_cover f hf w y
  apply hxy
  rw [← hab, ← hcd]
  exact ((hfalse a c).mul_right (children_commute f w a d)).mul_left
    (((children_commute f w c b).symm).mul_right (htrue b d))

end ProductPaths
end Kourovka
