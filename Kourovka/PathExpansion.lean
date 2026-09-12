/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

namespace Kourovka
namespace ProductPaths

variable {A B : Type*} [Group A] [Group B]

/-- All binary words at one level, in lexicographic order. -/
def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allWords n).map (false :: ·) ++ (allWords n).map (true :: ·)

theorem allWords_length (n : ℕ) : ∀ w ∈ allWords n, w.length = n := by
  induction n with
  | zero =>
      intro w hw
      have he : w = [] := List.mem_singleton.mp hw
      subst w
      rfl
  | succ n ih =>
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        simp only [List.length_cons, ih v hv]
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        simp only [List.length_cons, ih v hv]

/-- Expand an iterate as a product of its equal-level path homomorphisms. -/
theorem path_expansion (f : A × B →* A × B) (n : ℕ) (x : A × B) :
    ((allWords n).map (fun w => path f w x)).prod = f^[n] x := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
      simp only [allWords, List.map_append, List.prod_append, List.map_map]
      change ((allWords n).map (fun w => axis false (f (path f w x)))).prod *
        ((allWords n).map (fun w => axis true (f (path f w x)))).prod = _
      have h (i : Bool) := ((axis i).comp f).map_list_prod
        ((allWords n).map (fun w => path f w x))
      simp only [List.map_map, MonoidHom.comp_apply] at h
      change ∀ i, axis i (f ((allWords n).map (fun w => path f w x)).prod) =
        ((allWords n).map (fun w => axis i (f (path f w x)))).prod at h
      rw [← h false, ← h true, ih, axis_product, Function.iterate_succ_apply']

/-- Every abelian path image is central in the whole product. -/
theorem path_central_of_not_nonabelian (f : A × B →* A × B)
    (hf : Function.Surjective f) (w : List Bool) (hn : ¬ Nonabelian f w) (x : A × B) :
    path f w x ∈ Subgroup.center (A × B) := by
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨y, rfl⟩ := (hf.iterate w.length) z
  rw [← path_expansion]
  apply Commute.list_prod_left
  intro t ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
  by_cases he : v = w
  · subst v
    by_contra hc
    exact hn ⟨y, x, hc⟩
  · exact level_commute f v w (allWords_length _ _ hv) he y x

/-- A group iterate as a bundled homomorphism. -/
def iterateHom (f : A × B →* A × B) (n : ℕ) : A × B →* A × B :=
  { toFun := f^[n]
    map_one' := iterate_map_one f n
    map_mul' := iterate_map_mul f n }

@[simp] theorem iterateHom_apply (f : A × B →* A × B) (n : ℕ) (x : A × B) :
    iterateHom f n x = f^[n] x := rfl

theorem iterateHom_surjective (f : A × B →* A × B) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (iterateHom f n) := hf.iterate n

@[simp] theorem axis_axis_same (i : Bool) (x : A × B) : axis i (axis i x) = axis i x := by
  cases i <;> rfl

theorem axis_axis_ne (i j : Bool) (hij : i ≠ j) (x : A × B) : axis i (axis j x) = 1 := by
  cases i <;> cases j <;> simp_all

/-- A projected path vanishes unless its first vertex is the selected factor. -/
theorem axis_path (i j : Bool) (f : A × B →* A × B) (w : List Bool) (x : A × B) :
    axis i (path f (j :: w) x) = if i = j then path f (j :: w) x else 1 := by
  rw [path_cons]
  split_ifs with h
  · subst j; exact axis_axis_same i _
  · exact axis_axis_ne i j h _

end ProductPaths
end Kourovka
