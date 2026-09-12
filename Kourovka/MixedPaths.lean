/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.PathExpansion

namespace Kourovka
namespace ProductPaths

variable {A B : Type*} [Group A] [Group B]

/-- The finite-path identity rules out a path with distinct middle and terminal vertices. -/
theorem crossed_word_not_nonabelian (f : A × B →* A × B) (m : ℕ) (hm : 0 < m)
    (hp : ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw)
    (u v : List Bool) (j k : Bool) (hu : u.length = m) (hv : (j :: v).length = m)
    (hjk : j ≠ k) : ¬ Nonabelian f ((u ++ (j :: v)) ++ [k]) := by
  intro hn
  have hlen : 2 * m < ((u ++ (j :: v)) ++ [k]).length := by
    simp only [List.length_append, List.length_singleton, hu, hv]
    omega
  have he := hp _ hlen hn
  have hm2 : m < m + m := by omega
  have hm0 : ¬ m < m := by omega
  have h2 : ¬ 2 * m < m + m := by omega
  simp only [List.getElem_append, List.length_append, hu, hv, hm2, hm0, h2,
    dif_pos, Nat.sub_self, List.getElem_cons_zero] at he
  have hz : 2 * m - (m + m) = 0 := by omega
  simp only [hz, List.getElem_cons_zero] at he
  exact hjk he

/-- Every term in a mixed two-block expansion has central image. -/
theorem mixed_term_central (f : A × B →* A × B) (hf : Function.Surjective f)
    (m : ℕ) (hm : 0 < m)
    (hp : ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw)
    (u v : List Bool) (hu : u.length = m) (hv : v.length = m)
    (j k : Bool) (hjk : j ≠ k) (x : A × B) :
    path f u (axis j (path f v (axis k x))) ∈ Subgroup.center (A × B) := by
  cases v with
  | nil => simp only [List.length_nil] at hv; omega
  | cons i v =>
      rw [axis_path]
      split_ifs with hji
      · subst i
        obtain ⟨y, rfl⟩ := hf x
        have hc := path_central_of_not_nonabelian f hf ((u ++ (j :: v)) ++ [k])
          (crossed_word_not_nonabelian f m hm hp u v j k hu hv hjk) y
        simpa only [path_append, MonoidHom.comp_apply, path_cons, path_nil] using hc
      · simpa only [map_one] using (Subgroup.center (A × B)).one_mem

/-- A common iterate kills each mixed off-diagonal composite modulo the center. -/
theorem mixed_iterate_central [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ (j k : Bool), j ≠ k → ∀ x : A × B,
      f^[m] (axis j (f^[m] (axis k x))) ∈ Subgroup.center (A × B) := by
  obtain ⟨m, hm, hp⟩ := finitePath_middle_eq_terminal f hf
  refine ⟨m, hm, ?_⟩
  intro j k hjk x
  let g : A × B →* A × B := (iterateHom f m).comp (axis j)
  change g (f^[m] (axis k x)) ∈ _
  rw [← path_expansion f m (axis k x), g.map_list_prod]
  apply Subgroup.list_prod_mem
  intro t ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
  change f^[m] (axis j (path f v (axis k x))) ∈ _
  rw [← path_expansion]
  apply Subgroup.list_prod_mem
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact mixed_term_central f hf m hm hp u v (allWords_length _ _ hu)
    (allWords_length _ _ hv) j k hjk x

end ProductPaths
end Kourovka
