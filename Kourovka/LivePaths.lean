/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.PathWeight
import Kourovka.FinitePaths
import Mathlib.Data.List.OfFn

namespace Kourovka
namespace ProductPaths

variable {A B : Type*} [Group A] [Group B]

/-- The nonabelian leaves at a fixed depth below a path. -/
def liveDescendants (f : A × B →* A × B) (w : List Bool) : ℕ → Set (List Bool)
  | 0 => {v | v = w ∧ Nonabelian f v}
  | n + 1 => liveDescendants f (w ++ [false]) n ∪ liveDescendants f (w ++ [true]) n

theorem liveDescendants_finite (f : A × B →* A × B) (n : ℕ) :
    ∀ w, (liveDescendants f w n).Finite := by
  induction n with
  | zero =>
      intro w
      exact (Set.finite_singleton w).subset (fun _ h => h.1)
  | succ n ih =>
      intro w
      exact (ih (w ++ [false])).union (ih (w ++ [true]))

/-- Every nonabelian extension occurs in the corresponding finite level. -/
theorem append_mem_liveDescendants (f : A × B →* A × B) (u : List Bool) :
    ∀ w, Nonabelian f (w ++ u) → w ++ u ∈ liveDescendants f w u.length := by
  induction u with
  | nil =>
      intro w h
      exact ⟨List.append_nil w, h⟩
  | cons i u ih =>
      intro w h
      have ha : w ++ i :: u = (w ++ [i]) ++ u := by simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [ha] at h ⊢
      cases i
      · exact Or.inl (ih (w ++ [false]) h)
      · exact Or.inr (ih (w ++ [true]) h)

/-- The number of nonabelian leaves is uniformly bounded by the root's finite budget. -/
theorem liveDescendants_ncard_le [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) (n : ℕ) :
    ∀ w, (liveDescendants f w n).ncard ≤ pathWeight f w := by
  classical
  induction n with
  | zero =>
      intro w
      by_cases h : Nonabelian f w
      · have he : liveDescendants f w 0 = {w} := by
          ext v
          simp only [liveDescendants, Set.mem_setOf_eq, Set.mem_singleton_iff]
          exact ⟨And.left, fun hv => ⟨hv, hv ▸ h⟩⟩
        rw [he, Set.ncard_singleton]
        exact pathWeight_pos f w h
      · have he : liveDescendants f w 0 = ∅ := by
          ext v
          simp only [liveDescendants, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨rfl, hv⟩
          exact h hv
        rw [he, Set.ncard_empty]
        exact Nat.zero_le _
  | succ n ih =>
      intro w
      calc
        (liveDescendants f w (n + 1)).ncard ≤
            (liveDescendants f (w ++ [false]) n).ncard +
              (liveDescendants f (w ++ [true]) n).ncard := Set.ncard_union_le _ _
        _ ≤ pathWeight f (w ++ [false]) + pathWeight f (w ++ [true]) :=
          Nat.add_le_add (ih _) (ih _)
        _ ≤ pathWeight f w := children_weight_le f hf w

/-- The initial word of an infinite binary path. -/
def initialWord (n : ℕ) (x : ℕ → Bool) : List Bool :=
  List.ofFn (FinitePaths.initialSegment n x)

/-- Infinite paths whose every finite initial word has nonabelian image. -/
def livePaths (f : A × B →* A × B) : Set (ℕ → Bool) :=
  {x | ∀ n, Nonabelian f (initialWord n x)}

/-- The group-theoretic branching budget bounds every finite prefix set. -/
theorem livePaths_prefix_bound [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) (n : ℕ) :
    (FinitePaths.initialSegment n '' livePaths f).ncard ≤ pathWeight f [] := by
  have hsub : List.ofFn '' (FinitePaths.initialSegment n '' livePaths f) ⊆
      liveDescendants f [] n := by
    rintro w ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    have h := append_mem_liveDescendants f (initialWord n x) [] (by simpa using hx n)
    simpa only [List.nil_append, initialWord, List.length_ofFn] using h
  calc
    (FinitePaths.initialSegment n '' livePaths f).ncard =
        (List.ofFn '' (FinitePaths.initialSegment n '' livePaths f)).ncard :=
      (Set.ncard_image_of_injective _ List.ofFn_injective).symm
    _ ≤ (liveDescendants f [] n).ncard :=
      Set.ncard_le_ncard hsub (liveDescendants_finite f n [])
    _ ≤ pathWeight f [] := liveDescendants_ncard_le f hf n []

/-- There are only finitely many infinite nonabelian paths. -/
theorem livePaths_finite [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) : (livePaths f).Finite :=
  FinitePaths.finite_of_bounded_prefixes (livePaths f) (pathWeight f [])
    (livePaths_prefix_bound f hf)

theorem initialWord_succ (n : ℕ) (x : ℕ → Bool) :
    initialWord (n + 1) x = x 0 :: initialWord n (FinitePaths.shift x) := by
  simp only [initialWord, List.ofFn_succ]
  rfl

/-- Deleting the first vertex preserves an infinite nonabelian path. -/
theorem livePaths_shift (f : A × B →* A × B) (x : ℕ → Bool) (hx : x ∈ livePaths f) :
    FinitePaths.shift x ∈ livePaths f := by
  intro n
  have h := hx (n + 1)
  rw [initialWord_succ] at h
  exact nonabelian_suffix f [x 0] (initialWord n (FinitePaths.shift x)) h

/-- The factorial of the product's weight works for every live path and every epimorphism. -/
theorem livePaths_factorial_middle_eq_terminal [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∀ x ∈ livePaths f,
      x (CenterWeight.weight (A × B)).factorial =
        x (2 * (CenterWeight.weight (A × B)).factorial) :=
  FinitePaths.factorial_middle_eq_terminal_of_bounded_prefixes
    (livePaths f) (CenterWeight.weight (A × B))
    (fun n => by simpa only [pathWeight_nil] using livePaths_prefix_bound f hf n)
    (livePaths_shift f)

/-- One common power of the shift agrees with its square on every live path. -/
theorem livePaths_middle_eq_terminal [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ livePaths f, x m = x (2 * m) :=
  ⟨(CenterWeight.weight (A × B)).factorial, Nat.factorial_pos _,
    livePaths_factorial_middle_eq_terminal f hf⟩

end ProductPaths
end Kourovka
