/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

namespace Kourovka
namespace FinitePaths

/-- The first `n` entries of a sequence. -/
def initialSegment {α : Type*} (n : ℕ) (x : ℕ → α) : Fin n → α := fun i => x i

/-- A finite family of distinct infinite sequences is separated by some finite prefix. -/
theorem exists_injective_prefix {α ι : Type*} [Fintype ι]
    (f : ι → ℕ → α) (hf : Function.Injective f) :
    ∃ n, Function.Injective (fun i => initialSegment n (f i)) := by
  classical
  have hsep : ∀ i j : ι, i ≠ j → ∃ k, f i k ≠ f j k := by
    intro i j hij
    exact Function.ne_iff.mp (fun h => hij (hf h))
  let d : ι × ι → ℕ := fun p =>
    if h : p.1 = p.2 then 0 else Classical.choose (hsep p.1 p.2 h)
  let n := Finset.univ.sup (fun p : ι × ι => d p + 1)
  refine ⟨n, ?_⟩
  intro i j hij
  by_contra hne
  have hd : f i (d (i, j)) ≠ f j (d (i, j)) := by
    simpa only [d, dif_neg hne] using Classical.choose_spec (hsep i j hne)
  have hdn : d (i, j) < n := by
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Finset.le_sup (f := fun p : ι × ι => d p + 1) (Finset.mem_univ (i, j)))
  exact hd (congrFun hij ⟨d (i, j), hdn⟩)

/-- Uniformly bounded prefix sets allow only finitely many infinite sequences. -/
theorem finite_of_bounded_prefixes {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b) : X.Finite := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  by_contra hX
  obtain ⟨T, hTX, hT, hcard⟩ := Set.Infinite.exists_subset_ncard_eq hX (b + 1)
  letI : Fintype T := hT.fintype
  obtain ⟨n, hn⟩ := exists_injective_prefix (fun x : T => x.val) Subtype.val_injective
  have hinj : Set.InjOn (initialSegment n) T := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hn (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hle : (initialSegment n '' T).ncard ≤ (initialSegment n '' X).ncard :=
    Set.ncard_le_ncard (Set.image_mono hTX)
  rw [Set.ncard_image_of_injOn hinj, hcard] at hle
  have := hb n
  omega

/-- Every endomap of a finite set has an idempotent positive iterate. -/
theorem exists_idempotent_iterate {X : Type*} [Finite X] (f : X → X) :
    ∃ m : ℕ, 0 < m ∧ f^[2 * m] = f^[m] := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  obtain ⟨a, b, hne, hab⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n])
  have hpair : ∃ a b : ℕ, a < b ∧ f^[a] = f^[b] := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨a, b, hlt, hab⟩
    · exact ⟨b, a, hgt, hab.symm⟩
  obtain ⟨a, b, hab, heq⟩ := hpair
  let d := b - a
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hperiod : ∀ n, a ≤ n → f^[n + d] = f^[n] := by
    intro n hn
    calc
      f^[n + d] = f^[(n - a) + b] := by congr 1; omega
      _ = f^[n - a] ∘ f^[b] := Function.iterate_add _ _ _
      _ = f^[n - a] ∘ f^[a] := by rw [← heq]
      _ = f^[(n - a) + a] := (Function.iterate_add _ _ _).symm
      _ = f^[n] := by rw [Nat.sub_add_cancel hn]
  have hmultiple : ∀ k n, a ≤ n → f^[n + k * d] = f^[n] := by
    intro k
    induction k with
    | zero => intro n hn; simp
    | succ k ih =>
      intro n hn
      rw [Nat.succ_mul, ← Nat.add_assoc, hperiod (n + k * d) (by omega), ih n hn]
  let m := (a + 1) * d
  have hm : 0 < m := Nat.mul_pos (by omega) hd
  have ham : a ≤ m := by
    dsimp [m]
    nlinarith
  refine ⟨m, hm, ?_⟩
  have hfin := hmultiple (a + 1) m ham
  change f^[m + m] = f^[m] at hfin
  simpa only [two_mul] using hfin

/-- Remove the initial entry from a sequence. -/
def shift {α : Type*} (x : ℕ → α) : ℕ → α := fun n => x (n + 1)

/-- A finite shift-closed family has one common eventual period. -/
theorem middle_eq_terminal {α : Type*} (X : Set (ℕ → α)) (hX : X.Finite)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ X, x m = x (2 * m) := by
  classical
  letI : Fintype X := hX.fintype
  let s : X → X := fun x => ⟨shift x.val, hs x.val x.property⟩
  have hiter : ∀ n (x : X) k, ((s^[n]) x).val k = x.val (k + n) := by
    intro n
    induction n with
    | zero => intro x k; rfl
    | succ n ih =>
      intro x k
      rw [Function.iterate_succ_apply']
      change ((s^[n]) x).val (k + 1) = x.val (k + (n + 1))
      rw [ih]
      exact congrArg x.val (by omega)
  obtain ⟨m, hm, heq⟩ := exists_idempotent_iterate s
  refine ⟨m, hm, ?_⟩
  intro x hx
  have he := congrArg (fun t : X => t.val 0) (congrFun heq ⟨x, hx⟩)
  simpa only [hiter, Nat.zero_add] using he.symm

/-- Bounded path branching and shift closure give the common middle-to-terminal index identity. -/
theorem middle_eq_terminal_of_bounded_prefixes {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ X, x m = x (2 * m) :=
  middle_eq_terminal X (finite_of_bounded_prefixes X b hb) hs

end FinitePaths
end Kourovka
