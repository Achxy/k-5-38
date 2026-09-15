/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
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

/-- A bound on all prefix sets also bounds the number of infinite sequences. -/
theorem ncard_le_of_bounded_prefixes {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b) : X.ncard ≤ b := by
  classical
  letI : Fintype X := (finite_of_bounded_prefixes X b hb).fintype
  obtain ⟨n, hn⟩ := exists_injective_prefix (fun x : X => x.val) Subtype.val_injective
  have hinj : Set.InjOn (initialSegment n) X := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hn (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  simpa only [Set.ncard_image_of_injOn hinj] using hb n

/-- The factorial of a cardinality bound is an idempotent exponent for every endomap. -/
theorem factorial_iterate_idempotent {X : Type*} [Fintype X]
    (f : X → X) (b : ℕ) (hcard : Fintype.card X ≤ b) :
    f^[2 * b.factorial] = f^[b.factorial] := by
  funext x
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (b + 1) => f^[i.val] x)
    (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hcard)
  have hpair : ∃ a c : ℕ, a < c ∧ c ≤ b ∧ f^[a] x = f^[c] x := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i.val, j.val, hlt, Nat.le_of_lt_succ j.isLt, heq⟩
    · exact ⟨j.val, i.val, hgt, Nat.le_of_lt_succ i.isLt, heq.symm⟩
  obtain ⟨a, c, hac, hcb, heq⟩ := hpair
  let d := c - a
  have hd : 0 < d := Nat.sub_pos_of_lt hac
  have hdb : d ≤ b := (Nat.sub_le c a).trans hcb
  have hperiod : ∀ n, a ≤ n → f^[n + d] x = f^[n] x := by
    intro n hn
    calc
      f^[n + d] x = f^[(n - a) + c] x := by congr 1; omega
      _ = f^[n - a] (f^[c] x) := Function.iterate_add_apply _ _ _ _
      _ = f^[n - a] (f^[a] x) := by rw [← heq]
      _ = f^[(n - a) + a] x := (Function.iterate_add_apply _ _ _ _).symm
      _ = f^[n] x := by rw [Nat.sub_add_cancel hn]
  have hmultiple : ∀ k n, a ≤ n → f^[n + k * d] x = f^[n] x := by
    intro k
    induction k with
    | zero => intro n hn; simp
    | succ k ih =>
      intro n hn
      rw [Nat.succ_mul, ← Nat.add_assoc, hperiod (n + k * d) (by omega), ih n hn]
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hd hdb
  have ham : a ≤ b.factorial := (Nat.le_of_lt hac).trans (hcb.trans (Nat.self_le_factorial b))
  have hfin := hmultiple k b.factorial ham
  simpa only [Nat.mul_comm k d, ← hk, two_mul] using hfin

/-- Every endomap of a finite set has an idempotent positive iterate. -/
theorem exists_idempotent_iterate {X : Type*} [Finite X] (f : X → X) :
    ∃ m : ℕ, 0 < m ∧ f^[2 * m] = f^[m] := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  exact ⟨(Fintype.card X).factorial, Nat.factorial_pos _,
    factorial_iterate_idempotent f (Fintype.card X) le_rfl⟩

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

/-- The factorial bound depends only on the number of possible prefixes, not on the shift. -/
theorem factorial_middle_eq_terminal_of_bounded_prefixes {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b)
    (hs : ∀ x ∈ X, shift x ∈ X) :
    ∀ x ∈ X, x b.factorial = x (2 * b.factorial) := by
  classical
  letI : Fintype X := (finite_of_bounded_prefixes X b hb).fintype
  let s : X → X := fun x => ⟨shift x.val, hs x.val x.property⟩
  have hcard : Fintype.card X ≤ b := by
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using
      ncard_le_of_bounded_prefixes X b hb
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
  intro x hx
  have he := congrArg (fun t : X => t.val 0)
    (congrFun (factorial_iterate_idempotent s b hcard) ⟨x, hx⟩)
  simpa only [hiter, Nat.zero_add] using he.symm

end FinitePaths
end Kourovka
