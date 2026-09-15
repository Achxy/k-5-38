/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.LivePaths
import Mathlib.Data.List.Infix

namespace Kourovka
namespace ProductPaths

variable {A B : Type*} [Group A] [Group B]

/-- Choose one nonabelian right child whenever the current path is nonabelian. -/
noncomputable def extendWord (f : A × B →* A × B) (w : List Bool) : List Bool := by
  classical
  exact w ++ [if Nonabelian f (w ++ [false]) then false else true]

theorem extendWord_length (f : A × B →* A × B) (w : List Bool) :
    (extendWord f w).length = w.length + 1 := by
  classical
  simp only [extendWord, List.length_append, List.length_singleton]

theorem prefix_extendWord (f : A × B →* A × B) (w : List Bool) :
    w <+: extendWord f w := ⟨_, rfl⟩

theorem extendWord_nonabelian (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) : Nonabelian f (extendWord f w) := by
  classical
  unfold extendWord
  split_ifs with hfalse
  · exact hfalse
  · exact (nonabelian_child f hf w h).resolve_left hfalse

noncomputable def extensionWord (f : A × B →* A × B) (w : List Bool) (n : ℕ) : List Bool :=
  (extendWord f)^[n] w

theorem extensionWord_length (f : A × B →* A × B) (w : List Bool) (n : ℕ) :
    (extensionWord f w n).length = w.length + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((extendWord f)^[n + 1] w).length = _
      rw [Function.iterate_succ_apply']
      rw [extendWord_length, ← extensionWord, ih]
      omega

theorem extensionWord_nonabelian (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) (n : ℕ) :
    Nonabelian f (extensionWord f w n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      change Nonabelian f ((extendWord f)^[n + 1] w)
      rw [Function.iterate_succ_apply']
      exact extendWord_nonabelian f hf _ ih

theorem extensionWord_prefix (f : A × B →* A × B) (w : List Bool)
    {n m : ℕ} (h : n ≤ m) : extensionWord f w n <+: extensionWord f w m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih =>
      apply ih.trans
      change extensionWord f w (n + k) <+: (extendWord f)^[n + (k + 1)] w
      rw [show n + (k + 1) = (n + k) + 1 by omega, Function.iterate_succ_apply']
      exact prefix_extendWord f _

/-- The compatible finite extensions determine one infinite binary path. -/
noncomputable def extensionStream (f : A × B →* A × B) (w : List Bool) (n : ℕ) : Bool :=
  (extensionWord f w (n + 1))[n]'(by rw [extensionWord_length]; omega)

theorem initialWord_extensionStream (f : A × B →* A × B) (w : List Bool) (n : ℕ) :
    initialWord n (extensionStream f w) = (extensionWord f w n).take n := by
  apply List.ext_getElem
  · simp only [initialWord, List.length_ofFn, List.length_take, extensionWord_length]
    omega
  · intro i hi hj
    have hin : i < n := by simpa only [initialWord, List.length_ofFn] using hi
    simp only [initialWord, List.getElem_ofFn, FinitePaths.initialSegment,
      List.getElem_take, extensionStream]
    exact (extensionWord_prefix f w (by omega : i + 1 ≤ n)).getElem
      (by rw [extensionWord_length]; omega)

/-- Nonabelianity passes to every initial subpath. -/
theorem nonabelian_of_prefix (f : A × B →* A × B) {u v : List Bool}
    (huv : u <+: v) (hv : Nonabelian f v) : Nonabelian f u := by
  obtain ⟨s, rfl⟩ := huv
  exact nonabelian_prefix f u s hv

/-- Every finite nonabelian path extends to an infinite live path. -/
theorem exists_livePath_extension (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) :
    ∃ x ∈ livePaths f, initialWord w.length x = w := by
  refine ⟨extensionStream f w, ?_, ?_⟩
  · intro n
    rw [initialWord_extensionStream]
    exact nonabelian_of_prefix f (List.take_prefix n _)
      (extensionWord_nonabelian f hf w h n)
  · rw [initialWord_extensionStream]
    have hp : w <+: extensionWord f w w.length := extensionWord_prefix f w (Nat.zero_le _)
    exact (List.prefix_iff_eq_take.mp hp).symm

/-- The uniform factorial shift identity holds on all sufficiently long nonabelian paths. -/
theorem finitePath_factorial_middle_eq_terminal [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw := by
  let m := (CenterWeight.weight (A × B)).factorial
  change ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
    w[m]'(by omega) = w[2 * m]'hw
  intro w hw hn
  obtain ⟨x, hx, hwx⟩ := exists_livePath_extension f hf w hn
  have hp := livePaths_factorial_middle_eq_terminal f hf x hx
  have hget (i : ℕ) (hi : i < w.length) : w[i] = x i := by
    have hpref : w <+: initialWord w.length x := by rw [hwx]
    simpa only [initialWord, List.getElem_ofFn, FinitePaths.initialSegment] using hpref.getElem hi
  rw [hget m (by omega), hget (2 * m) hw]
  exact hp

/-- The common shift identity applies to every sufficiently long finite nonabelian path. -/
theorem finitePath_middle_eq_terminal [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw :=
  ⟨(CenterWeight.weight (A × B)).factorial, Nat.factorial_pos _,
    finitePath_factorial_middle_eq_terminal f hf⟩

end ProductPaths
end Kourovka
