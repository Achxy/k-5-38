/-
Authors: Achyuth Jayadevan <achyuth@jayadevan.in>
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.DerivedReduction
import Kourovka.AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective

/-! # Integral lifts for central corrections -/

noncomputable section

open scoped nonZeroDivisors

namespace Kourovka.CentralLattice

variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]

/-- Saturation in an abelian group, defined by ordinary torsion in the quotient. -/
def saturation (D : Submodule ℤ M) : Submodule ℤ M :=
  (Submodule.torsion ℤ (M ⧸ D)).comap D.mkQ

theorem mem_saturation (D : Submodule ℤ M) (x : M) :
    x ∈ saturation D ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ D := by
  change (∃ n : ℤ⁰, n • D.mkQ x = 0) ↔ _
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, nonZeroDivisors.coe_ne_zero n, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero D).mp hn
  · rintro ⟨n, hn, hx⟩
    exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩,
      (Submodule.Quotient.mk_eq_zero D).mpr hx⟩

theorem le_saturation (D : Submodule ℤ M) : D ≤ saturation D := by
  intro x hx
  exact (mem_saturation D x).mpr ⟨1, one_ne_zero, by simpa using hx⟩

theorem smul_mem_saturation_iff (D : Submodule ℤ M) {n : ℤ} (hn : n ≠ 0) (x : M) :
    n • x ∈ saturation D ↔ x ∈ saturation D := by
  constructor
  · intro hx
    obtain ⟨m, hm, hmx⟩ := (mem_saturation D _).mp hx
    exact (mem_saturation D x).mpr ⟨m * n, mul_ne_zero hm hn, by
      simpa only [mul_smul] using hmx⟩
  · exact (saturation D).smul_mem n

instance quotientSaturation_torsionFree (D : Submodule ℤ M) :
    NoZeroSMulDivisors ℤ (M ⧸ saturation D) where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    intro n x h
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      obtain ⟨x, rfl⟩ := (saturation D).mkQ_surjective x
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      apply (smul_mem_saturation_iff D hn x).mp
      exact (Submodule.Quotient.mk_eq_zero _).mp h

/-- Finite generation supplies a single nonzero denominator for the saturated image. -/
theorem exists_denominator [Module.Finite ℤ M] (D : Submodule ℤ M) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ saturation D, d • x ∈ D := by
  let S := saturation D
  let E : Submodule ℤ S := D.comap S.subtype
  have ht : Module.IsTorsion ℤ (S ⧸ E) := by
    intro x
    obtain ⟨x, rfl⟩ := E.mkQ_surjective x
    obtain ⟨n, hn, hx⟩ := (mem_saturation D x.val).mp x.property
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero E).mpr hx
  obtain ⟨d, hd, hd0⟩ := Set.nonempty_iff_ne_empty.mpr
    (Submodule.annihilator_top_inter_nonZeroDivisors ht)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd0, ?_⟩
  intro x hx
  have hzero := (Submodule.mem_annihilator.mp hd) (E.mkQ ⟨x, hx⟩) Submodule.mem_top
  exact (Submodule.Quotient.mk_eq_zero E).mp hzero

/-- A saturated subgroup of a finitely generated abelian group admits a retraction. -/
theorem exists_retraction [Module.Finite ℤ M] (D : Submodule ℤ M) :
    ∃ p : M →ₗ[ℤ] saturation D, ∀ x : saturation D, p x = x := by
  let S := saturation D
  obtain ⟨j, hj⟩ := Module.projective_lifting_property S.mkQ
    (LinearMap.id : M ⧸ S →ₗ[ℤ] M ⧸ S) S.mkQ_surjective
  let p : M →ₗ[ℤ] S := (LinearMap.id - j.comp S.mkQ).codRestrict S (by
    intro x
    apply (Submodule.Quotient.mk_eq_zero S).mp
    change S.mkQ (x - j (S.mkQ x)) = 0
    rw [map_sub]
    have he := congrArg (fun f : M ⧸ S →ₗ[ℤ] M ⧸ S => f (S.mkQ x)) hj
    change S.mkQ (j (S.mkQ x)) = S.mkQ x at he
    rw [he, sub_self])
  refine ⟨p, ?_⟩
  intro x
  apply Subtype.ext
  change x.val - j (S.mkQ x.val) = x.val
  have hx : S.mkQ x.val = 0 := (Submodule.Quotient.mk_eq_zero S).mpr x.property
  simp [hx]

theorem map_mem_saturation (D : Submodule ℤ M) (u : M →ₗ[ℤ] M)
    (hu : ∀ x ∈ D, u x ∈ D) {x : M} (hx : x ∈ saturation D) :
    u x ∈ saturation D := by
  obtain ⟨n, hn, hnx⟩ := (mem_saturation D x).mp hx
  exact (mem_saturation D (u x)).mpr ⟨n, hn, by simpa using hu _ hnx⟩

/-- The integral correction in the free quotient is lifted into the original source of
central elements. No basis or collection of central lifts is assumed as input. -/
theorem exists_free_correction [Module.Finite ℤ M] [NoZeroSMulDivisors ℤ M]
    (c : Z →ₗ[ℤ] M) (u : M →ₗ[ℤ] M) (d : ℤ) (hd : d ≠ 0)
    (hden : ∀ x ∈ saturation (LinearMap.range c), d • x ∈ (LinearMap.range c))
    (hu : ∀ x ∈ (LinearMap.range c), u x ∈ (LinearMap.range c))
    (hrow : ∀ y, ∃ x z, u x + c z = y)
    (hcong : ∀ x, ∃ y, u x - x = d • y) :
    ∃ h : M →ₗ[ℤ] Z, Function.Surjective (u + c.comp h) := by
  let S := saturation (LinearMap.range c)
  obtain ⟨p, hp⟩ := exists_retraction (LinearMap.range c)
  have hdelta : ∀ x : S, x.val - u x.val ∈ (LinearMap.range c) := by
    intro x
    obtain ⟨y, hy⟩ := hcong x.val
    have hs : u x.val - x.val ∈ S :=
      S.sub_mem (map_mem_saturation (LinearMap.range c) u hu x.property) x.property
    rw [hy] at hs
    have hsy : y ∈ S := (smul_mem_saturation_iff (LinearMap.range c) hd y).mp hs
    have hdy := hden y hsy
    have hneg := (LinearMap.range c).neg_mem hdy
    simpa only [← hy, neg_sub] using hneg
  let delta : S →ₗ[ℤ] (LinearMap.range c) :=
    (S.subtype - u.comp S.subtype).codRestrict (LinearMap.range c) hdelta
  obtain ⟨k, hk⟩ := Module.projective_lifting_property (LinearMap.rangeRestrict c) delta
    (by rintro ⟨x, z, rfl⟩; exact ⟨z, rfl⟩)
  let h := k.comp p
  refine ⟨h, ?_⟩
  let v := u + c.comp h
  have hv : ∀ x : S, v x.val = x.val := by
    intro x
    have he := congrArg (fun f : S →ₗ[ℤ] (LinearMap.range c) => (f x).val) hk
    change c (k x) = x.val - u x.val at he
    change u x.val + c (k (p x.val)) = x.val
    rw [hp x, he]
    abel
  have hdiff : ∀ x, v x - u x ∈ S := by
    intro x
    change (u x + c (h x)) - u x ∈ S
    have hc : c (h x) ∈ S := le_saturation (LinearMap.range c) ⟨h x, rfl⟩
    simpa only [add_sub_cancel_left] using hc
  intro y
  obtain ⟨x, z, hz⟩ := hrow y
  have hsy : y - v x ∈ S := by
    rw [← hz]
    have hc : c z ∈ S := le_saturation (LinearMap.range c) ⟨z, rfl⟩
    have he : u x + c z - v x = c z - (v x - u x) := by abel
    rw [he]
    exact S.sub_mem hc (hdiff x)
  refine ⟨x + (y - v x), ?_⟩
  change v (x + (y - v x)) = y
  rw [map_add, hv ⟨y - v x, hsy⟩]
  simp [sub_eq_add_neg, add_left_comm]

/-- Every endomorphism preserves torsion. -/
theorem map_torsion (u : M →ₗ[ℤ] M) {x : M}
    (hx : x ∈ Submodule.torsion ℤ M) : u x ∈ Submodule.torsion ℤ M := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  change (n : ℤ) • u x = 0
  change (n : ℤ) • x = 0 at hn
  simpa only [map_smul, map_zero] using congrArg u hn

/-- The free quotient of a finitely generated abelian group. -/
abbrev FreeQuotient (M : Type*) [AddCommGroup M] := M ⧸ Submodule.torsion ℤ M

/-- The action induced on the quotient by torsion. -/
def freeMap (u : M →ₗ[ℤ] M) : FreeQuotient M →ₗ[ℤ] FreeQuotient M :=
  (Submodule.torsion ℤ M).mapQ (Submodule.torsion ℤ M) u (fun _ => map_torsion u)

@[simp] theorem freeMap_mkQ (u : M →ₗ[ℤ] M) (x : M) :
    freeMap u ((Submodule.torsion ℤ M).mkQ x) =
      (Submodule.torsion ℤ M).mkQ (u x) := rfl

/-- Finite generation provides an integer annihilating every torsion element. -/
theorem exists_torsion_annihilator [Module.Finite ℤ M] :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ Submodule.torsion ℤ M, d • x = 0 := by
  let T := Submodule.torsion ℤ M
  obtain ⟨d, hd, hd0⟩ := Set.nonempty_iff_ne_empty.mpr
    (Submodule.annihilator_top_inter_nonZeroDivisors
      (Submodule.torsion_isTorsion (R := ℤ) (M := M)))
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd0, ?_⟩
  intro x hx
  exact congrArg Subtype.val ((Submodule.mem_annihilator.mp hd) (⟨x, hx⟩ : T) Submodule.mem_top)

theorem smul_mem_torsion_iff {d : ℤ} (hd : d ≠ 0) (x : M) :
    d • x ∈ Submodule.torsion ℤ M ↔ x ∈ Submodule.torsion ℤ M := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n * ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    exact (mul_smul (n : ℤ) d x).trans hn
  · exact (Submodule.torsion ℤ M).smul_mem d

/-- Congruence modulo an integer annihilating torsion forces the identity on torsion. -/
theorem eq_on_torsion_of_congr (u : M →ₗ[ℤ] M) (d : ℤ) (hd : d ≠ 0)
    (hkill : ∀ x ∈ Submodule.torsion ℤ M, d • x = 0)
    (hcong : ∀ x, ∃ y, u x - x = d • y) :
    ∀ x ∈ Submodule.torsion ℤ M, u x = x := by
  intro x hx
  obtain ⟨y, hy⟩ := hcong x
  have hdy : d • y ∈ Submodule.torsion ℤ M :=
    hy ▸ (Submodule.torsion ℤ M).sub_mem (map_torsion u hx) hx
  have hzero := hkill y ((smul_mem_torsion_iff hd y).mp hdy)
  exact sub_eq_zero.mp (hy.trans hzero)

/-- Lift the free-quotient correction to the full finitely generated abelian group. -/
theorem exists_correction_of_congr [Module.Finite ℤ M]
    (c : Z →ₗ[ℤ] M) (u : M →ₗ[ℤ] M) (d : ℤ) (hd : d ≠ 0)
    (hden : ∀ x ∈ saturation (LinearMap.range ((Submodule.torsion ℤ M).mkQ.comp c)),
      d • x ∈ LinearMap.range ((Submodule.torsion ℤ M).mkQ.comp c))
    (hkill : ∀ x ∈ Submodule.torsion ℤ M, d • x = 0)
    (hu : ∀ x ∈ LinearMap.range c, u x ∈ LinearMap.range c)
    (hrow : ∀ y, ∃ x z, u x + c z = y)
    (hcong : ∀ x, ∃ y, u x - x = d • y) :
    ∃ h : M →ₗ[ℤ] Z, Function.Surjective (u + c.comp h) := by
  let T := Submodule.torsion ℤ M
  let q := T.mkQ
  let cq := q.comp c
  have huq : ∀ x ∈ LinearMap.range cq, freeMap u x ∈ LinearMap.range cq := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hu (c z) ⟨z, rfl⟩
    exact ⟨w, congrArg q hw⟩
  have hrowq : ∀ y : FreeQuotient M, ∃ x z, freeMap u x + cq z = y := by
    intro y
    obtain ⟨y, rfl⟩ := T.mkQ_surjective y
    obtain ⟨x, z, hz⟩ := hrow y
    exact ⟨q x, z, by simpa only [map_add] using congrArg q hz⟩
  have hcongq : ∀ x : FreeQuotient M, ∃ y, freeMap u x - x = d • y := by
    intro x
    obtain ⟨x, rfl⟩ := T.mkQ_surjective x
    obtain ⟨y, hy⟩ := hcong x
    exact ⟨q y, by simpa only [map_sub, map_smul] using congrArg q hy⟩
  obtain ⟨k, hk⟩ := exists_free_correction cq (freeMap u) d hd hden huq hrowq hcongq
  let h := k.comp q
  let v := u + c.comp h
  have hqv : ∀ x, q (v x) = (freeMap u + cq.comp k) (q x) := by
    intro x
    change q (u x + c (k (q x))) = q (u x) + q (c (k (q x)))
    exact map_add q _ _
  have hvt : ∀ x ∈ T, v x = x := by
    intro x hx
    have hux := eq_on_torsion_of_congr u d hd hkill hcong x hx
    have hqx : q x = 0 := (Submodule.Quotient.mk_eq_zero T).mpr hx
    change u x + c (k (q x)) = x
    simp [hux, hqx]
  refine ⟨h, ?_⟩
  intro y
  obtain ⟨a, ha⟩ := hk (q y)
  obtain ⟨x, rfl⟩ := T.mkQ_surjective a
  have hx : q (v x) = q y := (hqv x).trans ha
  have ht : y - v x ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero T).mp
    change q (y - v x) = 0
    rw [map_sub, hx, sub_self]
  refine ⟨x + (y - v x), ?_⟩
  change v (x + (y - v x)) = y
  rw [map_add, hvt _ ht]
  simp [sub_eq_add_neg, add_left_comm]

/-- One congruence level works for every endomorphism preserving a given central image.
Both the denominator and the correcting homomorphism are proved to exist. -/
theorem exists_uniform_correction_modulus [Module.Finite ℤ M] (c : Z →ₗ[ℤ] M) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ u : M →ₗ[ℤ] M,
      (∀ x ∈ LinearMap.range c, u x ∈ LinearMap.range c) →
      (∀ y, ∃ x z, u x + c z = y) →
      (∀ x, ∃ y, u x - x = d • y) →
      ∃ h : M →ₗ[ℤ] Z, Function.Surjective (u + c.comp h) := by
  let cq := (Submodule.torsion ℤ M).mkQ.comp c
  obtain ⟨d, hd, hden⟩ := exists_denominator (LinearMap.range cq)
  obtain ⟨e, he, hkill⟩ := exists_torsion_annihilator (M := M)
  refine ⟨d * e, mul_ne_zero hd he, ?_⟩
  intro u hu hrow hcong
  apply exists_correction_of_congr c u (d * e) (mul_ne_zero hd he) _ _ hu hrow hcong
  · intro x hx
    rw [mul_comm d e, mul_smul]
    exact (LinearMap.range cq).smul_mem e (hden x hx)
  · intro x hx
    rw [mul_smul, hkill x hx, smul_zero]

section Groups

variable {G : Type*} [Group G]

/-- The ordinary induced endomorphism of abelianization, viewed as an integer-linear map. -/
def abelianMap (u : G →* G) :
    Additive (Abelianization G) →ₗ[ℤ] Additive (Abelianization G) :=
  (Abelianization.map u).toAdditive.toIntLinearMap

/-- The image of the actual center in the ordinary abelianization. -/
def centerImage : Additive (Subgroup.center G) →ₗ[ℤ] Additive (Abelianization G) :=
  (Abelianization.of.comp (Subgroup.center G).subtype).toAdditive.toIntLinearMap

/-- An integer-linear correction on abelianization gives a genuine center-valued homomorphism. -/
def centralLift
    (k : Additive (Abelianization G) →ₗ[ℤ] Additive (Subgroup.center G)) :
    G →* Subgroup.center G where
  toFun x := Additive.toMul (k (Additive.ofMul (Abelianization.of x)))
  map_one' := by
    change k (Additive.ofMul (Abelianization.of 1)) = 0
    simpa only [map_one] using k.map_zero
  map_mul' x y := by
    change k (Additive.ofMul (Abelianization.of (x * y))) =
      k (Additive.ofMul (Abelianization.of x)) + k (Additive.ofMul (Abelianization.of y))
    rw [map_mul]
    exact k.map_add _ _

theorem abelianMap_centralCorrection (u : G →* G)
    (k : Additive (Abelianization G) →ₗ[ℤ] Additive (Subgroup.center G)) :
    abelianMap (centralCorrection u (centralLift k)) = abelianMap u + centerImage.comp k := by
  ext a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  change Abelianization.of (u x * ↑(centralLift k x)) =
    Abelianization.of (u x) * Abelianization.of (↑(centralLift k x) : G)
  exact map_mul Abelianization.of _ _

/-- A congruence level is obtained from the finitely generated abelianization alone.
Every qualifying diagonal endomorphism then has an actual surjective central correction. -/
theorem exists_group_correction_modulus [Group.FG G] :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ u : G →* G,
      (∀ z ∈ Subgroup.center G, u z ∈ Subgroup.center G) →
      (∀ y, ∃ x z, z ∈ Subgroup.center G ∧ u x * z = y) →
      (∀ x : Additive (Abelianization G), ∃ y, abelianMap u x - x = d • y) →
      (∀ y ∈ commutator G, ∃ x ∈ commutator G, u x = y) →
      ∃ h : G →* Subgroup.center G, Function.Surjective (centralCorrection u h) := by
  letI : Group.FG (Abelianization G) :=
    Group.fg_of_surjective (f := Abelianization.of) QuotientGroup.mk_surjective
  letI : Module.Finite ℤ (Additive (Abelianization G)) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨d, hd, hmod⟩ := exists_uniform_correction_modulus (centerImage (G := G))
  refine ⟨d, hd, ?_⟩
  intro u hcenter hrow hcong hder
  have hu : ∀ x ∈ LinearMap.range (centerImage (G := G)),
      abelianMap u x ∈ LinearMap.range (centerImage (G := G)) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨Additive.ofMul (⟨u z.toMul.val, hcenter z.toMul.val z.toMul.property⟩ :
      Subgroup.center G), ?_⟩
    rfl
  have hrowAb : ∀ y : Additive (Abelianization G),
      ∃ x z, abelianMap u x + centerImage z = y := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨x, z, hz, hxy⟩ := hrow y
    refine ⟨Additive.ofMul (Abelianization.of x), Additive.ofMul (⟨z, hz⟩ : Subgroup.center G), ?_⟩
    change Abelianization.of (u x) * Abelianization.of z = Abelianization.of y
    rw [← map_mul, hxy]
  obtain ⟨k, hk⟩ := hmod (abelianMap u) hu hrowAb hcong
  refine ⟨centralLift k, centralCorrection_surjective u (centralLift k) hder ?_⟩
  rw [← abelianMap_centralCorrection u k] at hk
  exact hk

end Groups

end Kourovka.CentralLattice
