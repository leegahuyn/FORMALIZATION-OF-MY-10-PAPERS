import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalRationalEval
import PrimalitySheafVerification.ManuscriptAudit.CubicAffineFiberBound
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericAbscissaDichotomy
import PrimalitySheafVerification.ManuscriptAudit.CubicAlgebraicAbscissaDescent
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericSecantHeight
import PrimalitySheafVerification.ManuscriptAudit.CubicRationalPointHeight

/-! Positive generic Kummer height bounds the kernel of an actual natural point operation. -/

namespace ManuscriptAudit.CubicNaturalKernelDegree

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitThreeAdicTrace CubicNativePointBaseChange CubicNaturalPointEnd
open CubicGenericFunctionField CubicGenericAntiInvariant CubicGenericPointHeight
open CubicGenericSecantHeight CubicGenericAbscissaDichotomy CubicAlgebraicAbscissaDescent
open CubicNaturalRationalEval RationalMapFiberBound

noncomputable section
open scoped Classical

universe u

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] {A : K}

/-- Translating a base point by the generic point gives an actual transcendental input. -/
private theorem translate_affine (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (P : GeometricPoints K K A) :
    ∃ (x y : Model A) (hxy : (Curve (algebraMap K (Model A) A)).Nonsingular x y),
      pointsMap A (IsScalarTower.toAlgHom K K (Model A)) P + genericPoint A h₂ h₃ hA =
        .some x y hxy ∧ Transcendental K x := by
  let M := Model A
  let f := IsScalarTower.toAlgHom K K M
  let b := pointsMap A f
  let Q := genericPoint A h₂ h₃ hA
  have hTrans : Transcendental K (genericX A) :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc K) M).injective).mpr RatFunc.transcendental_X
  have hOutside : Q ∉ Set.range b := by
    rintro ⟨R, hR⟩
    obtain ⟨h, he⟩ : ∃ h, Q = .some (genericX A) (genericY A) h := ⟨_, rfl⟩
    cases R with
    | zero =>
      have h0 : (0 : GeometricPoints K M A) = Q := (map_zero b).symm.trans hR
      rw [he] at h0
      cases h0
    | some x y hxy =>
      obtain ⟨h', hMap⟩ := pointsMap_some A f x y hxy
      change pointsMap A f (.some x y hxy) = Q at hR
      rw [hMap, he, Affine.Point.some.injEq] at hR
      have hx : algebraMap K M x = genericX A := hR.1
      exact hTrans (hx ▸ isAlgebraic_algebraMap (A := M) x)
  have hSum : b P + Q ∉ Set.range b := by
    rintro ⟨R, hR⟩
    apply hOutside
    refine ⟨R - P, ?_⟩
    rw [map_sub, hR]
    abel
  change ∃ (x y : M) (hxy : (Curve (algebraMap K M A)).Nonsingular x y),
    b P + Q = .some x y hxy ∧ Transcendental K x
  cases h : b P + Q with
  | zero =>
    apply hSum.elim
    rw [h]
    exact ⟨0, map_zero b⟩
  | some x y hxy =>
    refine ⟨x, y, hxy, rfl, fun ha => hSum ?_⟩
    rw [h]
    exact in_range_of_isAlgebraic A h₂ h₃ hA hxy ha

/-- For a field-natural endomorphism with positive generic Kummer height, its arithmetic
kernel injects into a fiber whose abscissas are roots of a polynomial of that degree. -/
theorem card_of_injection_le (D : Family K A)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hHeight : height A (antiInvariantApply D (genericAntiPoint A h₂ h₃ hA)) ≠ 0)
    {T : Type*} (i : T → (D.atField K).ker) (hi : Function.Injective i) :
    Nat.card T ≤ 2 * height A (antiInvariantApply D (genericAntiPoint A h₂ h₃ hA)) := by
  let M := Model A
  let Q := genericPoint A h₂ h₃ hA
  let H := antiInvariantApply D (genericAntiPoint A h₂ h₃ hA)
  change height A H ≠ 0 at hHeight
  have h₂M : (2 : M) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K M)).mpr h₂
  have h₃M : (3 : M) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K M)).mpr h₃
  have h₂R : (2 : RatFunc K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (RatFunc K))).mpr h₂
  have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂M h₃M
    ((map_ne_zero (algebraMap K M)).mpr hA)
  have hTarget : ∃ (t v : M) (htv : (Curve (algebraMap K M A)).Nonsingular t v),
      H.val = .some t v htv ∧ Transcendental K t := by
    cases he : H.val with
    | zero =>
      have h0 : H = 0 := Subtype.ext he
      exact (hHeight (by rw [h0, height_zero])).elim
    | some t v htv =>
      have hInv : (Affine.Point.some t v htv : Points A) ∈ antiInvariant A :=
        he ▸ H.property
      have hH : H = ⟨.some t v htv, hInv⟩ := Subtype.ext he
      exact ⟨t, v, htv, rfl, transcendental_of_height_ne_zero h₂ hInv (hH ▸ hHeight)⟩
  obtain ⟨t, v, htv, he, ht⟩ := hTarget
  have hInv : (Affine.Point.some t v htv : Points A) ∈ antiInvariant A := he ▸ H.property
  obtain ⟨r, hr⟩ := exists_algebraMap_of_fixed h₂R (abscissa_fixed A hInv)
  let f := fiberPolynomial r t
  have hF : f ≠ 0 := fiberPolynomial_ne_zero r t ht
  have hRep : H.val.xRep = ![algebraMap (RatFunc K) M r, 1] := by
    rw [he, hr] <;> rfl
  have hHr := CubicRationalPointHeight.height_eq_of_xRep A H r hRep
  have hR : (Curve (algebraMap K M A)).Nonsingular (algebraMap (RatFunc K) M r) v :=
    hr.symm ▸ htv
  have hG : D.atField M Q = .some (algebraMap (RatFunc K) M r) v hR := by
    have hd : D.atField M Q = .some t v htv := he
    rw [hd, Affine.Point.some.injEq]
    exact ⟨hr.symm, rfl⟩
  let b := pointsMap A (IsScalarTower.toAlgHom K K M)
  let P (g : T) := b (i g).val + Q
  have hP : Function.Injective P := by
    intro x y h
    exact hi (Subtype.ext ((pointsMap_injective A (IsScalarTower.toAlgHom K K M))
      (add_right_cancel h)))
  have hRoots (g : T) :
      ∃ (x y : M) (hxy : (Curve (algebraMap K M A)).Nonsingular x y),
        P g = .some x y hxy ∧ f.IsRoot x := by
    obtain ⟨x, y, hxy, he', hx⟩ := translate_affine h₂ h₃ hA (i g).val
    change P g = .some x y hxy at he'
    have hImage : D.atField M (P g) = .some t v htv := by
      change D.atField M (b (i g).val + Q) = _
      rw [map_add, ← D.commute, show D.atField K (i g).val = 0 from (i g).property, map_zero, zero_add]
      exact he
    rw [he'] at hImage
    have hRoot := isRoot_of_image D h₂ h₃ hA r hG hΔ hxy htv hx hImage
    exact ⟨x, y, hxy, he', hRoot⟩
  have hB := CubicAffineFiberBound.card_le_of_root_abscissas hΔ hF P hP hRoots
  rw [hHr]
  exact hB.trans (Nat.mul_le_mul_left _ (natDegree_fiberPolynomial_le r t))

/-- The entire geometric kernel satisfies the same degree bound. -/
theorem card_kernel_le (D : Family K A)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hHeight : height A (antiInvariantApply D (genericAntiPoint A h₂ h₃ hA)) ≠ 0) :
    Nat.card ↥(D.atField K).ker ≤
      2 * height A (antiInvariantApply D (genericAntiPoint A h₂ h₃ hA)) :=
  card_of_injection_le D h₂ h₃ hA hHeight id Function.injective_id

end

end ManuscriptAudit.CubicNaturalKernelDegree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CubicNaturalKernelDegree.card_of_injection_le,
      ``ManuscriptAudit.CubicNaturalKernelDegree.card_kernel_le] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
