import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusTranscendentalRelation
import PrimalitySheafVerification.ManuscriptAudit.CubicAlgebraicAbscissaDescent
import PrimalitySheafVerification.ManuscriptAudit.CubicDoublingSurjective

/-! The arithmetic characteristic polynomial annihilates actual relative Frobenius on all geometric points. -/

namespace ManuscriptAudit.CubicFrobeniusCharacteristicAllPoints

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace
open CubicGenericFunctionField CubicGenericAntiInvariant
open CubicFrobeniusTranscendentalRelation CubicNativePointBaseChange
open CubicAlgebraicAbscissaDescent

noncomputable section
open scoped Classical

variable (K L : Type*) [Field K] [Fintype K] [Field L] [IsAlgClosed L]
  [DecidableEq L] [Algebra K L]

private theorem pointsMap_characteristicError {M : Type*} [Field M] [DecidableEq M] [Algebra K M]
    (A : K) (f : L →ₐ[K] M) (P : GeometricPoints K L A) :
    pointsMap A f (characteristicError K L A P) = characteristicError K M A (pointsMap A f P) := by
  rw [characteristicError_apply, characteristicError_apply]
  simp only [map_add, map_sub, map_zsmul, map_arithmeticFrobenius]

/-- Translate by a generic point to transfer the two-torsion error identity to every geometric point. -/
theorem double_characteristicError {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hchar : ringChar K ≠ 2)
    {A : K} (hA : A ≠ 0) (P : GeometricPoints K L A) :
    (2 : ℕ) • characteristicError K L A P = 0 := by
  let a := algebraMap K L A
  let M := Model a
  letI : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  let f := IsScalarTower.toAlgHom K L M
  let b := pointsMap A f
  have h₂' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃' : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hA' : a ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  let Q : GeometricPoints K M A := genericPoint a h₂' h₃' hA'
  have hQ : ∃ h, Q = .some (genericX a) (genericY a) h := ⟨_, rfl⟩
  have hTrans : Transcendental L (genericX a) :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc L) M).injective).mpr RatFunc.transcendental_X
  have hOutside : Q ∉ Set.range b := by
    rintro ⟨R, hR⟩
    obtain ⟨hP, he⟩ := hQ
    cases R with
    | zero =>
      have hZ : (0 : GeometricPoints K M A) = Q := (map_zero b).symm.trans hR
      rw [he] at hZ
      cases hZ
    | some x y hxy =>
      obtain ⟨h', hMap⟩ := pointsMap_some A f x y hxy
      change pointsMap A f (.some x y hxy) = Q at hR
      rw [hMap, he, Affine.Point.some.injEq] at hR
      have hx : algebraMap L M x = genericX a := hR.1
      exact hTrans (hx ▸ isAlgebraic_algebraMap (A := M) x)
  have hOutsideSum : b P + Q ∉ Set.range b := by
    rintro ⟨R, he⟩
    apply hOutside
    refine ⟨R - P, ?_⟩
    rw [map_sub, he]
    abel
  have hOutsideError (R : GeometricPoints K M A) (hR : R ∉ Set.range b) :
      (2 : ℕ) • characteristicError K M A R = 0 := by
    cases R with
    | zero => simp
    | some x y hxy =>
      have hx : Transcendental L x := fun hAlg => hR
        (in_range_of_isAlgebraic A h₂ h₃ hA hxy hAlg)
      exact characteristicError_transcendental K M hq hk h₂ h₃ hchar hA hxy
        (Transcendental.of_tower_top K hx)
  have hQError := hOutsideError Q hOutside
  have hSumError := hOutsideError (b P + Q) hOutsideSum
  have hErrImage : (2 : ℕ) • characteristicError K M A (b P) = 0 := by
    simpa only [map_add, nsmul_add, hQError, add_zero] using hSumError
  apply (pointsMap_injective A f)
  rw [map_nsmul, pointsMap_characteristicError, map_zero]
  exact hErrImage

/-- The literal arithmetic characteristic polynomial t²−a·t+q annihilates
relative Frobenius on the full geometric point group. -/
theorem characteristic_relation (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hchar : ringChar K ≠ 2) {A : K} (hA : A ≠ 0) :
    characteristicError K L A = 0 := by
  have hOdd := FiniteField.odd_card_of_char_ne_two hchar
  let k := Fintype.card K / 2
  have hq : Fintype.card K = 2 * k + 1 := by dsimp only [k]; omega
  have hk : 0 < k := Nat.div_pos Fintype.one_lt_card two_pos
  have h₂' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃' : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hA' := (map_ne_zero (algebraMap K L)).mpr hA
  apply AddMonoidHom.ext
  intro P
  obtain ⟨R, hR⟩ := CubicDoublingSurjective.affine_doubling_surjective h₂' h₃' hA' P
  change characteristicError K L A P = 0
  rw [← hR, map_nsmul]
  exact double_characteristicError K L hq hk h₂ h₃ hchar hA R

end

end ManuscriptAudit.CubicFrobeniusCharacteristicAllPoints

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicFrobeniusCharacteristicAllPoints.double_characteristicError,
      ``ManuscriptAudit.CubicFrobeniusCharacteristicAllPoints.characteristic_relation] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
