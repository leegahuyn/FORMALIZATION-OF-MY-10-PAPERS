import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitPrimeTateCoefficients
import PrimalitySheafVerification.ManuscriptAudit.CubicTwistTateDeterminant
import PrimalitySheafVerification.ManuscriptAudit.RankTwoTraceOfDeterminant

/-! Actual ordinary Frobenius coefficients over all finite extension fields and all nonzero twists. -/

namespace ManuscriptAudit.CubicOrdinaryTwistTateCoefficients

open Polynomial Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicSupersingularUnitFrobenius CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace
open PowerTateModule PowerTateRankTwo CubicFrobeniusTranscendentalRelation
open Paper5NonsplitFrobeniusModFour
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (E L : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E]
  [Field L] [DecidableEq L] [Algebra E L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable (l : ℕ) [Fact l.Prime]

/-- Genuine rank-two basis on any good centered cubic over the algebraic closure. -/
def centeredBasis {a : L} (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0) (ha : a ≠ 0)
    (hl : l = 2 ∨ l = 3) : Basis (Fin 2) ℤ_[l] (Tate l (Curve a).Point) := by
  rcases hl with rfl | rfl
  · let B := CubicTwoPowerTorsionBasis.affineBasis h₂ h₃ ha 1
    let hs := CubicDoublingSurjective.affine_doubling_surjective h₂ h₃ ha
    exact (Basis.finTwoProd ℤ_[2]).map (padicPairEquiv 2 (Curve a).Point B hs)
  · exact (Basis.finTwoProd ℤ_[3]).map (CubicThreeAdicTate.affinePadicCoordinates h₂ h₃ ha)

private theorem unit_det_aux (K : Type*) [Field K] [Fintype K] [Algebra K L]
    (V : WeierstrassCurve.Affine L) (hV : (Curve (1 : K)).baseChange L = V) (h : V = Curve (1 : L)) :
    LinearMap.det (endMap l (pointMapAt K L (Curve (1 : K)) V hV
      (FiniteField.frobeniusAlgHom K L))) = LinearMap.det (endMap l (arithmeticUnit K L)) := by
  subst V
  rfl

/-- Unit-twist Frobenius on E has determinant the actual field size. -/
theorem unit_det (hp : 5 ≤ p) (hs : p % 3 = 1) (hl : l = 2 ∨ l = 3) :
    LinearMap.det (endMap l (arithmeticUnit E L)) = (Fintype.card E : ℤ_[l]) := by
  have hPrime := (CubicSplitPrimeTateCoefficients.trace_det p L hp hs
    (one_ne_zero : (1 : ZMod p) ≠ 0) l hl).2
  have hV := unit_det_aux L l (ZMod p) (Curve (algebraMap (ZMod p) L (1 : ZMod p)))
    (centered_baseChange (ZMod p) L 1) (congrArg Curve (map_one (algebraMap (ZMod p) L)))
  change LinearMap.det (CubicSplitPrimeTateCoefficients.native p L (1 : ZMod p) l) =
    LinearMap.det (endMap l (arithmeticUnit (ZMod p) L)) at hV
  have hDet : LinearMap.det (endMap l (arithmeticUnit (ZMod p) L)) = (p : ℤ_[l]) :=
    hV.symm.trans hPrime
  rw [arithmeticUnit_eq_prime_pow E L p, map_pow, map_pow, hDet,
    Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, Nat.cast_pow]

/-- On every finite ordinary extension, every actual twist has determinant #E. -/
theorem det_arithmetic (hp : 5 ≤ p) (hs : p % 3 = 1) (hl : l = 2 ∨ l = 3)
    {A : E} (hA : A ≠ 0) :
    LinearMap.det (endMap l (arithmeticPointFrobenius E L A)) = (Fintype.card E : ℤ_[l]) := by
  obtain ⟨h₂, h₃⟩ := small_char p L hp
  let B := centeredBasis L l h₂ h₃ (one_ne_zero : (1 : L) ≠ 0) hl
  rw [CubicTwistTateDeterminant.determinant_eq_unit E L l hl h₂ h₃ B hA]
  exact unit_det p E L l hp hs hl

/-- The exact signed point-count trace and determinant for every nonzero twist over E. -/
theorem trace_det (hp : 5 ≤ p) (hs : p % 3 = 1) (hl : l = 2 ∨ l = 3)
    {A : E} (hA : A ≠ 0) :
    let F := endMap l (arithmeticPointFrobenius E L A)
    LinearMap.trace ℤ_[l] _ F = (arithmeticTrace E A : ℤ_[l]) ∧
      LinearMap.det F = (Fintype.card E : ℤ_[l]) := by
  obtain ⟨h₂, h₃⟩ := small_char p E hp
  obtain ⟨h₂L, h₃L⟩ := small_char p L hp
  have hchar : ringChar E ≠ 2 := by
    intro h
    exact h₂ ((ringChar.spec E 2).mpr (by simpa only [h] using (dvd_rfl : (2 : ℕ) ∣ 2)))
  have h := CubicFrobeniusCharacteristicAllPoints.characteristic_relation E L h₂ h₃ hchar hA
  have he := congrArg (endMap l) h
  simp only [characteristicError, map_pow, map_sub, map_add, map_zsmul, map_one, map_zero] at he
  let F := endMap l (arithmeticPointFrobenius E L A)
  have hQuad : F ^ 2 - (arithmeticTrace E A : ℤ_[l]) • F +
      (Fintype.card E : ℤ_[l]) • (1 : Module.End ℤ_[l] (Tate l (GeometricPoints E L A))) = 0 := by
    rw [Int.cast_smul_eq_zsmul, ← Int.cast_natCast, Int.cast_smul_eq_zsmul]
    exact he
  have hD : LinearMap.det F = (Fintype.card E : ℤ_[l]) := det_arithmetic p E L l hp hs hl hA
  have hNZ : (Fintype.card E : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  let B := centeredBasis L l h₂L h₃L ((map_ne_zero (algebraMap E L)).mpr hA) hl
  exact ⟨RankTwoTraceOfDeterminant.trace_eq B F _ _ hNZ hD hQuad, hD⟩

/-- Full characteristic polynomial of the actual Frobenius, even for a twist defined only over E. -/
theorem charpoly (hp : 5 ≤ p) (hs : p % 3 = 1) (hl : l = 2 ∨ l = 3)
    {A : E} (hA : A ≠ 0) :
    let hL := small_char p L hp
    let B := centeredBasis L l hL.1 hL.2 ((map_ne_zero (algebraMap E L)).mpr hA) hl
    letI : Module.Free ℤ_[l] (Tate l (GeometricPoints E L A)) := Module.Free.of_basis B
    letI : Module.Finite ℤ_[l] (Tate l (GeometricPoints E L A)) := Module.Finite.of_basis B
    (endMap l (arithmeticPointFrobenius E L A)).charpoly =
      X ^ 2 - C (arithmeticTrace E A : ℤ_[l]) * X + C (Fintype.card E : ℤ_[l]) := by
  let hL := small_char p L hp
  let B := centeredBasis L l hL.1 hL.2 ((map_ne_zero (algebraMap E L)).mpr hA) hl
  letI : Module.Free ℤ_[l] (Tate l (GeometricPoints E L A)) := Module.Free.of_basis B
  letI : Module.Finite ℤ_[l] (Tate l (GeometricPoints E L A)) := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det p E L l hp hs hl hA
  dsimp only at ht hd ⊢
  rw [← LinearMap.charpoly_toMatrix _ B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

end

end ManuscriptAudit.CubicOrdinaryTwistTateCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicOrdinaryTwistTateCoefficients.centeredBasis,
      ``ManuscriptAudit.CubicOrdinaryTwistTateCoefficients.unit_det,
      ``ManuscriptAudit.CubicOrdinaryTwistTateCoefficients.det_arithmetic,
      ``ManuscriptAudit.CubicOrdinaryTwistTateCoefficients.trace_det,
      ``ManuscriptAudit.CubicOrdinaryTwistTateCoefficients.charpoly] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
