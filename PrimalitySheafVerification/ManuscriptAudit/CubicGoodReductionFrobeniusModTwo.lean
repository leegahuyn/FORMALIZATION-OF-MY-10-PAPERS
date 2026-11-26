import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeneralTwoTorsionCard
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusModTwoRecurrence
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace

/-!
# Frobenius modulo two for nonsingular short cubics

The geometric representation is the actual two-torsion of the base-changed
cubic. The signed trace input is the actual projective point count over the
prime field. The two coefficients of the resulting characteristic polynomial
are the respective reductions of the point trace and the prime.
-/

namespace ManuscriptAudit.CubicGoodReductionFrobeniusModTwo

open Polynomial FiniteFieldPointCount WeierstrassFrobeniusTwoTorsionTrace

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

private abbrev baseAffine (c A : ZMod p) := (shortCubic c A).toProjective.toAffine

private theorem shortCubic_baseChange (c A : ZMod p) :
    (shortCubic c A).baseChange L =
      shortCubic (algebraMap (ZMod p) L c) (algebraMap (ZMod p) L A) := by
  simp [shortCubic, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem geometricTwoTorsion_card (hpTwo : p ≠ 2) {c A : ZMod p}
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    Nat.card (geometricTwoTorsion p L (baseAffine p c A)) = 4 := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  have h₂ : (2 : L) ≠ 0 := by
    have hpMin := (Fact.out : p.Prime).two_le
    have hNat : ((2 : ℕ) : L) ≠ 0 :=
      (CharP.cast_eq_zero_iff L p 2).not.mpr <| fun hd => by
        have hle := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) hd
        omega
    simpa only [Nat.cast_ofNat] using hNat
  have hΔL : ((shortCubic c A).baseChange L).Δ ≠ 0 := by
    change ((shortCubic c A).map (algebraMap (ZMod p) L)).Δ ≠ 0
    rw [WeierstrassCurve.map_Δ]
    exact (map_ne_zero (algebraMap (ZMod p) L)).mpr hΔ
  rw [shortCubic_baseChange p L] at hΔL
  rw [Nat.card_congr (TwoTorsionFrobeniusModule.carrierEquiv _)]
  change Nat.card {P : (((shortCubic c A).baseChange L).toProjective.toAffine).Point //
    2 • P = 0} = 4
  rw [shortCubic_baseChange p L]
  exact CubicGeneralTwoTorsionCard.affineTwoTorsion_card h₂ hΔL

def actualFrobenius (hpTwo : p ≠ 2) {c A : ZMod p} (hΔ : (shortCubic c A).Δ ≠ 0) :
    geometricTwoTorsion p L (baseAffine p c A) ≃ₗ[ZMod 2]
      geometricTwoTorsion p L (baseAffine p c A) :=
  frobeniusOfCardFour p L _ (geometricTwoTorsion_card p L hpTwo hΔ)

def arithmeticTrace (c A : ZMod p) : ℤ :=
  (p : ℤ) + 1 - (Nat.card (shortCubic c A).toProjective.Point : ℤ)

theorem actualFrobenius_trace (hpTwo : p ≠ 2) {c A : ZMod p}
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    LinearMap.trace (ZMod 2) (geometricTwoTorsion p L (baseAffine p c A))
      (actualFrobenius p L hpTwo hΔ).toLinearMap = (arithmeticTrace p c A : ZMod 2) := by
  simpa only [actualFrobenius, arithmeticTrace, Int.cast_sub, Int.cast_add, Int.cast_natCast,
    Int.cast_one] using
    (trace_eq_signed_projective_count p L (shortCubic c A).toProjective
      (geometricTwoTorsion_card p L hpTwo hΔ) hpTwo)

theorem actualFrobenius_det (hpTwo : p ≠ 2) {c A : ZMod p}
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    LinearMap.det (actualFrobenius p L hpTwo hΔ).toLinearMap = (p : ZMod 2) :=
  det_eq_prime_cast p L _ (geometricTwoTorsion_card p L hpTwo hΔ) hpTwo

private theorem finiteModule (hpTwo : p ≠ 2) {c A : ZMod p}
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    Module.Finite (ZMod 2) (geometricTwoTorsion p L (baseAffine p c A)) := by
  have h := geometricTwoTorsion_card p L hpTwo hΔ
  letI : Finite (geometricTwoTorsion p L (baseAffine p c A)) :=
    Nat.finite_of_card_ne_zero (by rw [h]; decide)
  infer_instance

theorem actualFrobenius_charpoly (hpTwo : p ≠ 2) {c A : ZMod p}
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    letI := finiteModule p L hpTwo hΔ
    (actualFrobenius p L hpTwo hΔ).toLinearMap.charpoly =
      X ^ 2 - C (arithmeticTrace p c A : ZMod 2) * X + C (p : ZMod 2) := by
  let V := geometricTwoTorsion p L (baseAffine p c A)
  have hcard : Nat.card V = 4 := geometricTwoTorsion_card p L hpTwo hΔ
  letI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let b : Module.Basis (Fin 2) (ZMod 2) V :=
    FrobeniusModTwoLinear.basisOfCardFour _ hcard
  letI : Module.Finite (ZMod 2) V := finiteModule p L hpTwo hΔ
  have hp : (p : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr ((Fact.out : p.Prime).odd_of_ne_two hpTwo)
  rw [FrobeniusModTwoRecurrence.linear_characteristic_polynomial V b,
    actualFrobenius_trace p L hpTwo hΔ, hp, map_one]

end
end ManuscriptAudit.CubicGoodReductionFrobeniusModTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicGoodReductionFrobeniusModTwo.geometricTwoTorsion_card,
      ``ManuscriptAudit.CubicGoodReductionFrobeniusModTwo.actualFrobenius_trace,
      ``ManuscriptAudit.CubicGoodReductionFrobeniusModTwo.actualFrobenius_det,
      ``ManuscriptAudit.CubicGoodReductionFrobeniusModTwo.actualFrobenius_charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
