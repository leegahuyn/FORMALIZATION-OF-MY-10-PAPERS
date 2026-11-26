import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoTorsionCard
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualHasseWeil
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace

/-!
# Frobenius on the actual geometric two-torsion of the good printed family

For the reductions with coefficient parameter p_n = p, the trace on the
native geometric two-torsion is the signed arithmetic point count modulo two.
The determinant on the same representation is the reduction of p.
-/

namespace ManuscriptAudit.Paper5FrobeniusModTwo

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open WeierstrassCurve CubicGeometricTorsion CubicTwoTorsionCard
open WeierstrassFrobeniusTwoTorsionTrace Paper5ActualHasseWeil

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

abbrev printedAffine (A : ZMod p) := (paper5TraceCurve p A).toProjective.toAffine

theorem geometricTwoTorsion_card (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    Nat.card (geometricTwoTorsion p L (printedAffine p A)) = 4 := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  have hsmall (n : ℕ) (h₀ : 0 < n) (hn : n < p) : (n : L) ≠ 0 :=
    (CharP.cast_eq_zero_iff L p n).not.mpr
      (fun h => (Nat.not_le_of_lt hn) (Nat.le_of_dvd h₀ h))
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 2 (by decide) (by omega)
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 3 (by decide) (by omega)
  have ha : algebraMap (ZMod p) L A ≠ 0 :=
    (map_ne_zero (algebraMap (ZMod p) L)).mpr hA
  have hΔ := CubicFiniteTorsion.shortCubic_zero_discriminant_ne_zero p hp ha
  rw [Nat.card_congr (TwoTorsionFrobeniusModule.carrierEquiv _)]
  change Nat.card {P : (((paper5TraceCurve p A).baseChange L).toProjective.toAffine).Point //
    2 • P = 0} = 4
  rw [printed_cubic_baseChange_eq_zero]
  exact affineTwoTorsion_card h₂ h₃ ha hΔ

def actualFrobenius (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    geometricTwoTorsion p L (printedAffine p A) ≃ₗ[ZMod 2]
      geometricTwoTorsion p L (printedAffine p A) :=
  frobeniusOfCardFour p L _ (geometricTwoTorsion_card p L hp hA)

theorem actualFrobenius_trace (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    LinearMap.trace (ZMod 2) (geometricTwoTorsion p L (printedAffine p A))
      (actualFrobenius p L hp hA).toLinearMap = (firstTrace p A : ZMod 2) := by
  simpa only [actualFrobenius, firstTrace, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
    using trace_eq_signed_projective_count p L (paper5TraceCurve p A).toProjective
      (geometricTwoTorsion_card p L hp hA) (by omega)

theorem actualFrobenius_det (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    LinearMap.det (actualFrobenius p L hp hA).toLinearMap = (p : ZMod 2) :=
  det_eq_prime_cast p L _ (geometricTwoTorsion_card p L hp hA) (by omega)

end
end ManuscriptAudit.Paper5FrobeniusModTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.Paper5FrobeniusModTwo.geometricTwoTorsion_card,
      ``ManuscriptAudit.Paper5FrobeniusModTwo.actualFrobenius_trace,
      ``ManuscriptAudit.Paper5FrobeniusModTwo.actualFrobenius_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
