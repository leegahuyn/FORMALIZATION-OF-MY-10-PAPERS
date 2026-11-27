import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitTwoAdicTrace

/-! Modulo-four characteristic coefficients of the actual 2-adic Frobenius in the nonsplit family. -/

namespace ManuscriptAudit.Paper5NonsplitTwoAdicModFour

open Polynomial FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open Paper5TwoAdicCoefficients Paper5TwoPowerFrobenius
open TorsionFrobeniusModule TwoPowerTorsionCompatibleBasis TwoPowerTorsionCoordinateOperator
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L] [IsAlgClosed L]

private theorem printedAffine_eq (A : ZMod p) :
    Paper5FrobeniusModTwo.printedAffine p A = Curve A := by
  simp [Paper5FrobeniusModTwo.printedAffine, paper5TraceCurve, Curve, CubicAffine, shortCubic,
    ZMod.natCast_self]

/-- Actual 2-adic Frobenius determinant reduces to p in Z/4 for every prime p congruent to 2 mod 3. -/
theorem determinant_reduction_eq_prime (hp : 5 ≤ p) (hp3 : p % 3 = 2)
    {A : ZMod p} (hA : A ≠ 0) :
    PadicInt.toZModPow 2 (determinant p L hp hA) = (p : ZMod 4) := by
  rw [(reduction_trace_det p L hp hA 2).2]
  let e := compatibleLevelEquiv (GeometricPoints p L A)
    (geometricDoublingSurj p L hp hA) (geometricTwoTorsionCard p L hp hA) 2
  let f := mapLinear 4 (pointFrobenius p L A)
  change LinearMap.det (e.symm.conj f) = _
  have he : LinearMap.det (e.symm.conj f) = LinearMap.det f :=
    LinearMap.det_conj f e.symm
  rw [he]
  change LinearMap.det (frobeniusLinear 4 p L (Paper5FrobeniusModTwo.printedAffine p A)) = _
  rw [printedAffine_eq]
  exact Paper5NonsplitFrobeniusModFour.determinant_eq_prime p L hp hp3 hA

theorem coordinate_charpoly_eq (hp : 5 ≤ p) (hp3 : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    (coordinateFrobenius p L hp hA 2).toLinearMap.charpoly = X ^ 2 + C (p : ZMod 4) := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  let B := Module.Basis.finTwoProd (ZMod 4)
  let f := (coordinateFrobenius p L hp hA 2).toLinearMap
  have ht := (reduction_trace_det p L hp hA 2).1
  rw [Paper5NonsplitTwoAdicTrace.trace_eq_zero p L hp hA hp3, map_zero] at ht
  have hd : LinearMap.det f = (p : ZMod 4) :=
    (reduction_trace_det p L hp hA 2).2.symm.trans
      (determinant_reduction_eq_prime p L hp hp3 hA)
  change f.charpoly = _
  rw [← LinearMap.charpoly_toMatrix f B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod 4) B, LinearMap.det_toMatrix B,
    show LinearMap.trace (ZMod 4) (ZMod 4 × ZMod 4) f = 0 from ht.symm,
    hd, map_zero, zero_mul, sub_zero]

end
end ManuscriptAudit.Paper5NonsplitTwoAdicModFour

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5NonsplitTwoAdicModFour.determinant_reduction_eq_prime,
      ``ManuscriptAudit.Paper5NonsplitTwoAdicModFour.coordinate_charpoly_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
