import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5TwoAdicCoefficients
import PrimalitySheafVerification.ManuscriptAudit.PowerTateRankTwo

/-! Prime-adic trace and determinant specialize to the actual finite-level point operators. -/

namespace ManuscriptAudit.PowerTateCoefficientReduction

open TorsionFrobeniusModule PowerTorsionTower PowerTateModule PowerTateRankTwo
open PowerTorsionCompatibleBasis Paper5TwoAdicCoefficients

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]
variable (B : Module.Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l G 1))
variable (h : Function.Surjective (fun P : G => l • P))

local notation "padicBasis" => padicPairEquiv l G B h
local notation "finiteBasis" => levelEquiv l G B (Nat.Prime.pos (Fact.out : Nat.Prime l)) h

def coordinateAction (f : AddMonoid.End G) : Module.End ℤ_[l] (ℤ_[l] × ℤ_[l]) :=
  (padicBasis).symm.conj (endMap l f)

def finiteCoordinateAction (f : AddMonoid.End G) (n : ℕ) :
    Module.End (ZMod (l ^ n)) (ZMod (l ^ n) × ZMod (l ^ n)) :=
  (finiteBasis n).symm.conj (mapLinear (l ^ n) f)

theorem reduction_action (f : AddMonoid.End G) (n : ℕ) (a : ℤ_[l] × ℤ_[l]) :
    mapPair (PadicInt.toZModPow n) (coordinateAction l G B h f a) =
      finiteCoordinateAction l G B h f n (mapPair (PadicInt.toZModPow n) a) := by
  have hP : padicBasis (coordinateAction l G B h f a) = endMap l f (padicBasis a) := by
    change padicBasis ((padicBasis).symm (endMap l f (padicBasis a))) = _
    exact (padicBasis).apply_symm_apply _
  have hN (b : ZMod (l ^ n) × ZMod (l ^ n)) :
      finiteBasis n (finiteCoordinateAction l G B h f n b) =
        mapLinear (l ^ n) f (finiteBasis n b) := by
    change finiteBasis n ((finiteBasis n).symm (mapLinear (l ^ n) f (finiteBasis n b))) = _
    exact (finiteBasis n).apply_symm_apply _
  apply (finiteBasis n).injective
  rw [hN]
  have he := congrArg (evaluate l G n) hP
  simp only [evaluate_padicPairEquiv, evaluate_endMap] at he
  exact he

include B h

theorem trace_det_reduce (f : AddMonoid.End G) (n : ℕ) :
    PadicInt.toZModPow n (LinearMap.trace ℤ_[l] (Tate l G) (endMap l f)) =
      LinearMap.trace (ZMod (l ^ n)) (PowerTorsion l G n) (mapLinear (l ^ n) f) ∧
    PadicInt.toZModPow n (LinearMap.det (endMap l f)) =
      LinearMap.det (mapLinear (l ^ n) f) := by
  have hh := map_trace_det (PadicInt.toZModPow n)
    (coordinateAction l G B h f) (finiteCoordinateAction l G B h f n)
    (reduction_action l G B h f n)
  have hp : LinearMap.det (coordinateAction l G B h f) = LinearMap.det (endMap l f) :=
    LinearMap.det_conj _ (padicBasis).symm
  have hn : LinearMap.det (finiteCoordinateAction l G B h f n) =
      LinearMap.det (mapLinear (l ^ n) f) :=
    LinearMap.det_conj _ (finiteBasis n).symm
  exact ⟨by simpa only [coordinateAction, finiteCoordinateAction, LinearMap.trace_conj'] using hh.1,
    by simpa only [hp, hn] using hh.2⟩

theorem determinant_eq_of_reductions (f : AddMonoid.End G) (d : ℤ_[l])
    (hd : ∀ n, PadicInt.toZModPow n d = LinearMap.det (mapLinear (l ^ n) f)) :
    LinearMap.det (endMap l f) = d :=
  PadicInt.ext_of_toZModPow.mp fun n => (trace_det_reduce l G B h f n).2.trans (hd n).symm

end
end ManuscriptAudit.PowerTateCoefficientReduction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTateCoefficientReduction.reduction_action,
      ``ManuscriptAudit.PowerTateCoefficientReduction.trace_det_reduce,
      ``ManuscriptAudit.PowerTateCoefficientReduction.determinant_eq_of_reductions] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
