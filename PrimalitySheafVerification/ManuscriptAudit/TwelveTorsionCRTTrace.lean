import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import PrimalitySheafVerification.ManuscriptAudit.TwelveTorsionCRTBasis

/-! Native trace and determinant reduce naturally along the actual twelve-torsion CRT. -/

namespace ManuscriptAudit.TwelveTorsionCRTTrace

open Module TorsionFrobeniusModule TwelveTorsionCRTBasis

noncomputable section

variable (G : Type*) [AddCommGroup G]
variable (B₄ : Basis (Fin 2) (ZMod 4) (Torsion 4 G))
variable (B₃ : Basis (Fin 2) (ZMod 3) (Torsion 3 G))
variable (f : AddMonoid.End G)

local notation "B" => basis G B₄ B₃

theorem matrix_reduce_four :
    reduceFour.mapMatrix (LinearMap.toMatrix B B (mapLinear 12 f)) =
      LinearMap.toMatrix B₄ B₄ (mapLinear 4 f) := by
  ext i j
  change reduceFour ((LinearMap.toMatrix B B (mapLinear 12 f)) i j) = _
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, repr_reduce_four G B₄ B₃]
  change B₄.repr (TwelveTorsionCRT.equivalence G (mapAdd 12 f (B j))).1 i =
    B₄.repr (mapAdd 4 f (B₄ j)) i
  rw [TwelveTorsionCRT.natural G f, basis_components G B₄ B₃]

theorem matrix_reduce_three :
    reduceThree.mapMatrix (LinearMap.toMatrix B B (mapLinear 12 f)) =
      LinearMap.toMatrix B₃ B₃ (mapLinear 3 f) := by
  ext i j
  change reduceThree ((LinearMap.toMatrix B B (mapLinear 12 f)) i j) = _
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, repr_reduce_three G B₄ B₃]
  change B₃.repr (TwelveTorsionCRT.equivalence G (mapAdd 12 f (B j))).2 i =
    B₃.repr (mapAdd 3 f (B₃ j)) i
  rw [TwelveTorsionCRT.natural G f, basis_components G B₄ B₃]

include B₄ B₃ in
theorem trace_det_reduce_four :
    reduceFour (LinearMap.trace (ZMod 12) (Torsion 12 G) (mapLinear 12 f)) =
      LinearMap.trace (ZMod 4) (Torsion 4 G) (mapLinear 4 f) ∧
    reduceFour (LinearMap.det (mapLinear 12 f)) = LinearMap.det (mapLinear 4 f) := by
  let D := basis G B₄ B₃
  constructor
  · rw [LinearMap.trace_eq_matrix_trace (ZMod 12) D,
      LinearMap.trace_eq_matrix_trace (ZMod 4) B₄, AddMonoidHom.map_trace]
    exact congrArg Matrix.trace (matrix_reduce_four G B₄ B₃ f)
  · rw [← LinearMap.det_toMatrix D, reduceFour.map_det, matrix_reduce_four G B₄ B₃ f,
      LinearMap.det_toMatrix B₄]

include B₄ B₃ in
theorem trace_det_reduce_three :
    reduceThree (LinearMap.trace (ZMod 12) (Torsion 12 G) (mapLinear 12 f)) =
      LinearMap.trace (ZMod 3) (Torsion 3 G) (mapLinear 3 f) ∧
    reduceThree (LinearMap.det (mapLinear 12 f)) = LinearMap.det (mapLinear 3 f) := by
  let D := basis G B₄ B₃
  constructor
  · rw [LinearMap.trace_eq_matrix_trace (ZMod 12) D,
      LinearMap.trace_eq_matrix_trace (ZMod 3) B₃, AddMonoidHom.map_trace]
    exact congrArg Matrix.trace (matrix_reduce_three G B₄ B₃ f)
  · rw [← LinearMap.det_toMatrix D, reduceThree.map_det, matrix_reduce_three G B₄ B₃ f,
      LinearMap.det_toMatrix B₃]

end
end ManuscriptAudit.TwelveTorsionCRTTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwelveTorsionCRTTrace.trace_det_reduce_four,
      ``ManuscriptAudit.TwelveTorsionCRTTrace.trace_det_reduce_three] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
