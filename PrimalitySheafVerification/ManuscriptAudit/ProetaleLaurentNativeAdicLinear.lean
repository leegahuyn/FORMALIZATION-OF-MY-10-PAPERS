import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicResidueScalar
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentNativeAdicHOne

/-! The actual native Laurent comparison is linear for the native
continuous-coefficient scalar action. -/

namespace ManuscriptAudit.ProetaleLaurentNativeAdicLinear

open AlgebraicGeometry CategoryTheory
open ProetaleLaurentCompatibleHOne (laurent)
open ProetaleLaurentNativeAdicHOne (adicEquiv adicEquiv_inverse_reduction)
open ProetaleLaurentAdicCoordinates (compatibleEquiv_apply levelEquiv)
open ProetaleAdicHOneDetection (reductionMap reductionMap_injective compatibleHOne)
open NativeAdicScalarAction (adicModule scalarMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := laurent K
private abbrev rho (n : ℕ) :=
  (ProetaleCoefficientUniverseLift.lift (X K)).map (ProetaleResidueSheaves.residueReduction (X K) ℓ n)

local instance : Module ℤ_[ℓ] ((X K).EllAdicCohomology ℓ 1) := adicModule (X K) ℓ 1

private theorem reduction_coordinate (a : ℤ_[ℓ]) (n : ℕ) :
    Sheaf.H.map (rho K ℓ n) 1 ((adicEquiv K ℓ).symm a) =
      levelEquiv K ℓ n (PadicInt.toZModPow n a) :=
  (congrArg (fun t : compatibleHOne (X K) ℓ ↦ t.val n) (adicEquiv_inverse_reduction K ℓ a)).trans
    (compatibleEquiv_apply K ℓ a n)

set_option maxHeartbeats 1600000 in
theorem coordinate_smul (r a : ℤ_[ℓ]) :
    (adicEquiv K ℓ).symm (r • a) = r • (adicEquiv K ℓ).symm a := by
  apply reductionMap_injective (X K) ℓ
  apply Subtype.ext
  funext n
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (show ℓ.Prime from Fact.out).ne_zero⟩
  change Sheaf.H.map (rho K ℓ n) 1 ((adicEquiv K ℓ).symm (r * a)) =
    Sheaf.H.map (rho K ℓ n) 1 (Sheaf.H.map (scalarMap (X K) ℓ r) 1 ((adicEquiv K ℓ).symm a))
  calc
    _ = levelEquiv K ℓ n (PadicInt.toZModPow n (r * a)) := reduction_coordinate K ℓ (r * a) n
    _ = (PadicInt.toZModPow n r).val • levelEquiv K ℓ n (PadicInt.toZModPow n a) := by
      rw [← map_nsmul, map_mul]
      apply congrArg (levelEquiv K ℓ n)
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    _ = (PadicInt.toZModPow n r).val • Sheaf.H.map (rho K ℓ n) 1 ((adicEquiv K ℓ).symm a) :=
      congrArg (fun z ↦ (PadicInt.toZModPow n r).val • z) (reduction_coordinate K ℓ a n).symm
    _ = _ := (NativeAdicResidueScalar.reduction_scalar (X K) ℓ 1 n r ((adicEquiv K ℓ).symm a)).symm

/-- The actual native integral Laurent group is a free adic module of rank one. -/
def adicLinearEquiv : ℤ_[ℓ] ≃ₗ[ℤ_[ℓ]] ((X K).EllAdicCohomology ℓ 1) where
  toAddEquiv := (adicEquiv K ℓ).symm
  map_smul' := coordinate_smul K ℓ

end
end ManuscriptAudit.ProetaleLaurentNativeAdicLinear

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleLaurentNativeAdicLinear.adicLinearEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
