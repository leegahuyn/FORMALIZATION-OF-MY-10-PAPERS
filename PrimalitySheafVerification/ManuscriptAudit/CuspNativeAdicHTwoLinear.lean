import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoReductionDetection
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoReduction
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicResidueScalar

/-! The actual native Laurent boundary is linear for the integral adic
scalar action. Its scalar formula is detected in each finite residue. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoLinear

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp)
open CuspNativeAdicHTwoLower (adicInclusion)
open CuspNativeAdicHTwoReduction (residueInclusion reduction_adicInclusion)
open CuspNativeAdicHTwoReductionDetection (reduction_injective)
open ProetaleAdicReductionAllDegrees (reductionMap)
open NativeAdicScalarAction (adicModule scalarMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveCusp K

set_option maxHeartbeats 1100000 in
theorem adicInclusion_map_mul (r a : ℤ_[ℓ]) :
    adicInclusion K ℓ (r * a) =
      Sheaf.H.map (scalarMap (X K) ℓ r) 2 (adicInclusion K ℓ a) := by
  apply reduction_injective K ℓ
  apply Subtype.ext
  funext n
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : Nat.Prime ℓ).ne_zero⟩
  let m := (PadicInt.toZModPow n r).val
  have hr : PadicInt.toZModPow n (r * a) = m • PadicInt.toZModPow n a := by
    rw [map_mul, nsmul_eq_mul]
    exact congrArg (fun z : ZMod (ℓ ^ n) ↦ z * PadicInt.toZModPow n a)
      (ZMod.natCast_zmod_val (PadicInt.toZModPow n r)).symm
  calc
    _ = residueInclusion K ℓ n (PadicInt.toZModPow n (r * a)) :=
      reduction_adicInclusion K ℓ (r * a) n
    _ = residueInclusion K ℓ n (m • PadicInt.toZModPow n a) := congrArg (residueInclusion K ℓ n) hr
    _ = m • residueInclusion K ℓ n (PadicInt.toZModPow n a) := map_nsmul _ _ _
    _ = m • (reductionMap (X K) ℓ 2 (adicInclusion K ℓ a)).val n :=
      congrArg (fun z ↦ m • z) (reduction_adicInclusion K ℓ a n).symm
    _ = _ := (NativeAdicResidueScalar.reduction_scalar (X K) ℓ 2 n r (adicInclusion K ℓ a)).symm

local instance : Module ℤ_[ℓ] ((X K).EllAdicCohomology ℓ 2) := adicModule (X K) ℓ 2

/-- The exhibited native degree-two Laurent line is an adic linear inclusion. -/
def adicLinearInclusion : ℤ_[ℓ] →ₗ[ℤ_[ℓ]] ((X K).EllAdicCohomology ℓ 2) where
  toAddHom := adicInclusion K ℓ
  map_smul' := adicInclusion_map_mul K ℓ

theorem adicLinearInclusion_injective : Function.Injective (adicLinearInclusion K ℓ) :=
  CuspNativeAdicHTwoLower.adicInclusion_injective K ℓ

end

end ManuscriptAudit.CuspNativeAdicHTwoLinear

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoLinear.adicInclusion_map_mul,
      ``ManuscriptAudit.CuspNativeAdicHTwoLinear.adicLinearInclusion,
      ``ManuscriptAudit.CuspNativeAdicHTwoLinear.adicLinearInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
