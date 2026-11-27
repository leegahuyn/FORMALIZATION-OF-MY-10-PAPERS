import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationModFourKernel
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitTwoPowerFrobenius
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools

/-! The exact mod-four fixed-point alternatives apply to native split centered Frobenius. -/

namespace ManuscriptAudit.CubicSplitFrobeniusModFourPatterns

open WeierstrassCurve CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace
open CubicRotationModFourKernel CubicSplitTwoPowerFrobenius TorsionFrobeniusModule

noncomputable section

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L]
  [IsAlgClosed L] [DecidableEq L]

private theorem pointMapAt_injective (W : Affine E) (V : Affine L) (hW : W.baseChange L = V)
    (g : L →ₐ[E] L) : Function.Injective (pointMapAt E L W V hW g) := by
  subst V
  change Function.Injective (Affine.Point.map (W' := W) g)
  exact Affine.Point.map_injective (W' := W) g

/-- The actual mod-four module in a cyclic basis of its rational cube rotation. -/
theorem exists_native_rotation_form {A z : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3) :
    let F := levelFrobenius E L A 2
    let S := levelRotation E L h₂ h₃ hA hz 2
    ∃ B : Module.Basis (Fin 2) (ZMod 4) (Level E L A 2),
      S (B 0) = B 1 ∧ S (B 1) = -B 0 - B 1 ∧
        ∃ a b : ZMod 4, F = a • 1 + b • S := by
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃
  have hAL : algebraMap E L A ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  have hzL := hz.map_of_injective (algebraMap E L).injective
  let S := levelRotation E L h₂ h₃ hA hz 2
  obtain ⟨B, hB⟩ := CubicRotationCyclicBasis.exists_rotation_basis
    h₂L h₃L hAL hzL.pow_eq_one (hzL.ne_one (by decide)) 1
  have h₀ : S (B 0) = B 1 := hB
  have h₁ : S (B 1) = -B 0 - B 1 := by
    have h := CubicRotationCyclicBasis.rotation_linear_quad
      h₂L h₃L hAL hzL.pow_eq_one (hzL.ne_one (by decide)) 2 (B 0)
    change S (S (B 0)) = -B 0 - S (B 0) at h
    rwa [h₀] at h
  obtain ⟨ab, hab, _⟩ := level_form E L h₂ h₃ hA hz 1
  exact ⟨B, h₀, h₁, ab.1, ab.2, hab⟩

/-- The actual cubed arithmetic Frobenius and its negative have the exact 16/4 or 4/4
possibilities on geometric four-torsion. -/
theorem native_cube_fixed_patterns {A z : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3) :
    CubeFixedPatterns (levelFrobenius E L A 2) := by
  let F := levelFrobenius E L A 2
  let S := levelRotation E L h₂ h₃ hA hz 2
  obtain ⟨B, h₀, h₁, a, b, hab⟩ := exists_native_rotation_form E L h₂ h₃ hA hz
  letI : Finite (Level E L A 2) := Finite.of_injective _ B.equivFun.injective
  have hF : Function.Injective F :=
    mapLinear_injective 4 _ (pointMapAt_injective E L _ _ _ _)
  let e := LinearEquiv.ofBijective F hF.bijective_of_finite
  have hDet : LinearMap.det F = 1 ∨ LinearMap.det F = 3 :=
    FourTorsionDeterminantTools.determinant_cases e
  exact cube_fixed_patterns B S F h₀ h₁ a b hab hDet

end
end ManuscriptAudit.CubicSplitFrobeniusModFourPatterns

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitFrobeniusModFourPatterns.native_cube_fixed_patterns
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
