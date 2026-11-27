import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusModFourArithmetic

/-! The exact residue of both coefficients on the actual two-adic Tate module. -/

namespace ManuscriptAudit.CubicTwoAdicResidueArithmetic

open CubicNonsplitThreeAdicTrace CubicSplitTwoPowerFrobenius CubicDoublingSurjective
open CubicSplitExtensionTraceRecurrence PowerTateModule PowerTateCoefficientReduction

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [Algebra K L] [IsAlgClosed L] [DecidableEq L]

/-- Reduction of the actual two-adic Tate trace and determinant gives the
arithmetic coefficients modulo four. -/
theorem trace_det_mod_four {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) :
    let G := GeometricPoints K L A
    let F := endMap 2 (arithmeticPointFrobenius K L A)
    PadicInt.toZModPow 2 (LinearMap.trace ℤ_[2] (Tate 2 G) F) = (signedTrace A : ZMod 4) ∧
      PadicInt.toZModPow 2 (LinearMap.det F) = (Fintype.card K : ZMod 4) := by
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hAL : algebraMap K L A ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  let G := GeometricPoints K L A
  let B := CubicTwoPowerTorsionBasis.affineBasis h₂L h₃L hAL 1
  have hDiv : Function.Surjective (fun P : G => (2 : ℕ) • P) :=
    affine_doubling_surjective h₂L h₃L hAL
  exact ⟨(trace_det_reduce 2 G B hDiv (arithmeticPointFrobenius K L A) 2).1.trans
      (CubicFrobeniusModFourArithmetic.trace_eq_signed_count K L h₂ h₃ hA),
    CubicFrobeniusDeterminantModFour.adic_determinant_mod_four K L h₂ h₃ hA⟩

end
end ManuscriptAudit.CubicTwoAdicResidueArithmetic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicTwoAdicResidueArithmetic.trace_det_mod_four
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
