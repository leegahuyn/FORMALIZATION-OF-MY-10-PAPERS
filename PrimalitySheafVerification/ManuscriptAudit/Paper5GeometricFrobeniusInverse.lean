import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.Padics.PadicIntegers
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly

/-! The inverse of the native arithmetic generator on the rational Tate module has reciprocal determinant. -/

namespace ManuscriptAudit.Paper5GeometricFrobeniusInverse

open PowerTateModule CubicNonsplitThreeAdicTrace CubicNonsplitPrimeAdicFrobenius
open CubicNonsplitTwoThreeAdicCharpoly
open scoped TensorProduct

noncomputable section

private theorem determinant_baseChange {R S V : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup V] [Module R V]
    (b : Basis (Fin 2) R V) (f : Module.End R V) :
    LinearMap.det (f.baseChange S) = algebraMap R S (LinearMap.det f) := by
  let b' := Algebra.TensorProduct.basis S b
  rw [← LinearMap.det_toMatrix b', ← LinearMap.det_toMatrix b, RingHom.map_det]
  congr 1
  ext i j
  simp [b']

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L]
    [IsAlgClosed L] [DecidableEq L]

abbrev RationalTate (A : E) := ℚ_[2] ⊗[ℤ_[2]] Tate 2 (GeometricPoints E L A)

def arithmetic (A : E) : Module.End ℚ_[2] (RationalTate E L A) :=
  (Action E L 2 A).baseChange ℚ_[2]

theorem arithmetic_det {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq : Fintype.card E % 3 = 2) :
    LinearMap.det (arithmetic E L A) = (Fintype.card E : ℚ_[2]) := by
  rw [arithmetic, determinant_baseChange (twoAdicBasis E L h₂ h₃ hA),
    two_adic_determinant E L h₂ h₃ hA hq, map_natCast]

def arithmeticEquiv {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq : Fintype.card E % 3 = 2) :
    RationalTate E L A ≃ₗ[ℚ_[2]] RationalTate E L A := by
  let b := Algebra.TensorProduct.basis ℚ_[2] (twoAdicBasis E L h₂ h₃ hA)
  letI : Module.Finite ℚ_[2] (RationalTate E L A) := Module.Finite.of_basis b
  apply LinearMap.equivOfDetNeZero (arithmetic E L A)
  rw [arithmetic_det E L h₂ h₃ hA hq]
  exact_mod_cast (Fintype.card_pos.ne' : Fintype.card E ≠ 0)

theorem arithmeticEquiv_toLinearMap {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq : Fintype.card E % 3 = 2) :
    (arithmeticEquiv E L h₂ h₃ hA hq).toLinearMap = arithmetic E L A := rfl

/-- On the covariant Tate module, the inverse generator acts by the inverse linear equivalence. -/
def inverseGenerator {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq : Fintype.card E % 3 = 2) :
    Module.End ℚ_[2] (RationalTate E L A) :=
  (arithmeticEquiv E L h₂ h₃ hA hq).symm.toLinearMap

theorem inverse_det {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq : Fintype.card E % 3 = 2) :
    LinearMap.det (inverseGenerator E L h₂ h₃ hA hq) = (Fintype.card E : ℚ_[2])⁻¹ := by
  rw [inverseGenerator, LinearEquiv.det_coe_symm, arithmeticEquiv_toLinearMap,
    arithmetic_det E L h₂ h₃ hA hq]

end

section Five

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 5) L] [IsAlgClosed L] [DecidableEq L]

theorem literal_inverse_det_ne_five :
    LinearMap.det (inverseGenerator (ZMod 5) L (A := 1) (by decide) (by decide)
      one_ne_zero (by rw [ZMod.card]; decide)) ≠ (5 : ℚ_[2]) := by
  rw [inverse_det, ZMod.card]
  norm_num

end Five
end ManuscriptAudit.Paper5GeometricFrobeniusInverse

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5GeometricFrobeniusInverse.arithmetic_det,
      ``ManuscriptAudit.Paper5GeometricFrobeniusInverse.arithmeticEquiv_toLinearMap,
      ``ManuscriptAudit.Paper5GeometricFrobeniusInverse.inverse_det,
      ``ManuscriptAudit.Paper5GeometricFrobeniusInverse.literal_inverse_det_ne_five] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
