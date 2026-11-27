import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RadicalRotationFixed

/-! The two primitive coordinate rotations on the actual double radical algebra. -/

namespace ManuscriptAudit.DoubleRadicalRotation

open Polynomial RadicalCoordinateAlgebra RadicalRotationFixed

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] [Nontrivial R]

variable (m n : ℕ) (a b : R)

local notation "C₀" => Extension m a
local notation "D₀" => DoubleExtension m n a b

private def onFirstAlgebra (z : K) (hz : z ^ m = 1) : C₀ →ₐ[R] D₀ :=
  (IsScalarTower.toAlgHom R C₀ D₀).comp (rotation m a z hz)

def rotateFirst (z : K) (hz : z ^ m = 1) : D₀ →ₐ[R] D₀ :=
  AdjoinRoot.liftAlgHom (relation n (algebraMap R C₀ b)) (onFirstAlgebra m n a b z hz)
    (secondRoot m n a b) (by
      simp only [relation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [(onFirstAlgebra m n a b z hz).commutes, secondRoot_pow, sub_self])

def rotateSecond (z : K) (hz : z ^ n = 1) : D₀ →ₐ[R] D₀ :=
  (rotation n (algebraMap R C₀ b) z hz).restrictScalars R

@[simp] theorem rotateFirst_of (z : K) (hz : z ^ m = 1) (x : C₀) :
    rotateFirst m n a b z hz (algebraMap C₀ D₀ x) =
      algebraMap C₀ D₀ (rotation m a z hz x) := by
  unfold rotateFirst
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of] <;> rfl

@[simp] theorem rotateFirst_firstRoot (z : K) (hz : z ^ m = 1) :
    rotateFirst m n a b z hz (firstRoot m n a b) =
      algebraMap K D₀ z * firstRoot m n a b := by
  unfold firstRoot
  rw [rotateFirst_of, rotation_root, map_mul, ← IsScalarTower.algebraMap_apply K C₀ D₀]

@[simp] theorem rotateFirst_secondRoot (z : K) (hz : z ^ m = 1) :
    rotateFirst m n a b z hz (secondRoot m n a b) = secondRoot m n a b := by
  unfold rotateFirst secondRoot root
  rw [AdjoinRoot.liftAlgHom_root]

@[simp] theorem rotateSecond_firstRoot (z : K) (hz : z ^ n = 1) :
    rotateSecond m n a b z hz (firstRoot m n a b) = firstRoot m n a b := by
  change rotation n (algebraMap R C₀ b) z hz (algebraMap C₀ D₀ (root m a)) = _
  exact (rotation n (algebraMap R C₀ b) z hz).commutes (root m a)

@[simp] theorem rotateSecond_secondRoot (z : K) (hz : z ^ n = 1) :
    rotateSecond m n a b z hz (secondRoot m n a b) =
      algebraMap K D₀ z * secondRoot m n a b :=
  rotation_root n (algebraMap R C₀ b) z hz

/-- Invariance under the two primitive rotations implies actual descent to the base ring. -/
theorem exists_base_of_fixed (hm : m ≠ 0) (hn : n ≠ 0)
    {z w : K} (hz : IsPrimitiveRoot z m) (hw : IsPrimitiveRoot w n) (t : D₀)
    (hU : rotateFirst m n a b z hz.pow_eq_one t = t)
    (hV : rotateSecond m n a b w hw.pow_eq_one t = t) :
    ∃ f : R, algebraMap R D₀ f = t := by
  letI : Nontrivial C₀ := (algebraMap_injective m a hm).nontrivial
  have hV' : rotation n (algebraMap R C₀ b) w hw.pow_eq_one t = t := hV
  obtain ⟨c, hc⟩ := exists_scalar_of_fixed n (algebraMap R C₀ b) hn w hw t hV'
  have hRot := congrArg (rotateFirst m n a b z hz.pow_eq_one) hc
  rw [rotateFirst_of, hU] at hRot
  have hC : rotation m a z hz.pow_eq_one c = c :=
    (algebraMap_injective n (algebraMap R C₀ b) hn) (hRot.trans hc.symm)
  obtain ⟨f, hf⟩ := exists_scalar_of_fixed m a hm z hz c hC
  exact ⟨f, (IsScalarTower.algebraMap_apply R C₀ D₀ f).trans
    ((congrArg (algebraMap C₀ D₀) hf).trans hc)⟩

end
end ManuscriptAudit.DoubleRadicalRotation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.DoubleRadicalRotation.rotateFirst_firstRoot,
      ``ManuscriptAudit.DoubleRadicalRotation.rotateFirst_secondRoot,
      ``ManuscriptAudit.DoubleRadicalRotation.rotateSecond_firstRoot,
      ``ManuscriptAudit.DoubleRadicalRotation.rotateSecond_secondRoot,
      ``ManuscriptAudit.DoubleRadicalRotation.exists_base_of_fixed] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
