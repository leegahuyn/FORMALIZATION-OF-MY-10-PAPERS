import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericFunctionField

/-! The generic centered cubic specializes to every affine point with transcendental abscissa. -/

namespace ManuscriptAudit.CubicGenericSpecialization

open CubicGenericFunctionField

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Evaluation of K(X) at a transcendental element in a field extension. -/
def rationalAt (x : L) (hx : Transcendental K x) : RatFunc K →ₐ[K] L :=
  (IntermediateField.adjoin K ({x} : Set L)).val.comp
    (RatFunc.algEquivOfTranscendental x hx).toAlgHom

theorem rationalAt_X (x : L) (hx : Transcendental K x) :
    rationalAt x hx RatFunc.X = x := by
  exact RatFunc.algEquivOfTranscendental_X x hx

/-- The function field has a K-algebra map to every transcendental affine solution. -/
theorem exists_specialization (A : K) (x y : L) (hx : Transcendental K x)
    (hy : y ^ 2 = x ^ 3 + algebraMap K L A) :
    ∃ f : Model A →ₐ[K] L, f (genericX A) = x ∧ f (genericY A) = y := by
  let e := rationalAt x hx
  letI : Algebra (RatFunc K) L := e.toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) L := IsScalarTower.of_algebraMap_eq (fun c => (e.commutes c).symm)
  have hX : e RatFunc.X = x := rationalAt_X x hx
  have hA : e (RatFunc.C A) = algebraMap K L A := e.commutes A
  have hYP : y * y = radicand A • (1 : L) + (0 : RatFunc K) • y := by
    change y * y = e (radicand A) * 1 + e 0 * y
    rw [map_zero, zero_mul, add_zero, mul_one, ← pow_two, radicand, map_add, map_pow, hX, hA]
    exact hy
  let f : Model A →ₐ[RatFunc K] L := QuadraticAlgebra.lift ⟨y, hYP⟩
  refine ⟨f.restrictScalars K, ?_, ?_⟩
  · change f (algebraMap (RatFunc K) (Model A) RatFunc.X) = x
    exact (f.commutes RatFunc.X).trans hX
  · change (genericY A).re • (1 : L) + (genericY A).im • y = y
    simp [genericY]

end

end ManuscriptAudit.CubicGenericSpecialization

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericSpecialization.rationalAt_X,
      ``ManuscriptAudit.CubicGenericSpecialization.exists_specialization] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
