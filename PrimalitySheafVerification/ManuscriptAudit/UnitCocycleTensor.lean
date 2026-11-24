import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor identities for a unit descent cocycle

The transition unit lies in the actual double-overlap tensor-product
ring. The three pullbacks, diagonal, and module maps below are the
ones for extension and restriction of scalars, written explicitly on
tensor products.
-/

namespace ManuscriptAudit.UnitCocycleTensor

open TensorProduct

noncomputable section

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- Pull a double-overlap element to the first and second factors. -/
def pull12 : (B ⊗[R] B) →ₐ[B] (B ⊗[R] (B ⊗[R] B)) :=
  Algebra.TensorProduct.map (AlgHom.id B B)
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B)

/-- Pull a double-overlap element to the first and third factors. -/
def pull13 : (B ⊗[R] B) →ₐ[B] (B ⊗[R] (B ⊗[R] B)) :=
  Algebra.TensorProduct.map (AlgHom.id B B)
    (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B)

/-- Pull a double-overlap element to the second and third factors. -/
def pull23 : (B ⊗[R] B) →ₐ[R] (B ⊗[R] (B ⊗[R] B)) :=
  Algebra.TensorProduct.includeRight

/-- Restriction along the diagonal is multiplication. -/
def diagonal : (B ⊗[R] B) →ₐ[B] B :=
  Algebra.TensorProduct.lmul'' R

/-- The (B)-linear coaction on the free rank-one module, obtained by
multiplying the transition unit by the image of the scalar on the left. -/
def twistedCoaction (u : (B ⊗[R] B)ˣ) : B →ₗ[B] B ⊗[R] B where
  toFun b := b • (u : B ⊗[R] B)
  map_add' x y := add_smul x y _
  map_smul' c b := by
    change (c * b) • (u : B ⊗[R] B) = c • b • (u : B ⊗[R] B)
    exact mul_smul c b _

theorem twistedCoaction_apply (u : (B ⊗[R] B)ˣ) (b : B) :
    twistedCoaction R B u b = (b ⊗ₜ[R] (1 : B)) * (u : B ⊗[R] B) := by
  change b • (u : B ⊗[R] B) = _
  rw [Algebra.smul_def] <;> rfl

/-- Extend the coaction on the second tensor factor. -/
def tensorCoaction (u : (B ⊗[R] B)ˣ) :
    (B ⊗[R] B) →ₗ[B] (B ⊗[R] (B ⊗[R] B)) :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : B →ₗ[B] B)
    ((twistedCoaction R B u).restrictScalars R)

theorem pull13_tmul (a b : B) :
    pull13 R B (a ⊗ₜ[R] b) = a ⊗ₜ[R] ((1 : B) ⊗ₜ[R] b) := by
  simp only [pull13, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.includeRight_apply]

/-- On the double overlap, base change of the coaction multiplies
the first-two-factor pullback by the transition unit on factors two and three. -/
theorem tensorCoaction_apply (u : (B ⊗[R] B)ˣ) (z : B ⊗[R] B) :
    tensorCoaction R B u z = pull12 R B z * pull23 R B (u : B ⊗[R] B) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | tmul a b =>
    change a ⊗ₜ[R] (twistedCoaction R B u b) = _
    rw [twistedCoaction_apply]
    simp only [pull12, pull23, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]

/-- The diagonal normalization of a transition unit yields the counit identity. -/
theorem twistedCoaction_counit (u : (B ⊗[R] B)ˣ) (h : diagonal R B (u : B ⊗[R] B) = 1)
    (b : B) : diagonal R B (twistedCoaction R B u b) = b := by
  change diagonal R B (b • (u : B ⊗[R] B)) = b
  rw [map_smul, h, smul_eq_mul, mul_one]

/-- The usual triple-overlap unit cocycle law yields the coassociativity identity. -/
theorem twistedCoaction_coassoc (u : (B ⊗[R] B)ˣ)
    (h : pull12 R B (u : B ⊗[R] B) * pull23 R B (u : B ⊗[R] B) =
      pull13 R B (u : B ⊗[R] B)) (b : B) :
    tensorCoaction R B u (twistedCoaction R B u b) =
      pull13 R B (twistedCoaction R B u b) := by
  rw [tensorCoaction_apply]
  change pull12 R B (b • (u : B ⊗[R] B)) * pull23 R B (u : B ⊗[R] B) =
    pull13 R B (b • (u : B ⊗[R] B))
  simp only [map_smul, smul_mul_assoc, h]

end

end ManuscriptAudit.UnitCocycleTensor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.UnitCocycleTensor.twistedCoaction_apply,
      ``ManuscriptAudit.UnitCocycleTensor.pull13_tmul,
      ``ManuscriptAudit.UnitCocycleTensor.tensorCoaction_apply,
      ``ManuscriptAudit.UnitCocycleTensor.twistedCoaction_counit,
      ``ManuscriptAudit.UnitCocycleTensor.twistedCoaction_coassoc] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
