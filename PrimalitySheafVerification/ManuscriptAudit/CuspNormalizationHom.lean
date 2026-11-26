import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Unramified.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspFlatUnramifiedSections

/-!
# Full faithfulness on affine cusp algebra maps

Base change along the normalization induces a bijection of algebra maps
from a formally unramified cusp algebra to a flat cusp algebra. In
particular this gives the map-level part of affine étale invariance.
-/

namespace ManuscriptAudit.CuspNormalizationHom

open Polynomial TensorProduct

noncomputable section

variable (K : Type*) [Field K]

private abbrev A := CuspPunctured.CuspSubalgebra K
private abbrev B := Polynomial K

variable (P T : Type*) [CommRing P] [CommRing T]
variable [Algebra (A K) P] [Algebra (A K) T]
variable [Algebra.FormallyUnramified (A K) P] [Module.Flat (A K) T]

private def swapHomEquiv :
    (P →ₐ[A K] T ⊗[A K] B K) ≃ (P →ₐ[A K] B K ⊗[A K] T) where
  toFun f := (Algebra.TensorProduct.comm (A K) T (B K)).toAlgHom.comp f
  invFun f := (Algebra.TensorProduct.comm (A K) T (B K)).symm.toAlgHom.comp f
  left_inv f := AlgHom.ext fun x => (Algebra.TensorProduct.comm (A K) T (B K)).symm_apply_apply (f x)
  right_inv f := AlgHom.ext fun x => (Algebra.TensorProduct.comm (A K) T (B K)).apply_symm_apply (f x)

/-- The natural map-level equivalence along the cusp normalization. -/
def homEquiv :
    (P →ₐ[A K] T) ≃ ((B K ⊗[A K] P) →ₐ[B K] (B K ⊗[A K] T)) :=
  (((Algebra.TensorProduct.liftEquivRight (A K) T P T).trans
    (CuspFlatUnramifiedSections.flatSectionsEquiv K T (P := T ⊗[A K] P))).trans
    (Algebra.TensorProduct.liftEquivRight (A K) T P (T ⊗[A K] B K)).symm).trans
      ((swapHomEquiv K P T).trans
        (Algebra.TensorProduct.liftEquivRight (A K) (B K) P (B K ⊗[A K] T)))

set_option backward.isDefEq.respectTransparency false in
/-- The forward map is actual scalar extension of an algebra homomorphism. -/
theorem homEquiv_apply (f : P →ₐ[A K] T) :
    homEquiv K P T f = Algebra.TensorProduct.map (AlgHom.id (B K) (B K)) f := by
  let eL := Algebra.TensorProduct.liftEquivRight (A K) T P T
  let eM := Algebra.TensorProduct.liftEquivRight (A K) T P (T ⊗[A K] B K)
  let eR := Algebra.TensorProduct.liftEquivRight (A K) (B K) P (B K ⊗[A K] T)
  let eN := CuspFlatUnramifiedSections.flatSectionsEquiv K T (P := T ⊗[A K] P)
  let e := Algebra.TensorProduct.comm (A K) T (B K)
  apply eR.symm.injective
  change eR.symm (eR (e.toAlgHom.comp (eM.symm (eN (eL f))))) =
    eR.symm (Algebra.TensorProduct.map (AlgHom.id (B K) (B K)) f)
  rw [Equiv.symm_apply_apply]
  apply AlgHom.ext
  intro p
  change e (eN (eL f) ((1 : T) ⊗ₜ[A K] p)) =
    Algebra.TensorProduct.map (AlgHom.id (B K) (B K)) f ((1 : B K) ⊗ₜ[A K] p)
  have hEval :
      eN (eL f) ((1 : T) ⊗ₜ[A K] p) = eL f ((1 : T) ⊗ₜ[A K] p) ⊗ₜ[A K] (1 : B K) :=
    CuspFlatUnramifiedSections.flatSectionsEquiv_apply K T (eL f) _
  have hLift : eL f ((1 : T) ⊗ₜ[A K] p) = f p := by
    change Algebra.TensorProduct.lift (Algebra.ofId T T) f (fun _ _ => .all _ _)
      ((1 : T) ⊗ₜ[A K] p) = f p
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rw [hEval, hLift, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- Scalar extension along the cusp normalization is bijective on these hom sets. -/
theorem baseChange_bijective :
    Function.Bijective
      (fun f : P →ₐ[A K] T => Algebra.TensorProduct.map (AlgHom.id (B K) (B K)) f) := by
  have h : (fun f : P →ₐ[A K] T => Algebra.TensorProduct.map (AlgHom.id (B K) (B K)) f) =
      (homEquiv K P T : (P →ₐ[A K] T) → _) := funext fun f => (homEquiv_apply K P T f).symm
  rw [h]
  exact (homEquiv K P T).bijective

end

end ManuscriptAudit.CuspNormalizationHom

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNormalizationHom.homEquiv_apply,
      ``ManuscriptAudit.CuspNormalizationHom.baseChange_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
