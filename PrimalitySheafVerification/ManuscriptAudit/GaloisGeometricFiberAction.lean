import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.GaloisCoverAction

/-!
# Geometric fibers of finite Galois covers are free right actions

The automorphisms of a finite Galois field cover act on its geometric
fiber. Equality of two translates cancels after passing to the
injective field map attached to the geometric point. The construction
also applies after postcomposing the cover with any étale field chart.
-/

namespace ManuscriptAudit.GaloisGeometricFiberAction

open AlgebraicGeometry CategoryTheory
open EtaleObjectRestriction FieldEtaleGaloisCovers GaloisCoverAction

noncomputable section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [IsSepClosed Ω]
variable (x : Spec (CommRingCat.of Ω) ⟶ X)
variable (F L : Type) [Field F] [Field L] [Algebra F L] [Module.Finite F L] [IsGalois F L]
variable (j : Spec (CommRingCat.of F) ⟶ X) [Etale j]

/-- The native geometric fiber over the Galois cover of the étale field chart. -/
abbrev fiber :=
  (Scheme.pointSmallEtale x).fiber.obj ((postcompose j).obj (galoisObject F L))

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition with Galois automorphisms defines a right group action
on the actual geometric fiber. -/
def rightAction : MulAction (L ≃ₐ[F] L)ᵐᵒᵖ (fiber x F L j) where
  smul σ t := (Scheme.pointSmallEtale x).fiber.map
    ((postcompose j).map (automorphism F L (MulOpposite.unop σ))) t
  one_smul t := by
    change (Scheme.pointSmallEtale x).fiber.map
      ((postcompose j).map (automorphism F L 1)) t = t
    rw [automorphism_one, Functor.map_id, Functor.map_id] <;> rfl
  mul_smul σ τ t := by
    change (Scheme.pointSmallEtale x).fiber.map
      ((postcompose j).map (automorphism F L (MulOpposite.unop τ * MulOpposite.unop σ))) t =
        (Scheme.pointSmallEtale x).fiber.map
          ((postcompose j).map (automorphism F L (MulOpposite.unop σ)))
          ((Scheme.pointSmallEtale x).fiber.map
            ((postcompose j).map (automorphism F L (MulOpposite.unop τ))) t)
    rw [automorphism_mul, Functor.map_comp, Functor.map_comp] <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The right action on each geometric fiber is free, by injectivity
of maps from the field of the cover into the geometric field. -/
theorem rightAction_free (t : fiber x F L j) :
    letI := rightAction x F L j
    Function.Injective (fun σ : L ≃ₐ[F] L ↦ MulOpposite.op σ • t) := by
  intro σ τ h
  have e := congrArg (fun z : fiber x F L j ↦ z.left) h
  change t.left ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) =
    t.left ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) at e
  have hRing := congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of L) ↦
    Spec.preimage f) e
  simp only [Spec.preimage_comp, Spec.preimage_map] at hRing
  apply AlgEquiv.ext
  intro a
  apply (Spec.preimage t.left).hom.injective
  exact congrArg (fun f : CommRingCat.of L ⟶ CommRingCat.of Ω ↦ f a) hRing

end

end ManuscriptAudit.GaloisGeometricFiberAction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.GaloisGeometricFiberAction.rightAction_free
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
