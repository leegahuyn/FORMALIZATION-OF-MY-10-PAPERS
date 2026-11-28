import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Etale.Basic

/-! The actual base-change extension on affine rings commutes with
both a map of stages and a map of the corresponding relative charts. -/

namespace ManuscriptAudit.AffineStageTensorExtensionMaps

open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B M N D E : Type u}
  [CommRing A] [CommRing B] [CommRing M] [CommRing N] [CommRing D] [CommRing E]
  [Algebra A B] [Algebra A M] [Algebra A N] [Algebra A D] [Algebra A E]
  [Algebra B D] [Algebra B E] [IsScalarTower A B D] [IsScalarTower A B E]

/-- Extend the given actual stage-to-chart map to a relative B-algebra map. -/
def extend (f : M →ₐ[A] D) : B ⊗[A] M →ₐ[B] D :=
  Algebra.TensorProduct.lift (Algebra.ofId B D) f (fun _ _ ↦ Commute.all _ _)

/-- The compatible base change of an actual map of stages. -/
def extendMap (f : M →ₐ[A] N) : B ⊗[A] M →ₐ[B] B ⊗[A] N :=
  Algebra.TensorProduct.map (AlgHom.id B B) f

/-- Extending along B commutes with composition in the absolute stage. -/
theorem extend_comp (f : M →ₐ[A] N) (g : N →ₐ[A] D) :
    (extend g).comp (extendMap (B := B) f) = extend (g.comp f) := by
  apply Algebra.TensorProduct.ext'
  intro b m
  rfl

/-- The extension behaves naturally under the actual relative
maps on the chart, in particular under either tensor-square inclusion. -/
theorem postcomp_extend (f : M →ₐ[A] D) (g : D →ₐ[B] E) :
    g.comp (extend f) = extend ((g.restrictScalars A).comp f) := by
  apply Algebra.TensorProduct.ext'
  intro b m
  change g (algebraMap B D b * f m) = algebraMap B E b * g (f m)
  rw [map_mul, g.commutes]

/-- The comparison with the original absolute chart map is literally
the right tensor inclusion. -/
theorem extend_includeRight (f : M →ₐ[A] D) :
    ((extend (B := B) f).restrictScalars A).comp Algebra.TensorProduct.includeRight = f :=
  Algebra.TensorProduct.lift_comp_includeRight (Algebra.ofId B D) f (fun _ _ ↦ Commute.all _ _)

end
end ManuscriptAudit.AffineStageTensorExtensionMaps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineStageTensorExtensionMaps.extend_comp,
      ``ManuscriptAudit.AffineStageTensorExtensionMaps.postcomp_extend,
      ``ManuscriptAudit.AffineStageTensorExtensionMaps.extend_includeRight] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
