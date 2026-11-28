import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! A morphism between actual weakly étale affine charts has a
faithfully flat map at every corresponding pair of prime local rings. -/

namespace ManuscriptAudit.WeaklyEtaleStageStalkInjection

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap specMap specMap_structureMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A C)]

/-- Pullback of an affine stage to an actual weakly étale affine
chart detects equality in the local ring at the image point. -/
theorem localRingHom_injective (g : C →ₐ[A] B)
    (q : Ideal C) [q.IsPrime] (r : Ideal B) [r.IsPrime] (hq : q = r.comap g.toRingHom) :
    Function.Injective (Localization.localRingHom q r g.toRingHom hq) := by
  let φ := CommRingCat.ofHom g.toRingHom
  let p := specMap A g
  have hComp : WeaklyEtale (p ≫ structureMap A C) := by
    rw [specMap_structureMap]
    infer_instance
  letI : WeaklyEtale (p ≫ structureMap A C) := hComp
  letI : WeaklyEtale p := WeaklyEtale.of_comp p (structureMap A C)
  letI : Algebra C B := g.toRingHom.toAlgebra
  letI : Module.Flat C B :=
    (RingHom.flat_algebraMap_iff).mp ((Flat.SpecMap_iff (f := φ)).mp (inferInstanceAs (Flat p)))
  letI : r.LiesOver q := ⟨hq⟩
  letI := Localization.AtPrime.algebraOfLiesOver q r
  let S := Localization.AtPrime q
  let T := Localization.AtPrime r
  letI : IsLocalHom (algebraMap S T) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q r g.toRingHom hq))
  letI : Module.FaithfullyFlat S T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective S T

end
end ManuscriptAudit.WeaklyEtaleStageStalkInjection

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleStageStalkInjection.localRingHom_injective
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
