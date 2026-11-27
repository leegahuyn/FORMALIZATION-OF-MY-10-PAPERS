import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousCoefficientNaturality

/-! The actual native cohomology comparison under a scheme
isomorphism commutes with continuous coefficient homomorphisms. -/

namespace ManuscriptAudit.SchemeIsoProetaleCohomologyNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open SchemeIsoProetaleSheaves (sheafEquivalence integersIso functionsIso)
open SchemeIsoProetaleCohomology (continuousCohomologyEquiv)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleContinuousCoefficientNaturality (map)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{0}} (e : X ≅ Y)

private abbrev A := AddCommGrpCat.{1}
private abbrev C (T : Scheme.{0}) := Sheaf (Scheme.ProEt.topology T) A
private abbrev F : C X ⥤ C Y := (sheafEquivalence e).functor

local instance : (F e).Additive := (F e).additive_of_preserves_binary_products

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [TopologicalSpace M] [TopologicalSpace N] [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
variable (f : M →+ N) (hf : Continuous f)

private theorem functionsIso_natural :
    (F e).map (map f hf X) ≫ (functionsIso e N).hom =
      (functionsIso e M).hom ≫ map f hf Y := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  exact ContinuousMap.ext (fun _ ↦ rfl)

private theorem continuousCohomologyEquiv_apply (n : ℕ) (x : Sheaf.H (functions M X) n) :
    continuousCohomologyEquiv e M n x =
      ((Ext.mk₀ (integersIso e).inv).comp (x.mapExactFunctor (F e)) (zero_add n)).comp
        (Ext.mk₀ (functionsIso e M).hom) (add_zero n) := rfl

/-- Actual scheme-isomorphism transport commutes with the native
cohomology arrow induced by a continuous coefficient homomorphism. -/
theorem continuousCohomologyEquiv_map (n : ℕ) (x : Sheaf.H (functions M X) n) :
    continuousCohomologyEquiv e N n (Sheaf.H.map (map f hf X) n x) =
      Sheaf.H.map (map f hf Y) n (continuousCohomologyEquiv e M n x) := by
  simp only [continuousCohomologyEquiv_apply, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, functionsIso_natural]

end
end ManuscriptAudit.SchemeIsoProetaleCohomologyNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SchemeIsoProetaleCohomologyNaturality.continuousCohomologyEquiv_map
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
