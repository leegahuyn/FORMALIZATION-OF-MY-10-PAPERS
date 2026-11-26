import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionQuotient

/-!
# The canonical quotient map to the geometric skyscraper

At a geometric point between the two opens, the quotient stalk
determines a map from the actual cokernel to the geometric skyscraper
by the native point adjunction.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

private abbrev C := AddCommGrpCat.{u}

variable {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j] (M : C.{u})
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)

private abbrev coefficient :=
  (Scheme.pointSmallEtale s).sheafFiber.obj ((constantSheaf U.smallEtaleTopology C.{u}).obj M)

/-- The adjoint of the quotient stalk comparison at a geometric point of the difference. -/
def nestedOpenQuotientToSkyscraper (hs : ¬ ∃ t : Spec (.of Ω) ⟶ V, t ≫ i = s) :
    cokernel (nestedOpenConstantMap i j M) ⟶
      (Scheme.pointSmallEtale (s ≫ j)).skyscraperSheaf (coefficient M s) :=
  ((Scheme.pointSmallEtale (s ≫ j)).skyscraperSheafAdjunction.homEquiv _ _)
    (nestedOpenQuotientStalkIso i j M s hs).hom

/-- The canonical composite to the skyscraper kills the nested-open inclusion. -/
theorem nestedOpenConstantMap_comp_toSkyscraper
    (hs : ¬ ∃ t : Spec (.of Ω) ⟶ V, t ≫ i = s) :
    nestedOpenConstantMap i j M ≫ cokernel.π (nestedOpenConstantMap i j M) ≫
      nestedOpenQuotientToSkyscraper i j M s hs = 0 := by
  rw [← Category.assoc, cokernel.condition, zero_comp]

/-- Applying the geometric stalk and then the point adjunction counit recovers
the stalk isomorphism used to construct the map. -/
theorem nestedOpenQuotientToSkyscraper_stalk_comp_counit
    (hs : ¬ ∃ t : Spec (.of Ω) ⟶ V, t ≫ i = s) :
    (Scheme.pointSmallEtale (s ≫ j)).sheafFiber.map (nestedOpenQuotientToSkyscraper i j M s hs) ≫
      (Scheme.pointSmallEtale (s ≫ j)).skyscraperSheafAdjunction.counit.app (coefficient M s) =
    (nestedOpenQuotientStalkIso i j M s hs).hom := by
  let a := (Scheme.pointSmallEtale (s ≫ j)).skyscraperSheafAdjunction (A := C.{u})
  rw [← a.homEquiv_counit] <;> exact (a.homEquiv _ _).symm_apply_apply _

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotientToSkyscraper,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenConstantMap_comp_toSkyscraper,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotientToSkyscraper_stalk_comp_counit] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
