import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import PrimalitySheafVerification.ManuscriptAudit.FreeActionFunctionCohomology
import PrimalitySheafVerification.ManuscriptAudit.GaloisGeometricFiberAction

/-!
# Galois cohomology of the sections of a geometric skyscraper

At a finite Galois cover of an étale field chart, the geometric
skyscraper has function sections on the geometric fiber, with the
geometric right Galois action. That action is free.
-/

namespace ManuscriptAudit.GaloisSkyscraperSectionCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleObjectRestriction FieldEtaleGaloisCovers GaloisCoverAction
open FreeActionFunctionCohomology GaloisGeometricFiberAction

noncomputable section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [IsSepClosed Ω]
variable (x : Spec (CommRingCat.of Ω) ⟶ X)
variable (F L : Type) [Field F] [Field L] [Algebra F L] [Module.Finite F L] [IsGalois F L]
variable (j : Spec (CommRingCat.of F) ⟶ X) [Etale j]
variable (M : AddCommGrpCat.{0})

private abbrev restrictedSkyscraper :=
  (restriction j).obj ((Scheme.pointSmallEtale x).skyscraperSheaf M)

set_option backward.isDefEq.respectTransparency false in
private def sectionsEquiv :
    (restrictedSkyscraper x F j M).obj.obj (op (galoisObject F L)) ≃ₗ[ℤ]
      (fiber x F L j → M) := by
  let A : fiber x F L j → AddCommGrpCat.{0} := fun _ ↦ M
  let e : ((∏ᶜ A : AddCommGrpCat.{0}) : Type) ≃+ (fiber x F L j → M) :=
    { toEquiv := Concrete.productEquiv A
      map_add' := by
        intro a b
        funext t
        simp only [Concrete.productEquiv_apply_apply, Pi.add_apply, map_add] }
  exact e.toIntLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The native section representation is the function representation
on the geometric fiber with the actual Galois action. -/
def sectionsRepIso :
    letI := rightAction x F L j
    sectionsRep F L (restrictedSkyscraper x F j M) ≅
      actionFunctions ℤ (L ≃ₐ[F] L) (fiber x F L j) M := by
  letI := rightAction x F L j
  refine Rep.mkIso <| .mk (sectionsEquiv x F L j M) (fun σ ↦ ?_)
  apply LinearMap.ext
  intro a
  funext t
  let A : fiber x F L j → AddCommGrpCat.{0} := fun _ ↦ M
  let p : fiber x F L j → fiber x F L j :=
    (Scheme.pointSmallEtale x).fiber.map ((postcompose j).map (automorphism F L σ))
  let h : (∏ᶜ A : AddCommGrpCat.{0}) ⟶ (∏ᶜ A) := Pi.map' p (fun _ ↦ 𝟙 M)
  change Concrete.productEquiv A (h a) t = Concrete.productEquiv A a (p t)
  rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
    ← ConcreteCategory.comp_apply]
  change (Pi.map' p (fun _ ↦ 𝟙 M) ≫ Pi.π A t) a = Pi.π A (p t) a
  rw [Pi.map'_comp_π, Category.comp_id]

/-- All positive group cohomology of geometric skyscraper sections vanishes
on any finite Galois field cover of an étale field chart. -/
theorem sections_H_succ_isZero (n : ℕ) :
    IsZero (groupCohomology (sectionsRep F L (restrictedSkyscraper x F j M)) (n + 1)) := by
  letI := rightAction x F L j
  exact (actionFunctions_H_succ_isZero ℤ (L ≃ₐ[F] L) (fiber x F L j) M
    (rightAction_free x F L j) n).of_iso <|
    (groupCohomology.functor ℤ (L ≃ₐ[F] L) (n + 1)).mapIso (sectionsRepIso x F L j M)

end

end ManuscriptAudit.GaloisSkyscraperSectionCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisSkyscraperSectionCohomology.sectionsRepIso,
      ``ManuscriptAudit.GaloisSkyscraperSectionCohomology.sections_H_succ_isZero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
