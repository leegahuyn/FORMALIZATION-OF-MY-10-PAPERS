import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphismLimits
import PrimalitySheafVerification.ManuscriptAudit.DensePointRestriction
import PrimalitySheafVerification.ManuscriptAudit.EtaleCechOrdinaryAcyclic
import PrimalitySheafVerification.ManuscriptAudit.EtaleCechProduct
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperProductResolution
import PrimalitySheafVerification.ManuscriptAudit.SkyscraperCechAcyclic

/-! Actual geometric skyscrapers give Čech-acyclic injective
presentations on the affine étale site of a spectrum. -/

namespace ManuscriptAudit.AffineEtaleCechSkyscrapers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EtaleCechDirectSum EtaleCechSectionLifts

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R : CommRingCat.{0})

private abbrev X := Spec R
private abbrev Ab := AddCommGrpCat.{0}
private abbrev Γ := Scheme.AffineEtale.topology (X R)
private abbrev Full := Sheaf (X R).smallEtaleTopology Ab
private abbrev Aff := Sheaf (Γ R) Ab
private abbrev E := Scheme.AffineEtale.sheafEquiv (X R) Ab

local instance : HasFiniteLimits (X R).AffineEtale := AffineEtaleMorphism.spec_hasFiniteLimits R

/-- The restriction of an actual geometric skyscraper on a spectrum
is Čech-acyclic on every singleton cover of its affine site. -/
theorem skyscraper_restriction_cechAcyclic (Φ : (X R).smallEtaleTopology.Point.{0}) (M : Ab) :
    AffineCechAcyclic ((E R).inverse.obj (Φ.skyscraperSheaf M)) := by
  intro U T f hf n
  let Ψ := DensePointRestriction.affineEtalePoint (X R) Φ
  let F : Aff R := (E R).inverse.obj (Φ.skyscraperSheaf M)
  let G : Aff R := Ψ.skyscraperSheaf M
  let e : F ≅ G := (fullyFaithfulSheafToPresheaf (Γ R) Ab).preimageIso (Iso.refl _)
  let H := sheafToPresheaf (Γ R) Ab ⋙ cochains f
  have h := SkyscraperCechAcyclic.H_succ_isZero f Ψ M hf n
  have hG : (Cech f G.obj).ExactAt (n + 1) :=
    ((Cech f G.obj).exactAt_iff_isZero_homology (n + 1)).mpr h
  exact hG.of_iso ((H.mapIso e).symm)

/-- Every sheaf on the affine étale site admits an injective
presentation by a product of actual Čech-acyclic skyscrapers. -/
theorem exists_cechAcyclic_injectivePresentation (A : Aff R) :
    ∃ I : InjectivePresentation A, AffineCechAcyclic I.J := by
  let B := (E R).functor.obj A
  let I₀ := GeometricSkyscraperProductResolution.injectivePresentation (X R) B
  let I := (E R).injectivePresentationOfMapInjectivePresentation A I₀
  let F := GeometricSkyscraperProductResolution.skyscraper (X R) B
  let G := fun x ↦ (E R).inverse.obj (F x)
  have hI : I.J = (E R).inverse.obj (∏ᶜ F) := by
    change (E R).inverse.obj I₀.J = _
    exact congrArg (E R).inverse.obj
      (GeometricSkyscraperProductResolution.injectivePresentation_J (X R) B)
  let e : I.J ≅ ∏ᶜ G := eqToIso hI ≪≫ PreservesProduct.iso (E R).inverse F
  refine ⟨I, ?_⟩
  intro U T f hf n
  have hG (x : X R) : AffineCechAcyclic (G x) :=
    skyscraper_restriction_cechAcyclic R
      (GeometricSkyscraperProductResolution.geometricFiber (X R) x)
      (GeometricSkyscraperProductResolution.coefficient (X R) B x)
  have h := EtaleCechProduct.product_exactAt_succ f G n (fun x ↦ hG x f hf n)
  let H := sheafToPresheaf (Γ R) Ab ⋙ cochains f
  exact h.of_iso (H.mapIso e).symm

end

end ManuscriptAudit.AffineEtaleCechSkyscrapers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleCechSkyscrapers.skyscraper_restriction_cechAcyclic,
      ``ManuscriptAudit.AffineEtaleCechSkyscrapers.exists_cechAcyclic_injectivePresentation] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
