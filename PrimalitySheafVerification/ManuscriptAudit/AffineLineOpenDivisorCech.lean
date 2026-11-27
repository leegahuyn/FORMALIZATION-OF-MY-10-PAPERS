import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCechSkyscrapers
import PrimalitySheafVerification.ManuscriptAudit.AffineLineOpenDivisorSum
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSkyscraperRestriction

/-! The actual affine-site restriction of the affine-line divisor
sheaf is Čech-acyclic on every affine open. -/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleCechSkyscrapers EtaleCechDirectSum EtaleCechSectionLifts
open EtaleObjectRestriction FiniteSupportPresheaf IsDedekindDomain

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable (R : CommRingCat.{0})

private abbrev V := Spec R
private abbrev Ab := AddCommGrpCat.{0}
private abbrev J := Scheme.AffineEtale.topology (V R)
private abbrev C := Sheaf (J R) Ab
private abbrev E := Scheme.AffineEtale.sheafEquiv (V R) Ab

local instance : HasFiniteLimits (V R).AffineEtale := AffineEtaleMorphism.spec_hasFiniteLimits R

private theorem cechAcyclic_of_iso {A B : C R} (e : A ≅ B) (h : AffineCechAcyclic A) :
    AffineCechAcyclic B := by
  intro U T f hf n
  let H := sheafToPresheaf (J R) Ab ⋙ cochains f
  exact (h f hf n).of_iso (H.mapIso e)

private theorem cechAcyclic_of_isZero {A : C R} (h : IsZero A) : AffineCechAcyclic A := by
  intro U T f hf n
  let W := CechNerveLowDegrees.N f (n + 1)
  let F := sheafToPresheaf (J R) Ab ⋙ (evaluation (V R).AffineEtaleᵒᵖ Ab).obj (op W)
  have h' : IsZero ((Cech f A.obj).X (n + 1)) := F.map_isZero h
  exact HomologicalComplex.ExactAt.of_isZero h'

variable (K : Type) [Field K] [IsAlgClosed K]
variable (j : V R ⟶ X K) [IsOpenImmersion j]

private abbrev P := HeightOneSpectrum (Polynomial K)
private abbrev E₀ := Scheme.AffineEtale.sheafEquiv (X K) Ab
private abbrev sourcePoint (p : P K) : Spec (CommRingCat.of K) ⟶ X K :=
  AffineLineRationalClosedPoints.rationalPoint K ((AffineLineRationalClosedPoints.closedPointEquiv K).symm p)

/-- An actual summand on an affine open is Čech-acyclic. A point in the
open gives an actual smaller skyscraper, and its absence gives zero. -/
theorem affineOpenDivisorPiece_cechAcyclic (p : P K) :
    AffineCechAcyclic (affineOpenDivisorPiece K R j p) := by
  let M := AddCommGrpCat.of ℤ
  let S (t : Spec (CommRingCat.of K) ⟶ X K) :=
    (restriction j).obj ((Scheme.pointSmallEtale t).skyscraperSheaf M)
  let A := (E R).inverse.obj (S (sourcePoint K p))
  let D := affineOpenDivisorPiece K R j p
  let e : D ≅ A := (E R).inverse.mapIso
    ((restriction j).mapIso ((E₀ K).counitIso.app
      ((Scheme.pointSmallEtale (sourcePoint K p)).skyscraperSheaf M)))
  apply cechAcyclic_of_iso R e.symm
  by_cases h : ∃ t : Spec (CommRingCat.of K) ⟶ V R, t ≫ j = sourcePoint K p
  · obtain ⟨t, ht⟩ := h
    let e₁ : S (sourcePoint K p) ≅ (Scheme.pointSmallEtale t).skyscraperSheaf M :=
      eqToIso (congrArg S ht.symm) ≪≫ OpenEtaleSkyscraperRestriction.restrictionInsideIso j t M
    exact cechAcyclic_of_iso R ((E R).inverse.mapIso e₁).symm
      (skyscraper_restriction_cechAcyclic R (Scheme.pointSmallEtale t) M)
  · have h₀ : IsZero (S (sourcePoint K p)) :=
      OpenEtaleSkyscraperRestriction.restrictionOutside_isZero j (sourcePoint K p) h M
    exact cechAcyclic_of_isZero R ((E R).inverse.map_isZero h₀)

/-- The actual restricted divisor is singleton Čech-acyclic anywhere
on the small affine étale site of the affine open. -/
theorem affineRestrictedDivisor_cechAcyclic :
    AffineCechAcyclic ((affineOpenRestriction K R j).obj (affineDivisorSheaf K)) := by
  apply cechAcyclic_of_iso R (affineRestrictedDivisorIso K R j).symm
  intro U T f hf n
  let B := fun p : P K ↦ (affineOpenDivisorPiece K R j p).obj
  change (Cech f (directSum B)).ExactAt (n + 1)
  exact directSum_exactAt_succ f B n (fun p ↦ affineOpenDivisorPiece_cechAcyclic R K j p f hf n)

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.affineOpenDivisorPiece_cechAcyclic,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineRestrictedDivisor_cechAcyclic] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
