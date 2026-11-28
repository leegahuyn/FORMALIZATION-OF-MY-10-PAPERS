import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorFullExact
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericUnitQuotient
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne

/-! The actual generic-unit quotient evaluated on a factoring affine
open yields its genuine finite height-one divisor cycle. -/

namespace ManuscriptAudit.AffineGenericQuotientCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsDedekindDomain
open AffineGeometricDivisorSheaf AffineGeometricDivisorSections AffineGeometricDivisorFullExact
open OpenEtaleExtension OpenEtaleGenericUnitQuotient GenericEtaleUnitSections EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K A F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev X := Spec (CommRingCat.of A)
private abbrev Y := Spec (CommRingCat.of F)
private abbrev g := Spec.map (CommRingCat.ofHom (algebraMap A F))
private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}

variable {Z : Scheme.{0}} (j : X A ⟶ Z) [IsOpenImmersion j] (f : Y F ⟶ Z)

private abbrev Q := cokernel (pullbackToDirectImage f)
private abbrev R := restriction j AddCommGrpCat.{0}
private abbrev U := algebraEtaleObject A A
private abbrev T := identityObject Z

/-- The ambient small étale object of the native affine terminal chart. -/
abbrev openTerminal := (etalePostcompose j).obj (U A)

private def openTerminalArrow : openTerminal A j ⟶ T (Z := Z) :=
  (MorphismProperty.Over.mkIdTerminal @Etale Z).from _

/-- Actual quotient evaluation on the native affine open is a finite cycle
of its height-one primes. -/
def openQuotientCycles (hf : f = g A F ≫ j) :
    (Q F f).obj.obj (op (openTerminal A j)) ≃+ (HeightOneSpectrum A →₀ ℤ) := by
  let q : (R A j).obj (Q F f) ≅ genericPointUnitQuotient A F := by
    subst f
    exact quotientIso j (g A F)
  let d := genericPointUnitQuotientIsoDivisor K A F
  let b := (E A).inverse.mapIso (q ≪≫ d) ≪≫ restrictionIso K A
  let eval := (sheafSections (Scheme.AffineEtale.topology (X A)) AddCommGrpCat.{0}).obj
    (op (chartObject A A))
  let e : (Q F f).obj.obj (op (openTerminal A j)) ≃+
      (affineDivisorSheaf K A).obj.obj (op (chartObject A A)) :=
    (eval.mapIso b).addCommGroupIsoToAddEquiv
  exact e.trans (chartSectionsEquiv K A A)

/-- The actual finite cycle of an ambient global quotient section after
restriction to the given affine open. -/
def ambientSectionsToCycle (hf : f = g A F ≫ j) :
    (Q F f).obj.obj (op (T (Z := Z))) →+ (HeightOneSpectrum A →₀ ℤ) :=
  (openQuotientCycles K A F j f hf).toAddMonoidHom.comp
    ((Q F f).obj.map (openTerminalArrow A j).op).hom

end

end ManuscriptAudit.AffineGenericQuotientCycles

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGenericQuotientCycles.openQuotientCycles,
      ``ManuscriptAudit.AffineGenericQuotientCycles.ambientSectionsToCycle] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
