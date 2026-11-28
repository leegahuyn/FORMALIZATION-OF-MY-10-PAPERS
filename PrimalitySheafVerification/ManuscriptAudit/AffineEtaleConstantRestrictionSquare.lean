import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTerminalBasisSectionHom
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleNestedSectionComparison
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTerminalExt
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleTerminalSectionHom

/-! The actual restriction functors on the full and affine small étale
sites commute, including the literal morphisms from constant integers. -/

namespace ManuscriptAudit.AffineEtaleConstantRestrictionSquare

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open AffineEtaleNestedSectionComparison AffineEtaleTerminalBasisSectionHom
open EtaleTwoOpenHOne OpenEtaleExtension
open TerminalCohomologySectionHom OpenEtaleTerminalSectionHom

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

private abbrev B := AddCommGrpCat.{0}
private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev J (R : Type) [CommRing R] := (X R).smallEtaleTopology
private abbrev Jb (R : Type) [CommRing R] := Scheme.AffineEtale.topology (X R)
private abbrev E (R : Type) [CommRing R] := Scheme.AffineEtale.sheafEquiv (X R) B
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]
private abbrev F := restriction (i A S) B
private abbrev R := affineRestriction (i A S)

private abbrev t (R : Type) [CommRing R] := MorphismProperty.Over.mkIdTerminal @Etale (X R)
private abbrev t' (R : Type) [CommRing R] := KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)
private abbrev Z (R : Type) [CommRing R] := integerSheaf (J R)

/-- The actual comparison of restriction on the full and affine small sites. -/
def siteSquare : (E A).inverse ⋙ R A S ≅ F A S ⋙ (E S).inverse :=
  NatIso.ofComponents
    (fun P => (E S).inverse.mapIso ((F A S).mapIso ((E A).counitIso.app P)))
    (by
      intro P Q a
      have h := (E A).counitIso.hom.naturality a
      have h' := congrArg (fun f : (E A).functor.obj ((E A).inverse.obj P) ⟶ Q =>
        (E S).inverse.map ((F A S).map f)) h
      simpa only [Functor.map_comp] using h')

/-- The actual integer maps in the full and affine derived restrictions
have the same effect through the literal small-site comparison. -/
theorem integer_square :
    AffineEtaleDerivedRestriction.restrictionConstant A S ≫ (R A S).map (basisIntegerIso A).hom ≫
        (siteSquare A S).hom.app (Z A) =
      (basisIntegerIso S).hom ≫ (E S).inverse.map (constantIntegerIso (i A S)).hom := by
  let x := Sheaf.H.equiv₀ (Z A) (t A) (Ext.mk₀ (𝟙 (Z A)))
  let y := OpenEtaleTerminalSectionHom.restrictSection (i A S) (Z A) x
  have hx : sectionHom (J A) (t A) (Z A) x = 𝟙 (Z A) := by
    apply (Ext.mk₀_bijective (Z A) (Z A)).injective
    rw [mk₀_sectionHom, x, AddEquiv.symm_apply_apply]
  have hA := sectionHom_basis A (Z A) x
  rw [hx, Functor.map_id, Category.comp_id] at hA
  have hF := OpenEtaleTerminalSectionHom.sectionHom_restrict (i A S) (Z A) x
  rw [hx, Functor.map_id, Category.comp_id] at hF
  have hS := sectionHom_basis S ((F A S).obj (Z A)) y
  rw [hF] at hS
  have h := AffineEtaleTerminalExt.sectionHom_restrict A S ((siteSquare A S).hom.app (Z A)) x
  change sectionHom (Jb S) (t' S) ((E S).inverse.obj ((F A S).obj (Z A)))
      (((F A S).map ((E A).counitIso.hom.app (Z A))).hom.app (op (identityObject (X S)))
        ((AffineEtaleCechRestriction.restrictSection (i A S) ((E A).inverse.obj (Z A))
          (baseMap A S)).hom x)) =
    AffineEtaleDerivedRestriction.restrictionConstant A S ≫
      (R A S).map (sectionHom (Jb A) (t' A) ((E A).inverse.obj (Z A)) x) ≫
        (siteSquare A S).hom.app (Z A) at h
  rw [affineSection_counit A S (Z A) x, hA] at h
  exact h.symm.trans hS

end

end ManuscriptAudit.AffineEtaleConstantRestrictionSquare

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleConstantRestrictionSquare.integer_square
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
