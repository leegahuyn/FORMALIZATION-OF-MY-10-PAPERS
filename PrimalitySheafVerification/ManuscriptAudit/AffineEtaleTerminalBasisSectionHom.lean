import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSheafificationUnit
import PrimalitySheafVerification.ManuscriptAudit.TerminalCohomologySectionHom
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorOverlap
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology

/-! On the genuine affine small étale basis, the actual section represented
by constant integers is literally the same terminal section as on the full site. -/

namespace ManuscriptAudit.AffineEtaleTerminalBasisSectionHom

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open TerminalCohomologySectionHom AffineEtaleSheafificationUnit
open AffineEtaleTensorOverlap EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

variable (R : Type) [CommRing R]

private abbrev A := AddCommGrpCat.{0}
private abbrev X := Spec (CommRingCat.of R)
private abbrev J := (X R).smallEtaleTopology
private abbrev Jb := Scheme.AffineEtale.topology (X R)
private abbrev E := Scheme.AffineEtale.sheafEquiv (X R) A
private abbrev T := identityObject (X R)
private abbrev T' := baseObject R
private abbrev t := MorphismProperty.Over.mkIdTerminal @Etale (X R)
private abbrev t' := KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)

/-- The actual constant integer sheaf comparison for the affine basis. -/
def basisIntegerIso : integerSheaf (Jb R) ≅ (E R).inverse.obj (integerSheaf (J R)) :=
  (comparison (X R)).app (integerPresheaf (D := (X R).Etale))

variable (F : Sheaf (J R) A)

/-- The actual morphism representing a section on the full small site
restricts to the corresponding morphism on the affine basis. -/
theorem sectionHom_basis (x : F.obj.obj (op (T R))) :
    sectionHom (Jb R) (t' R) ((E R).inverse.obj F)
        (show ((E R).inverse.obj F).obj.obj (op (T' R)) from x) =
      (basisIntegerIso R).hom ≫ (E R).inverse.map (sectionHom (J R) (t R) F x) := by
  let f := sectionHom (J R) (t R) F x
  let p := presheafHom (J R) F f
  let Q := (E R).inverse.obj F
  let g := (basisIntegerIso R).hom ≫ (E R).inverse.map f
  let s := sheafificationAdjunction (J R) A
  have hp : (s.homEquiv (integerPresheaf (D := (X R).Etale)) F).symm p = f :=
    (s.homEquiv (integerPresheaf (D := (X R).Etale)) F).symm_apply_apply f
  have h := comparison_postcompose (X R) (integerPresheaf (D := (X R).Etale)) F p
  rw [hp] at h
  have hv := congrArg (fun a : integerPresheaf (D := (X R).AffineEtale) ⟶ Q.obj =>
    a.app (op (T' R)) (ULift.up 1)) h
  change (presheafHom (Jb R) Q g).app (op (T' R)) (ULift.up 1) =
    p.app (op (T R)) (ULift.up 1) at hv
  have hx : p.app (op (T R)) (ULift.up 1) = x := by
    rw [← evaluate_hom (J R) (t R) F, mk₀_sectionHom, AddEquiv.apply_symm_apply]
  apply (Ext.mk₀_bijective (integerSheaf (Jb R)) Q).injective
  apply (Sheaf.H.equiv₀ Q (t' R)).injective
  rw [mk₀_sectionHom, AddEquiv.apply_symm_apply, evaluate_hom]
  exact (hv.trans hx).symm

end

end ManuscriptAudit.AffineEtaleTerminalBasisSectionHom

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleTerminalBasisSectionHom.sectionHom_basis
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
