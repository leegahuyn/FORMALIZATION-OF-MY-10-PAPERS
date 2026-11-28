import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! Exact formula for the sheafification comparison of the actual
full and affine small étale sites on the sheafification unit. -/

namespace ManuscriptAudit.AffineEtaleSheafificationUnit

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Functor CategoryTheory.Functor.IsDenseSubsite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (X : Scheme.{u})

private abbrev A := AddCommGrpCat.{u}
private abbrev J := Scheme.AffineEtale.topology X
private abbrev K := X.smallEtaleTopology
private abbrev G := Scheme.AffineEtale.Spec X
private abbrev a := sheafificationAdjunction (J X) A.{u}
private abbrev b := sheafificationAdjunction (K X) A.{u}
private abbrev E := Scheme.AffineEtale.sheafEquiv X A.{u}
private abbrev L := presheafToSheaf (K X) A.{u}
private abbrev W := (Functor.whiskeringLeft X.AffineEtaleᵒᵖ X.Etaleᵒᵖ A.{u}).obj (G X).op

/-- The actual compatibility of full and affine sheafification. -/
abbrev comparison :=
  sheafEquivSheafificationCompatibility (J X) (K X) (G X) A.{u}

/-- The actual dense-subsite comparison factors the literal restricted
unit of full small étale sheafification. -/
theorem comparison_unit (F : X.Etaleᵒᵖ ⥤ A.{u}) :
    (a X).homEquiv ((W X).obj F) ((E X).inverse.obj ((L X).obj F))
      ((comparison X).hom.app F) =
    (W X).map ((b X).unit.app F) := by
  letI := IsDenseSubsite.isLocallyFull (J X) (K X) (G X)
  letI := IsDenseSubsite.isCoverDense (J X) (K X) (G X)
  let H := sheafifyAdjunctionOfIsEquivalence (J X) (K X) (G X) A.{u}
  let t := (H.leftAdjointUniq (b X)).hom.app F
  let Q := (L X).obj F
  let F' := (presheafToSheaf (J X) A.{u}).obj ((W X).obj F)
  let c := (E X).unitIso.hom.app F' ≫ (E X).inverse.map t
  let r : ((W X).obj F ⟶ (W X).obj Q.obj) ≃ (F ⟶ Q.obj) :=
    IsCoverDense.restrictHomEquivHom (G := G X)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app H (b X) F
  have h' : r ((a X).homEquiv ((W X).obj F) ((E X).inverse.obj Q) c) =
      (b X).unit.app F := by
    change (sheafifyAdjunctionOfIsEquivalence (J X) (K X) (G X) A.{u}).homEquiv F Q t =
      (b X).unit.app F at h
    rw [sheafifyAdjunctionOfIsEquivalence, Adjunction.mkOfHomEquiv_homEquiv] at h
    exact h
  have hh := congrArg r.symm h'
  rw [Equiv.symm_apply_apply] at hh
  have hc : (comparison X).hom.app F = c := by
    simp [comparison, c, F', t, H, sheafEquivSheafificationCompatibility,
      sheafifyOfIsEquivalenceCompIso, Scheme.AffineEtale.sheafEquiv]
  rw [hc]
  exact hh

/-- The compatibility on actual maps into a full sheaf is obtained by
literally restricting their presheaf adjoints. -/
theorem comparison_postcompose (F : X.Etaleᵒᵖ ⥤ A.{u})
    (Q : Sheaf (K X) A.{u}) (g : F ⟶ Q.obj) :
    (a X).homEquiv ((W X).obj F) ((E X).inverse.obj Q)
      ((comparison X).hom.app F ≫ (E X).inverse.map (((b X).homEquiv F Q).symm g)) =
    (W X).map g := by
  let f := ((b X).homEquiv F Q).symm g
  have hf : (b X).unit.app F ≫ (sheafToPresheaf (K X) A.{u}).map f = g :=
    ((b X).homEquiv_unit (f := f)).symm.trans (((b X).homEquiv F Q).apply_symm_apply g)
  rw [(a X).homEquiv_naturality_right]
  change (a X).homEquiv ((W X).obj F) ((E X).inverse.obj ((L X).obj F))
      ((comparison X).hom.app F) ≫ (W X).map ((sheafToPresheaf (K X) A.{u}).map f) =
    (W X).map g
  rw [comparison_unit, ← Functor.map_comp, hf]

end

end ManuscriptAudit.AffineEtaleSheafificationUnit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleSheafificationUnit.comparison_unit,
      ``ManuscriptAudit.AffineEtaleSheafificationUnit.comparison_postcompose] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
