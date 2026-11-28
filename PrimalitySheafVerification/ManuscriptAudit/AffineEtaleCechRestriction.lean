import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictionEvaluation

/-! Actual Čech section restriction on affine small étale objects.
The difference of the two lifts is carried to the difference after
restriction whenever the cover and overlap arrows commute. -/

namespace ManuscriptAudit.AffineEtaleCechRestriction

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleOpenRestriction AffineEtaleRestrictionEvaluation

noncomputable section

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev C := AddCommGrpCat.{u}
variable (I : Sheaf (Scheme.AffineEtale.topology X) C.{u})
private abbrev F := affinePostcompose j
private abbrev J := (affineRestriction j).obj I

/-- Pull a section over an ambient affine object onto an open affine object. -/
def restrictSection {D : U.AffineEtale} {V : X.AffineEtale} (r : (F j).obj D ⟶ V) :
    I.obj.obj (op V) ⟶ (J j I).obj.obj (op D) :=
  I.obj.map r.op ≫ (restrictionPresheafIso j I).inv.app (op D)

theorem restrictSection_target {D D' : U.AffineEtale} {V : X.AffineEtale}
    (r : (F j).obj D ⟶ V) (d : D' ⟶ D) :
    restrictSection j I r ≫ (J j I).obj.map d.op =
      restrictSection j I ((F j).map d ≫ r) := by
  unfold restrictSection
  rw [Category.assoc, ← (restrictionPresheafIso j I).inv.naturality d.op, ← Category.assoc]
  congr 1
  rw [op_comp, Functor.map_comp] <;> rfl

theorem restrictSection_source {D : U.AffineEtale} {V V' : X.AffineEtale}
    (r : (F j).obj D ⟶ V) (d : V ⟶ V') :
    I.obj.map d.op ≫ restrictSection j I r = restrictSection j I (r ≫ d) := by
  unfold restrictSection
  rw [← Category.assoc, op_comp, Functor.map_comp]

/-- Actual restriction takes the Čech difference of one local section
to the Čech difference on the base-changed cover. -/
theorem restrictSection_difference {D E : U.AffineEtale} {V W : X.AffineEtale}
    (r : (F j).obj D ⟶ V) (s : (F j).obj E ⟶ W)
    (p₁ p₂ : E ⟶ D) (q₁ q₂ : W ⟶ V)
    (h₁ : s ≫ q₁ = (F j).map p₁ ≫ r) (h₂ : s ≫ q₂ = (F j).map p₂ ≫ r)
    (y : I.obj.obj (op V)) :
    (restrictSection j I s).hom ((I.obj.map q₁.op).hom y - (I.obj.map q₂.op).hom y) =
      ((J j I).obj.map p₁.op).hom ((restrictSection j I r).hom y) -
      ((J j I).obj.map p₂.op).hom ((restrictSection j I r).hom y) := by
  rw [map_sub]
  congr 1
  · have e := (restrictSection_source j I s q₁).trans
      ((congrArg (restrictSection j I) h₁).trans (restrictSection_target j I r p₁).symm)
    exact congrArg (fun f => f.hom y) e
  · have e := (restrictSection_source j I s q₂).trans
      ((congrArg (restrictSection j I) h₂).trans (restrictSection_target j I r p₂).symm)
    exact congrArg (fun f => f.hom y) e

end

end ManuscriptAudit.AffineEtaleCechRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleCechRestriction.restrictSection_difference
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
