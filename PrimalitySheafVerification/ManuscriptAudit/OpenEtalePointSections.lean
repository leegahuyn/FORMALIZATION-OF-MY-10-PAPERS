import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericImageRestriction
import PrimalitySheafVerification.ManuscriptAudit.EtaleCohomologyPresheafZero
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne

/-! A factoring point sees the same actual degree-zero sections on every
open through which it factors. -/

namespace ManuscriptAudit.OpenEtalePointSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleObjectRestriction SmallEtaleBaseChange OpenEtaleGenericImageRestriction
open EtaleTwoOpenHOne EtaleCohomologyPresheafZero

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {Y U X : Scheme.{u}} (g : Y ⟶ U) (j : U ⟶ X) [IsOpenImmersion j]

private def openObjectIso :
    (postcompose j).obj (identityObject U) ≅ Scheme.Etale.mk j :=
  MorphismProperty.Over.isoMk (Iso.refl U) (by simp)

/-- Base-changing an open through which the point factors gives the
terminal étale object over the point's source. -/
def factoringOpen_isTerminal :
    IsTerminal ((etaleBaseChange (g ≫ j)).obj (Scheme.Etale.mk j)) := by
  let B := etaleBaseChange g
  letI : PreservesFiniteLimits B := preservesFiniteLimits g
  let t := identityObject U
  have ht : IsTerminal t := MorphismProperty.Over.mkIdTerminal @Etale U
  let i : B.obj t ≅ (etaleBaseChange (g ≫ j)).obj (Scheme.Etale.mk j) :=
    ((postcomposeBaseChangeIso j g).app t).symm ≪≫
      (etaleBaseChange (g ≫ j)).mapIso (openObjectIso j)
  exact (ht.isTerminalObj B t).ofIso i

variable {V : Scheme.{u}} (k : V ⟶ X) [IsOpenImmersion k]
variable (f : Y ⟶ X) (h : Y ⟶ V)
variable (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

private abbrev D := (directImage f AddCommGrpCat.{u}).obj M

/-- On the actual direct image, the real degree-zero cohomology presheaf
restriction is bijective between any two opens through which the point factors. -/
theorem restriction_HZero_bijective
    (a : Scheme.Etale.mk k ⟶ Scheme.Etale.mk j)
    (hj : f = g ≫ j) (hk : f = h ≫ k) :
    Function.Bijective (((D f M).cohomologyPresheaf 0).map a.op).hom := by
  let B := etaleBaseChange f
  have hU : IsTerminal (B.obj (Scheme.Etale.mk j)) := by
    change IsTerminal ((etaleBaseChange f).obj (Scheme.Etale.mk j))
    rw [hj]
    exact factoringOpen_isTerminal g j
  have hV : IsTerminal (B.obj (Scheme.Etale.mk k)) := by
    change IsTerminal ((etaleBaseChange f).obj (Scheme.Etale.mk k))
    rw [hk]
    exact factoringOpen_isTerminal h k
  letI : IsIso (B.map a) := isIso_of_isTerminal hV hU (B.map a)
  let e := (M.obj.mapIso (asIso (B.map a)).op).addCommGroupIsoToAddEquiv
  let b := equivZero (D f M) (Scheme.Etale.mk j)
  let c := equivZero (D f M) (Scheme.Etale.mk k)
  let r := ((D f M).cohomologyPresheaf 0).map a.op
  have he (x) : c (r x) = e (b x) := equivZero_natural (D f M) a x
  constructor
  · intro x y hxy
    apply b.injective
    apply e.injective
    exact (he x).symm.trans ((congrArg c hxy).trans (he y))
  · intro y
    obtain ⟨x, hx⟩ := (e.bijective.comp b.bijective).2 (c y)
    exact ⟨x, c.injective ((he x).trans hx)⟩

end

end ManuscriptAudit.OpenEtalePointSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtalePointSections.restriction_HZero_bijective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
