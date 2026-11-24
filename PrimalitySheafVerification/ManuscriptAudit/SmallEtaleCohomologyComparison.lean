import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology

/-!
# Constant-coefficient comparison for the native small étale site

Restriction to affine objects induces the usual sheaf equivalence.
Terminal evaluation identifies the constant sheaves, and Ext under the
sheaf equivalence gives the actual derived cohomology comparison.
-/

namespace ManuscriptAudit.SmallEtaleCohomologyComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

private abbrev affineSite (R : CommRingCat.{0}) := Scheme.AffineEtale.topology (Spec R)
private abbrev fullSite (R : CommRingCat.{0}) := (Spec R).smallEtaleTopology
private abbrev siteInclusion (R : CommRingCat.{0}) := Scheme.AffineEtale.Spec (Spec R)

private abbrev siteEquiv (R : CommRingCat.{0}) :=
  Scheme.AffineEtale.sheafEquiv (Spec R) AddCommGrpCat.{0}

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

/-- The native full small étale site has the required Ext groups. -/
def fullSiteHasExt (R : CommRingCat.{0}) :
    HasExt.{0} (Sheaf (fullSite R) AddCommGrpCat.{0}) := by
  let C := Sheaf (fullSite R) AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology (Spec R) AddCommGrpCat.{0}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{0} (C := C)
  exact hasExt_of_enoughInjectives C

attribute [local instance] fullSiteHasExt

private def fullTerminal_isTerminal (R : CommRingCat.{0}) :
    IsTerminal ((siteInclusion R).obj (KummerAffineCohomology.affineTerminal R)) := by
  refine IsTerminal.ofUniqueHom (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _)) ?_
  intro U f
  apply MorphismProperty.Over.Hom.ext
  change f.left = U.hom
  have h := f.w
  change f.left ≫ 𝟙 (Spec R) = U.hom at h
  simpa only [Category.comp_id] using h

/-- The affine-to-full sheaf equivalence carries constant sheaves to the
actual constant sheaves on the small étale site. -/
def constantComparison (R : CommRingCat.{0}) :
    constantSheaf (affineSite R) AddCommGrpCat.{0} ⋙ (siteEquiv R).functor ≅
      constantSheaf (fullSite R) AddCommGrpCat.{0} :=
  ((constantSheafAdj (affineSite R) AddCommGrpCat.{0}
    (KummerAffineCohomology.affineTerminal_isTerminal R)).comp (siteEquiv R).toAdjunction).leftAdjointUniq
      (constantSheafAdj (fullSite R) AddCommGrpCat.{0} (fullTerminal_isTerminal R))

set_option backward.isDefEq.respectTransparency false in
/-- Constant-coefficient derived cohomology on the affine and full small
étale sites agrees in every degree. -/
def cohomologyEquiv (R : CommRingCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ) :
    Sheaf.H ((constantSheaf (affineSite R) AddCommGrpCat.{0}).obj A) n ≃+
      Sheaf.H ((constantSheaf (fullSite R) AddCommGrpCat.{0}).obj A) n := by
  let C := Sheaf (affineSite R) AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology (Spec R) AddCommGrpCat.{0}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{0} (C := C)
  let F := (siteEquiv R).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  let Z := AddCommGrpCat.of (ULift.{0} ℤ)
  let X := (constantSheaf (affineSite R) AddCommGrpCat.{0}).obj Z
  let Y := (constantSheaf (affineSite R) AddCommGrpCat.{0}).obj A
  let e₀ := AddEquiv.ofBijective (F.mapExtAddHom X Y n)
    (F.mapExt_bijective_of_preservesInjectiveObjects X Y n)
  let e₁ := (((extFunctor (C := Sheaf (fullSite R) AddCommGrpCat.{0}) n).mapIso
    ((constantComparison R).app Z).symm.op).app (F.obj Y)).addCommGroupIsoToAddEquiv
  let e₂ := ((Sheaf.functorH (fullSite R) n).mapIso
    ((constantComparison R).app A)).addCommGroupIsoToAddEquiv
  exact e₀.trans (e₁.trans e₂)

end

end ManuscriptAudit.SmallEtaleCohomologyComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleCohomologyComparison.constantComparison,
      ``ManuscriptAudit.SmallEtaleCohomologyComparison.cohomologyEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
