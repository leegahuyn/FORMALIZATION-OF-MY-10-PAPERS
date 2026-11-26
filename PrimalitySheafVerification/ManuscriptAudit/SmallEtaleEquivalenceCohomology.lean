import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.Equivalence
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# Constant coefficients under comparison of native small étale sites

An equivalence of sites carries constant sheaves to constant sheaves,
as seen by evaluating at a terminal étale object. It then identifies
the derived cohomology groups, using the exact equivalence of abelian
sheaf categories.
-/

namespace ManuscriptAudit.SmallEtaleEquivalenceCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open SmallEtaleCohomologyComparison

noncomputable section

private abbrev site (R : CommRingCat.{0}) := (Spec R).smallEtaleTopology

private def identityEtale (R : CommRingCat.{0}) : (Spec R).Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 (Spec R)) (by infer_instance)

private def identityEtale_isTerminal (R : CommRingCat.{0}) : IsTerminal (identityEtale R) := by
  refine IsTerminal.ofUniqueHom (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _)) ?_
  intro U f
  apply MorphismProperty.Over.Hom.ext
  change f.left = U.hom
  have h := f.w
  change f.left ≫ 𝟙 (Spec R) = U.hom at h
  exact (Category.comp_id f.left).symm.trans h

variable {R T : CommRingCat.{0}} (e : (Spec R).Etale ≌ (Spec T).Etale)
variable [e.inverse.IsDenseSubsite (site T) (site R)]

private abbrev sheafComparison := e.sheafCongr (site R) (site T) AddCommGrpCat.{0}

private def mappedIdentity_isTerminal : IsTerminal (e.functor.obj (identityEtale R)) := by
  let h := identityEtale_isTerminal R
  let homEquiv (U : (Spec T).Etale) :
      (e.inverse.obj U ⟶ identityEtale R) ≃ (U ⟶ e.functor.obj (identityEtale R)) :=
    e.symm.toAdjunction.homEquiv U (identityEtale R)
  refine IsTerminal.ofUniqueHom (fun U => homEquiv U (h.from (e.inverse.obj U))) ?_
  intro U f
  apply (homEquiv U).symm.injective
  exact (h.hom_ext _ _).trans ((homEquiv U).symm_apply_apply _).symm

/-- The sheaf equivalence from the small étale site comparison preserves constant sheaves. -/
def constantComparison :
    constantSheaf (site R) AddCommGrpCat.{0} ⋙ (sheafComparison e).functor ≅
      constantSheaf (site T) AddCommGrpCat.{0} :=
  ((constantSheafAdj (site R) AddCommGrpCat.{0} (identityEtale_isTerminal R)).comp
    (sheafComparison e).toAdjunction).leftAdjointUniq
    (constantSheafAdj (site T) AddCommGrpCat.{0} (mappedIdentity_isTerminal e))

attribute [local instance] fullSiteHasExt

set_option backward.isDefEq.respectTransparency false in
/-- The actual constant-coefficient derived groups agree in every degree. -/
def cohomologyEquiv (A : AddCommGrpCat.{0}) (n : ℕ) :
    Sheaf.H ((constantSheaf (site R) AddCommGrpCat.{0}).obj A) n ≃+
      Sheaf.H ((constantSheaf (site T) AddCommGrpCat.{0}).obj A) n := by
  let C := Sheaf (site R) AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology (Spec R) AddCommGrpCat.{0}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{0} (C := C)
  let F := (sheafComparison e).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  let Z := AddCommGrpCat.of (ULift.{0} ℤ)
  let X := (constantSheaf (site R) AddCommGrpCat.{0}).obj Z
  let Y := (constantSheaf (site R) AddCommGrpCat.{0}).obj A
  let e₀ := AddEquiv.ofBijective (F.mapExtAddHom X Y n)
    (F.mapExt_bijective_of_preservesInjectiveObjects X Y n)
  let e₁ := (((extFunctor (C := Sheaf (site T) AddCommGrpCat.{0}) n).mapIso
    ((constantComparison e).app Z).symm.op).app (F.obj Y)).addCommGroupIsoToAddEquiv
  let e₂ := ((Sheaf.functorH (site T) n).mapIso
    ((constantComparison e).app A)).addCommGroupIsoToAddEquiv
  exact e₀.trans (e₁.trans e₂)

end

end ManuscriptAudit.SmallEtaleEquivalenceCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleEquivalenceCohomology.constantComparison,
      ``ManuscriptAudit.SmallEtaleEquivalenceCohomology.cohomologyEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
