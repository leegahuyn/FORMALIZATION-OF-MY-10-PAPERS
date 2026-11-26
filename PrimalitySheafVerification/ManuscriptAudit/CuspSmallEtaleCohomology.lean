import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleBaseChange
import PrimalitySheafVerification.ManuscriptAudit.CuspAffineEtaleEquivalence
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCuspHOne

/-!
# Normalization invariance for the cusp in prime characteristic

Affine étale base change identifies the native affine sheaf categories.
The comparison preserves constant coefficients, so it also identifies
their Ext cohomology groups on the full small étale sites.
-/

namespace ManuscriptAudit.CuspSmallEtaleCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open CuspAffineEtale SmallEtaleCohomologyComparison

noncomputable section

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

private abbrev cuspRing := CommRingCat.of (CuspPunctured.CuspSubalgebra K)
private abbrev normalizationRing := CommRingCat.of (Polynomial K)

private abbrev affineCuspSite := Scheme.AffineEtale.topology (Cusp K)
private abbrev affineNormalizationSite := Scheme.AffineEtale.topology (Normalization K)

private def affineComparison :
    Sheaf (affineCuspSite K) AddCommGrpCat.{0} ≌
      Sheaf (affineNormalizationSite K) AddCommGrpCat.{0} := by
  letI := affinePullback_isEquivalence K p
  exact (AffineEtaleBaseChange.affineSheafEquivalence (CuspScheme.cuspMap K)
    ((surjective_iff (CuspScheme.cuspMap K)).mp (CuspScheme.paper2_cusp_map_surjective K))
    (affinePullback K) (affinePullbackSpecIso K) AddCommGrpCat.{0}).symm

private def mappedTerminal_isTerminal :
    IsTerminal ((affinePullback K).obj (KummerAffineCohomology.affineTerminal (cuspRing K))) := by
  let e := affineEtaleEquivalence K p
  let T := KummerAffineCohomology.affineTerminal (cuspRing K)
  let h := KummerAffineCohomology.affineTerminal_isTerminal (cuspRing K)
  let homEquiv (U : (Normalization K).AffineEtale) :
      (e.inverse.obj U ⟶ T) ≃ (U ⟶ (affinePullback K).obj T) :=
    e.symm.toAdjunction.homEquiv U T
  refine IsTerminal.ofUniqueHom (fun U => homEquiv U (h.from (e.inverse.obj U))) ?_
  intro U f
  apply (homEquiv U).symm.injective
  exact (h.hom_ext _ _).trans ((homEquiv U).symm_apply_apply _).symm

private def constantComparison :
    constantSheaf (affineCuspSite K) AddCommGrpCat.{0} ⋙ (affineComparison K p).functor ≅
      constantSheaf (affineNormalizationSite K) AddCommGrpCat.{0} :=
  ((constantSheafAdj (affineCuspSite K) AddCommGrpCat.{0}
    (KummerAffineCohomology.affineTerminal_isTerminal (cuspRing K))).comp
    (affineComparison K p).toAdjunction).leftAdjointUniq
    (constantSheafAdj (affineNormalizationSite K) AddCommGrpCat.{0} (mappedTerminal_isTerminal K p))

attribute [local instance] KummerCohomologySequence.affineSiteHasExt fullSiteHasExt

set_option backward.isDefEq.respectTransparency false in
private def affineCohomologyEquiv (A : AddCommGrpCat.{0}) (n : ℕ) :
    Sheaf.H ((constantSheaf (affineCuspSite K) AddCommGrpCat.{0}).obj A) n ≃+
      Sheaf.H ((constantSheaf (affineNormalizationSite K) AddCommGrpCat.{0}).obj A) n := by
  let C := Sheaf (affineCuspSite K) AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology (Cusp K) AddCommGrpCat.{0}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{0} (C := C)
  let F := (affineComparison K p).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  let Z := AddCommGrpCat.of (ULift.{0} ℤ)
  let X := (constantSheaf (affineCuspSite K) AddCommGrpCat.{0}).obj Z
  let Y := (constantSheaf (affineCuspSite K) AddCommGrpCat.{0}).obj A
  let e₀ := AddEquiv.ofBijective (F.mapExtAddHom X Y n)
    (F.mapExt_bijective_of_preservesInjectiveObjects X Y n)
  let e₁ := (((extFunctor (C := Sheaf (affineNormalizationSite K) AddCommGrpCat.{0}) n).mapIso
    ((constantComparison K p).app Z).symm.op).app (F.obj Y)).addCommGroupIsoToAddEquiv
  let e₂ := ((Sheaf.functorH (affineNormalizationSite K) n).mapIso
    ((constantComparison K p).app A)).addCommGroupIsoToAddEquiv
  exact e₀.trans (e₁.trans e₂)

/-- The cusp and its normalization have isomorphic constant-coefficient small étale
cohomology in every degree over a field of prime characteristic. -/
def normalizationCohomologyEquiv (A : AddCommGrpCat.{0}) (n : ℕ) :
    Sheaf.H ((constantSheaf (Cusp K).smallEtaleTopology AddCommGrpCat.{0}).obj A) n ≃+
      Sheaf.H ((constantSheaf (Normalization K).smallEtaleTopology AddCommGrpCat.{0}).obj A) n :=
  ((cohomologyEquiv (cuspRing K) A n).symm.trans (affineCohomologyEquiv K p A n)).trans
    (cohomologyEquiv (normalizationRing K) A n)

/-- On the actual full small étale site of the unpunctured cusp, H¹ vanishes
for constant cyclic coefficients of order invertible in the ground field. -/
theorem cusp_cyclic_HOne_subsingleton [IsAlgClosed K] (d : ℕ) [NeZero (d : K)] :
    Subsingleton
      (Sheaf.H ((constantSheaf (Cusp K).smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ZMod d))) 1) := by
  let e := normalizationCohomologyEquiv K p (AddCommGrpCat.of (ZMod d)) 1
  have h := SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K d
  exact ⟨fun a b => e.injective (h.elim _ _)⟩

end

end ManuscriptAudit.CuspSmallEtaleCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspSmallEtaleCohomology.normalizationCohomologyEquiv,
      ``ManuscriptAudit.CuspSmallEtaleCohomology.cusp_cyclic_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
