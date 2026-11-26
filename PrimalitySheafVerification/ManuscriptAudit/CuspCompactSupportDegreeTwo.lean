import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspChartIntersection
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportProjectiveComparison
import PrimalitySheafVerification.ManuscriptAudit.CuspSmallEtaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisConnecting
import PrimalitySheafVerification.ManuscriptAudit.EtaleOpenIntersection
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCuspHOne

/-!
# A nonzero second compact-support class from the actual cusp overlap

The native Mayer–Vietoris map from the punctured overlap is injective
because each affine chart has zero H¹. Ordinary cohomology on the
proper closure therefore receives a full cyclic coefficient group in
degree two. The comparison at infinity identifies this with a subgroup
of the same degree of compactly supported cohomology on the affine cusp.
-/

namespace ManuscriptAudit.CuspCompactSupportDegreeTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification CuspProperYChart CuspCompactSupportSequence
open OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev C (X : Scheme.{0}) (M : AddCommGrpCat.{0}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj M

private def restrictionCohomology {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : AddCommGrpCat.{0}) (d : ℕ) :
    Sheaf.H ((restriction j AddCommGrpCat.{0}).obj (C X M)) d ≃+
      Sheaf.H (C U M) d :=
  ((Sheaf.functorH U.smallEtaleTopology d).mapIso
    ((restrictionConstantIso j).app M)).addCommGroupIsoToAddEquiv

/-- The actual compactly supported H² contains a copy of the cyclic coefficient group. -/
theorem cuspHcTwo_contains_cyclic (K : Type) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (ℓ : ℕ) [NeZero (ℓ : K)] (hℓ : 2 ≤ ℓ) :
    ∃ f : ZMod ℓ →+ cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2, Function.Injective f := by
  let j := affineOpen K
  let k := lineOpen K
  let l := pullback.fst j k ≫ j
  letI : IsOpenImmersion j := affineOpen_isOpenImmersion K
  letI : IsOpenImmersion k := lineOpen_isOpenImmersion K
  letI : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion (pullback.fst j k ≫ j))
  let M := AddCommGrpCat.of (ZMod ℓ)
  let F := C (projectiveCusp K) M
  let a := EtaleOpenIntersection.fstLeg j k
  let b := EtaleOpenIntersection.sndLeg j k
  let hD := EtaleOpenIntersection.intersection_isPullback j k
  have hc : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun O : (projectiveCusp K).Opens => (O : Set (projectiveCusp K))) (affine_chart_cover K)
  have hj : Subsingleton (Sheaf.H ((restriction j AddCommGrpCat.{0}).obj F) 1) := by
    let e := restrictionCohomology j M 1
    have h := CuspSmallEtaleCohomology.cusp_cyclic_HOne_subsingleton K p ℓ
    exact ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩
  have hk : Subsingleton (Sheaf.H ((restriction k AddCommGrpCat.{0}).obj F) 1) := by
    let e := restrictionCohomology k M 1
    have h := SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K ℓ
    exact ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩
  let eIn := (SmallEtaleCuspHOne.puncturedCuspCyclicHOneEquiv K ℓ hℓ).trans
    ((SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
      (CuspChartIntersection.overlapIsoPuncturedCusp K) M 1).symm.trans
      (restrictionCohomology l M 1).symm)
  let δ := EtaleMayerVietoris.ordinaryConnecting j k l a b hD hc F 1
  have hδ : Function.Injective δ :=
    EtaleMayerVietoris.ordinaryConnecting_injective j k l a b hD hc F 1 hj hk
  let eOut := (cuspHcSuccProjectiveEquiv K M 1).symm
  exact ⟨eOut.toAddMonoidHom.comp (δ.comp eIn.toAddMonoidHom),
    eOut.injective.comp (hδ.comp eIn.injective)⟩

end

end ManuscriptAudit.CuspCompactSupportDegreeTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CuspCompactSupportDegreeTwo.cuspHcTwo_contains_cyclic
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
