import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportDegreeTwo
import PrimalitySheafVerification.ManuscriptAudit.KummerCohomologyDegreeTwo

/-!
# The native obstruction to exhausting cusp compactly supported H²

The first Mayer–Vietoris map injects the full cyclic coefficient group.
Its cokernel embeds into two copies of the affine-line unit-sheaf torsion.
The two targets come from the actual unpunctured cusp chart, by
normalization invariance, and the actual affine-line chart.
-/

namespace ManuscriptAudit.CuspCompactSupportDegreeTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification CuspProperYChart CuspCompactSupportSequence
open KummerCohomologyDegreeTwo OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

private abbrev C (X : Scheme.{0}) (M : AddCommGrpCat.{0}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj M

private def restrictionEquiv {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : AddCommGrpCat.{0}) (d : ℕ) :
    Sheaf.H ((restriction j AddCommGrpCat.{0}).obj (C X M)) d ≃+
      Sheaf.H (C U M) d :=
  ((Sheaf.functorH U.smallEtaleTopology d).mapIso
    ((restrictionConstantIso j).app M)).addCommGroupIsoToAddEquiv

/-- Degree-two affine-line unit-sheaf classes killed by the coefficient order. -/
abbrev affineLineUnitTorsion (K : Type) [Field K] (ℓ : ℕ) :=
  killedBy (Sheaf.H (KummerSheafSequence.unitSheaf (Spec (CommRingCat.of (Polynomial K)))) 2) ℓ

/-- The cyclic overlap group embeds in actual cusp compactly supported H².
Its image is the kernel of the two actual chart restrictions, expressed as
affine-line Kummer unit classes. -/
theorem cuspHcTwo_exact_with_affineUnitTorsion (K : Type) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (ℓ : ℕ) [NeZero (ℓ : K)] (hℓ : 2 ≤ ℓ) :
    ∃ (f : ZMod ℓ →+ cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2)
      (g : cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2 →+
        (affineLineUnitTorsion K ℓ × affineLineUnitTorsion K ℓ)),
      Function.Injective f ∧ Function.Exact f g := by
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
    let e := restrictionEquiv j M 1
    have h := CuspSmallEtaleCohomology.cusp_cyclic_HOne_subsingleton K p ℓ
    exact ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩
  have hk : Subsingleton (Sheaf.H ((restriction k AddCommGrpCat.{0}).obj F) 1) := by
    let e := restrictionEquiv k M 1
    have h := SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K ℓ
    exact ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩
  let eIn := (SmallEtaleCuspHOne.puncturedCuspCyclicHOneEquiv K ℓ hℓ).trans
    ((SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
      (CuspChartIntersection.overlapIsoPuncturedCusp K) M 1).symm.trans
      (restrictionEquiv l M 1).symm)
  let δ := EtaleMayerVietoris.ordinaryConnecting j k l a b hD hc F 1
  have hδ : Function.Injective δ :=
    EtaleMayerVietoris.ordinaryConnecting_injective j k l a b hD hc F 1 hj hk
  let eOut := cuspHcSuccProjectiveEquiv K M 1
  let Q := EtaleMayerVietoris.ordinaryOpenCoverSequence j k l a b hD hc F 1
  have hQ := EtaleMayerVietoris.ordinaryOpenCoverSequence_exact j k l a b hD hc F 1
  let r := (Q.map' 3 4).hom
  have hNative : Function.Exact δ r := by
    have h := hQ.exact' 2 3 4
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  let eT := affineLineCyclicHTwoEquiv K ℓ
  let eJ := (restrictionEquiv j M 2).trans
    ((CuspSmallEtaleCohomology.normalizationCohomologyEquiv K p M 2).trans eT)
  let eK := (restrictionEquiv k M 2).trans eT
  let AJ := AddCommGrpCat.of (Sheaf.H ((restriction j AddCommGrpCat.{0}).obj F) 2)
  let AK := AddCommGrpCat.of (Sheaf.H ((restriction k AddCommGrpCat.{0}).obj F) 2)
  let eCharts := ((AddCommGrpCat.biprodIsoProd AJ AK).addCommGroupIsoToAddEquiv).trans
    (eJ.prodCongr eK)
  refine ⟨eOut.symm.toAddMonoidHom.comp (δ.comp eIn.toAddMonoidHom),
    eCharts.toAddMonoidHom.comp (r.comp eOut.toAddMonoidHom),
    eOut.symm.injective.comp (hδ.comp eIn.injective), ?_⟩
  intro x
  change eCharts (r (eOut x)) = 0 ↔ ∃ y, eOut.symm (δ (eIn y)) = x
  constructor
  · intro hx
    have hx' : r (eOut x) = 0 := eCharts.injective (hx.trans eCharts.map_zero.symm)
    obtain ⟨z, hz⟩ := (hNative (eOut x)).1 hx'
    refine ⟨eIn.symm z, eOut.injective ?_⟩
    simpa only [AddEquiv.apply_symm_apply] using hz
  · rintro ⟨y, hy⟩
    have hs : δ (eIn y) = eOut x := by
      simpa only [AddEquiv.apply_symm_apply] using congrArg eOut hy
    have hx' : r (eOut x) = 0 := (hNative (eOut x)).2 ⟨eIn y, hs⟩
    rw [hx', map_zero]

/-- The quotient by the cyclic overlap classes injects into the two affine-line
Kummer torsion groups. -/
theorem cuspHcTwo_quotient_injects_into_affineUnitTorsion (K : Type) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (ℓ : ℕ) [NeZero (ℓ : K)] (hℓ : 2 ≤ ℓ) :
    ∃ f : ZMod ℓ →+ cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2,
      Function.Injective f ∧
        ∃ g : (cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2 ⧸ f.range) →+
          (affineLineUnitTorsion K ℓ × affineLineUnitTorsion K ℓ), Function.Injective g := by
  obtain ⟨f, g, hf, hExact⟩ := cuspHcTwo_exact_with_affineUnitTorsion K p ℓ hℓ
  have h : f.range = g.ker := by
    ext x
    change (∃ y, f y = x) ↔ g x = 0
    exact (hExact x).symm
  refine ⟨f, hf, ?_⟩
  rw [h]
  exact ⟨QuotientAddGroup.kerLift g, QuotientAddGroup.kerLift_injective g⟩

end

end ManuscriptAudit.CuspCompactSupportDegreeTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspCompactSupportDegreeTwo.cuspHcTwo_exact_with_affineUnitTorsion,
      ``ManuscriptAudit.CuspCompactSupportDegreeTwo.cuspHcTwo_quotient_injects_into_affineUnitTorsion] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
