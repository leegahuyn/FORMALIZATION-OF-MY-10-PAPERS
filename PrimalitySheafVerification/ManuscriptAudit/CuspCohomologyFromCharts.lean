import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportDegreeTwo

/-! The native degree shift from the cusp's affine charts and Laurent intersection. -/

namespace ManuscriptAudit.CuspCohomologyFromCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification CuspProperYChart CuspCompactSupportSequence OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

abbrev constantOn (X : Scheme.{0}) (M : AddCommGrpCat.{0}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj M

private def restrictedConstantEquiv {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : AddCommGrpCat.{0}) (d : ℕ) :
    Sheaf.H ((restriction j AddCommGrpCat.{0}).obj (constantOn X M)) d ≃+
      Sheaf.H (constantOn U M) d :=
  ((Sheaf.functorH U.smallEtaleTopology d).mapIso
    ((restrictionConstantIso j).app M)).addCommGroupIsoToAddEquiv

variable (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]

abbrev line := Spec (CommRingCat.of (Polynomial K))
abbrev torus := Spec (CommRingCat.of (LaurentPolynomial K))

theorem projectiveCusp_H_succ_subsingleton (M : AddCommGrpCat.{0}) (n : ℕ)
    (hLine : Subsingleton (Sheaf.H (constantOn (line K) M) n))
    (hLine' : Subsingleton (Sheaf.H (constantOn (line K) M) (n + 1)))
    (hTorus : Subsingleton (Sheaf.H (constantOn (torus K) M) n)) :
    Subsingleton (Sheaf.H (constantOn (projectiveCusp K) M) (n + 1)) := by
  let j := affineOpen K
  let k := lineOpen K
  let l := pullback.fst j k ≫ j
  letI : IsOpenImmersion j := affineOpen_isOpenImmersion K
  letI : IsOpenImmersion k := lineOpen_isOpenImmersion K
  letI : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion (pullback.fst j k ≫ j))
  let F := constantOn (projectiveCusp K) M
  let a := EtaleOpenIntersection.fstLeg j k
  let b := EtaleOpenIntersection.sndLeg j k
  let hD := EtaleOpenIntersection.intersection_isPullback j k
  have hc : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun O : (projectiveCusp K).Opens => (O : Set (projectiveCusp K))) (affine_chart_cover K)
  let eJ (d : ℕ) := (restrictedConstantEquiv j M d).trans
    (CuspSmallEtaleCohomology.normalizationCohomologyEquiv K p M d)
  let eK (d : ℕ) := restrictedConstantEquiv k M d
  let eL := (restrictedConstantEquiv l M n).trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
      (CuspChartIntersection.overlapIsoLaurent K) M n)
  have hj : Subsingleton (Sheaf.H ((restriction j AddCommGrpCat.{0}).obj F) n) :=
    ⟨fun x y => (eJ n).injective (hLine.elim _ _)⟩
  have hk : Subsingleton (Sheaf.H ((restriction k AddCommGrpCat.{0}).obj F) n) :=
    ⟨fun x y => (eK n).injective (hLine.elim _ _)⟩
  have hj' : Subsingleton (Sheaf.H ((restriction j AddCommGrpCat.{0}).obj F) (n + 1)) :=
    ⟨fun x y => (eJ (n + 1)).injective (hLine'.elim _ _)⟩
  have hk' : Subsingleton (Sheaf.H ((restriction k AddCommGrpCat.{0}).obj F) (n + 1)) :=
    ⟨fun x y => (eK (n + 1)).injective (hLine'.elim _ _)⟩
  have hl : Subsingleton (Sheaf.H ((restriction l AddCommGrpCat.{0}).obj F) n) :=
    ⟨fun x y => eL.injective (hTorus.elim _ _)⟩
  let δ := EtaleMayerVietoris.ordinaryConnecting j k l a b hD hc F n
  have hδ : Function.Surjective δ :=
    (EtaleMayerVietoris.ordinaryConnecting_bijective j k l a b hD hc F n hj hk hj' hk').2
  exact ⟨fun x y => by
    obtain ⟨x', rfl⟩ := hδ x
    obtain ⟨y', rfl⟩ := hδ y
    exact congrArg δ (hl.elim _ _)⟩

theorem cuspHc_succ_subsingleton (M : AddCommGrpCat.{0}) (n : ℕ)
    (hLine : Subsingleton (Sheaf.H (constantOn (line K) M) n))
    (hLine' : Subsingleton (Sheaf.H (constantOn (line K) M) (n + 1)))
    (hTorus : Subsingleton (Sheaf.H (constantOn (torus K) M) n)) :
    Subsingleton (cuspHc K M (n + 1)) := by
  let h := projectiveCusp_H_succ_subsingleton K p M n hLine hLine' hTorus
  let e := cuspHcSuccProjectiveEquiv K M n
  exact ⟨fun x y => e.injective (h.elim _ _)⟩

end
end ManuscriptAudit.CuspCohomologyFromCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCohomologyFromCharts.projectiveCusp_H_succ_subsingleton,
      ``ManuscriptAudit.CuspCohomologyFromCharts.cuspHc_succ_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
