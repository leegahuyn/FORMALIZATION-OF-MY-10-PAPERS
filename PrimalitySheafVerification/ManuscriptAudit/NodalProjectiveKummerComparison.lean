import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineToOverlapHOneZero
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartHOneCokernel
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients

/-! The actual Kummer sheaf on the proper node identifies with literal cyclic coefficients. -/

namespace ManuscriptAudit.NodalProjectiveKummerComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (affineOpen projectiveNode projectiveNodeToBase)
open NodalProperYChart (chartOpen)
open NodalYChartHOneCokernel (F)
open EtaleOpenIntersection (fstLeg)
open EtaleMayerVietoris (terminalCohomologyIso)
open OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.{0}
private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)
abbrev C (X : Scheme.{0}) (d : ℕ) := (constantSheaf X.smallEtaleTopology A).obj (M d)

/-- The native Kummer kernel is the literal cyclic coefficient sheaf. -/
def comparison (d : ℕ) [NeZero (d : K)] : C (projectiveNode K) d ≅ F K d := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  let e : KummerConstantCoefficients.coefficientGroup K d ≅ M d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive.toAddCommGrpIso
  exact (constantSheaf (projectiveNode K).smallEtaleTopology A).mapIso e.symm ≪≫
    KummerRelativeFull.firstIso (d := d) (projectiveNodeToBase K)

/-- Actual Kummer cohomology on an open chart agrees with ordinary cyclic cohomology there. -/
def chartCohomologyEquiv {U : Scheme.{0}} (j : U ⟶ projectiveNode K) [IsOpenImmersion j]
    (d : ℕ) [NeZero (d : K)] (n : ℕ) :
    (F K d).H' n (Scheme.Etale.mk j) ≃+ Sheaf.H (C U d) n := by
  let e := (Sheaf.cohomologyPresheafFunctor (projectiveNode K).smallEtaleTopology n).mapIso
    (comparison K d)
  let e₁ := (e.app (op (Scheme.Etale.mk j))).addCommGroupIsoToAddEquiv.symm
  let e₂ := openCohomologyPresheafEquiv j (C (projectiveNode K) d) n
  let e₃ := ((Sheaf.functorH U.smallEtaleTopology n).mapIso
    ((restrictionConstantIso j).app (M d))).addCommGroupIsoToAddEquiv
  exact e₁.trans (e₂.trans e₃)

/-- Terminal Kummer cohomology is ordinary proper cyclic cohomology. -/
def terminalCohomologyEquiv (d : ℕ) [NeZero (d : K)] (n : ℕ) :
    (F K d).H' n (EtaleTwoOpenHOne.identityObject (projectiveNode K)) ≃+
      Sheaf.H (C (projectiveNode K) d) n := by
  let e := (Sheaf.cohomologyPresheafFunctor (projectiveNode K).smallEtaleTopology n).mapIso
    (comparison K d)
  let e₁ := (e.app (op (EtaleTwoOpenHOne.identityObject (projectiveNode K)))).addCommGroupIsoToAddEquiv.symm
  exact e₁.trans (terminalCohomologyIso (C (projectiveNode K) d) n).addCommGroupIsoToAddEquiv

/-- The zero affine overlap restriction remains zero under the actual Kummer comparison. -/
theorem affine_leg_eq_zero (h2 : (2 : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] :
    (((F K ℓ).cohomologyPresheaf 1).map (fstLeg (affineOpen K) (chartOpen K)).op).hom = 0 := by
  let a := fstLeg (affineOpen K) (chartOpen K)
  let P := (C (projectiveNode K) ℓ).cohomologyPresheaf 1
  let Q := (F K ℓ).cohomologyPresheaf 1
  let e := (Sheaf.cohomologyPresheafFunctor (projectiveNode K).smallEtaleTopology 1).mapIso
    (comparison K ℓ)
  have hConst : P.map a.op = 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun (NodalAffineToOverlapHOneZero.restriction_eq_zero K ℓ h2) x
  have hn : P.map a.op ≫ e.hom.app (op (EtaleOpenIntersection.intersection (affineOpen K) (chartOpen K))) = e.hom.app (op (Scheme.Etale.mk (affineOpen K))) ≫ Q.map a.op := by
    exact e.hom.naturality a.op
  have hMap : Q.map a.op = 0 := by
    apply (cancel_epi (e.hom.app (op (Scheme.Etale.mk (affineOpen K))))).mp
    rw [← hn, hConst, zero_comp, comp_zero]
  exact congrArg (fun g ↦ g.hom) hMap

end
end ManuscriptAudit.NodalProjectiveKummerComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveKummerComparison.chartCohomologyEquiv,
      ``ManuscriptAudit.NodalProjectiveKummerComparison.terminalCohomologyEquiv,
      ``ManuscriptAudit.NodalProjectiveKummerComparison.affine_leg_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
