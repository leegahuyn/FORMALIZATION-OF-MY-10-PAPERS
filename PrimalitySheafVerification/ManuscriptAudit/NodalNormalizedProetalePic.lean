import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedUnitOrder
import PrimalitySheafVerification.ManuscriptAudit.ProetalePIDUnitHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleTwoOpenHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitRestriction
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCohomologyNoTorsion
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenSectionGluing

/-! For the actual normalized projective node, native units have
divisible global sections and torsion-free degree-one cohomology. -/

namespace ManuscriptAudit.NodalNormalizedProetalePic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveNormalization (normalizedNode)
open NodalNormalizedNativeCharts NodalNormalizedNativeCover
open NodalNormalizedUnitOrder
open NodalYChartImmersion (yCoordinateRing)
open ProetaleOpenLocalLifts
open OpenProetaleExtension (restriction)
open ProetaleUnitSheaf (unitSheaf)
open ProetaleUnitRestriction (restrictionUnitsIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)

private abbrev X := normalizedNode K
private abbrev J := Scheme.ProEt.topology (X K)
private abbrev G := AddCommGrpCat.{1}
private abbrev C := Sheaf (J K) G
private abbrev T := identityObject (X K)

local instance : EnoughInjectives (C K) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := C K)

private abbrev u := openArrow (yToNormalized K)
private abbrev v := openArrow (zToNormalized K h2)

private theorem restricted_HOne_subsingleton {W : Scheme.{0}} (j : W ⟶ X K) [IsOpenImmersion j]
    (hW : Subsingleton (Sheaf.H (unitSheaf W) 1)) :
    Subsingleton (Sheaf.H ((restriction j G).obj (F K)) 1) := by
  let H : Sheaf (Scheme.ProEt.topology W) G ⥤ G := Sheaf.functorH (Scheme.ProEt.topology W) 1
  let e := (H.mapIso (restrictionUnitsIso j)).addCommGroupIsoToAddEquiv
  exact ⟨fun a b ↦ e.injective (hW.elim _ _)⟩

/-- The global units of the actual normalization restrict bijectively
to the units of its polynomial chart. -/
theorem globalUnits_restrict_bijective :
    Function.Bijective ((F K).obj.map (v K h2).op) :=
  TwoOpenSectionGluing.restriction_bijective (F K) (u K) (v K h2) (firstLeg K) (secondLeg K h2)
    (native_overlap_isPullback K h2)
    (ProetaleTwoOpenHOne.twoOpenCover (yToNormalized K) (zToNormalized K h2) (charts_cover K h2))
    (firstLeg_injective K) (fun b ↦ (firstLeg_order_exact K _).mp (secondLeg_order_zero K h2 b))

/-- Every global regular unit of the actual normalization has a
positive-order root in the global unit group. -/
theorem globalUnits_nsmul_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun a : (F K).obj.obj (op (T K)) ↦ n • a) := by
  let e := AddEquiv.ofBijective ((F K).obj.map (v K h2).op).hom
    (globalUnits_restrict_bijective K h2)
  let q := e.trans (zUnits K h2)
  intro a
  obtain ⟨b, hb⟩ := CuspPicard.paper2_polynomial_unit_power_surjective K n hn (q a).toMul
  refine ⟨q.symm (Additive.ofMul b), q.injective ?_⟩
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  exact congrArg Additive.ofMul hb

set_option maxHeartbeats 1600000 in
/-- Native degree-one unit cohomology of the actual normalization is
torsion-free, using the integer order on its actual overlap. -/
theorem units_HOne_eq_zero_of_nsmul_eq_zero (n : ℕ) (hn : 0 < n)
    (a : Sheaf.H (F K) 1) (ha : n • a = 0) : a = 0 := by
  let I := Injective.under (F K)
  let i : F K ⟶ I := Injective.ι (F K)
  let hT : IsTerminal (T K) := MorphismProperty.Over.mkIdTerminal @WeaklyEtale (X K)
  have hY := restricted_HOne_subsingleton K (yToNormalized K)
    (ProetalePIDUnitHOne.HOne_subsingleton (yCoordinateRing K))
  have hZ := restricted_HOne_subsingleton K (zToNormalized K h2)
    (ProetalePIDUnitHOne.HOne_subsingleton (Polynomial K))
  exact TwoOpenCohomologyNoTorsion.eq_zero_of_nsmul_eq_zero i hT
    (u K) (v K h2) (firstLeg K) (secondLeg K h2) (native_overlap_isPullback K h2)
    (ProetaleTwoOpenHOne.twoOpenCover (yToNormalized K) (zToNormalized K h2) (charts_cover K h2))
    (order K) (firstLeg_order_exact K) (secondLeg_order_zero K h2)
    (restrictedCokernel_sections_surjective (yToNormalized K) i hY)
    (restrictedCokernel_sections_surjective (zToNormalized K h2) i hZ) hn a ha

end
end ManuscriptAudit.NodalNormalizedProetalePic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedProetalePic.globalUnits_restrict_bijective,
      ``ManuscriptAudit.NodalNormalizedProetalePic.globalUnits_nsmul_surjective,
      ``ManuscriptAudit.NodalNormalizedProetalePic.units_HOne_eq_zero_of_nsmul_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
