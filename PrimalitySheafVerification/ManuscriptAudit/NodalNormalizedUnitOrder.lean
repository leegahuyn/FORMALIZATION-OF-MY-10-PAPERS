import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspPicard
import PrimalitySheafVerification.ManuscriptAudit.IntegerHomOfDivisible
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeCover
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartUnitOrder
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitSheaf

/-! The order of native unit sections on the overlap detects exactly
extension to the normalized Y chart and vanishes on the polynomial Z chart. -/

namespace ManuscriptAudit.NodalNormalizedUnitOrder

open AlgebraicGeometry CategoryTheory Opposite
open NodalProjectiveNormalization (normalizedNode)
open NodalYChartImmersion (nodeYChart yCoordinateRing xCoeff)
open NodalYChartPrincipalOpen (principalInclusion principalRingHom coordinate_ne_zero)
open NodalYChartOverlap (overlapRing)
open NodalNormalizedNativeCharts
open NodalNormalizedNativeCover
open ProetaleOpenLocalLifts
open ProetaleUnitSheaf (unitSheaf specUnits)
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

abbrev F := unitSheaf (normalizedNode K)

abbrev Y := openObject (yToNormalized K)
abbrev D := overlapObject K
abbrev Z (h2 : (2 : K) ≠ 0) := openObject (zToNormalized K h2)

/-- Native sections on the normalized Y chart are its coordinate units. -/
def yUnits : (F K).obj.obj (op (Y K)) ≃+ Additive (yCoordinateRing K)ˣ :=
  specUnits (CommRingCat.of (yCoordinateRing K)) (𝟙 (nodeYChart K) ≫ yToNormalized K)

/-- Native sections on the overlap are the displayed localization units. -/
def overlapUnits : (F K).obj.obj (op (D K)) ≃+ Additive (overlapRing K)ˣ :=
  specUnits (CommRingCat.of (overlapRing K)) (principalInclusion K ≫ yToNormalized K)

/-- Native sections on the polynomial Z chart are polynomial units. -/
def zUnits (h2 : (2 : K) ≠ 0) : (F K).obj.obj (op (Z K h2)) ≃+ Additive (Polynomial K)ˣ :=
  specUnits (CommRingCat.of (Polynomial K))
    (𝟙 (Spec (CommRingCat.of (Polynomial K))) ≫ zToNormalized K h2)

theorem firstLeg_units (s : (F K).obj.obj (op (Y K))) :
    overlapUnits K ((F K).obj.map (firstLeg K).op s) =
      (ringUnits.map (principalRingHom K)).hom (yUnits K s) := by
  let r := principalRingHom K
  have h : ringUnits.map (Spec.map r).appTop ≫ (ringUnits.mapIso (Scheme.ΓSpecIso _)).hom =
      (ringUnits.mapIso (Scheme.ΓSpecIso _)).hom ≫ ringUnits.map r := by
    simp only [Functor.mapIso_hom, ← Functor.map_comp, Scheme.ΓSpecIso_naturality]
  exact ConcreteCategory.congr_hom h s.down

/-- The native Y restriction is injective since the overlap is localization at a nonzero element. -/
theorem firstLeg_injective : Function.Injective ((F K).obj.map (firstLeg K).op) := by
  intro a b hab
  have h := congrArg (overlapUnits K) hab
  rw [firstLeg_units, firstLeg_units] at h
  apply (yUnits K).injective
  apply Additive.ext
  apply Units.ext
  apply IsLocalization.injective (overlapRing K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (coordinate_ne_zero K))
  exact congrArg (fun s : Additive (overlapRing K)ˣ ↦ (s.toMul : overlapRing K)) h

/-- Integer valuation on actual ambient unit sections over the overlap. -/
def order : (F K).obj.obj (op (D K)) →+ ℤ :=
  (NodalYChartUnitOrder.order K).comp (overlapUnits K).toAddMonoidHom

variable [IsAlgClosed K]

/-- Order zero is equivalent to extension from the actual normalized Y chart. -/
theorem firstLeg_order_exact :
    Function.Exact ((F K).obj.map (firstLeg K).op) (order K) := by
  intro s
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := (NodalYChartUnitOrder.restriction_order_exact K (overlapUnits K s)).mp hs
    refine ⟨(yUnits K).symm a, (overlapUnits K).injective ?_⟩
    rw [firstLeg_units, AddEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨a, rfl⟩
    apply (NodalYChartUnitOrder.restriction_order_exact K _).mpr
    exact ⟨yUnits K a, (firstLeg_units K a).symm⟩

/-- The order vanishes on restrictions from the actual polynomial Z chart,
whose unit group is divisible over an algebraically closed field. -/
theorem secondLeg_order_zero (h2 : (2 : K) ≠ 0)
    (s : (F K).obj.obj (op (Z K h2))) :
    order K ((F K).obj.map (secondLeg K h2).op s) = 0 := by
  let f := ((order K).comp ((F K).obj.map (secondLeg K h2).op).hom).comp
    (zUnits K h2).symm.toAddMonoidHom
  have hDiv (n : ℕ) (hn : 0 < n) :
      Function.Surjective (fun x : Additive (Polynomial K)ˣ ↦ n • x) := by
    intro y
    obtain ⟨x, hx⟩ := CuspPicard.paper2_polynomial_unit_power_surjective K n hn y.toMul
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  have h := IntegerHomOfDivisible.eq_zero f hDiv (zUnits K h2 s)
  change order K ((F K).obj.map (secondLeg K h2).op ((zUnits K h2).symm (zUnits K h2 s))) = 0 at h
  rwa [AddEquiv.symm_apply_apply] at h

end
end ManuscriptAudit.NodalNormalizedUnitOrder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedUnitOrder.firstLeg_units,
      ``ManuscriptAudit.NodalNormalizedUnitOrder.firstLeg_injective,
      ``ManuscriptAudit.NodalNormalizedUnitOrder.firstLeg_order_exact,
      ``ManuscriptAudit.NodalNormalizedUnitOrder.secondLeg_order_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
