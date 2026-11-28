import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrincipalBoundary
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineDedekind
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityPuncture

/-! The affine neighborhood of the actual rational Cartier boundary is Dedekind. -/

namespace ManuscriptAudit.WeierstrassInfinityDedekind

open WeierstrassCurve.Affine
open WeierstrassInfinityChartAlgebra WeierstrassInfinityOriginIdeal
open WeierstrassInfinityChartCoordinates (affineY)
open WeierstrassInfinityChartOverlap (YOverlap ZOverlap overlapEquiv toZChart toZOverlap)
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev C := WeierstrassInfinityChartAlgebra.Ring W
private abbrev Z := ZOverlap W
private abbrev N := Neighborhood W

private theorem affineY_ne_zero : affineY W ≠ 0 := by
  simpa only [affineY, WeierstrassCurve.Affine.CoordinateRing.YClass, map_zero, sub_zero] using
    (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero (W' := W) (0 : Polynomial K))

private theorem zOverlap_dedekind : IsDedekindDomain (Z W) := by
  letI : IsDedekindDomain W.CoordinateRing :=
    WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W
  letI : IsDomain (Z W) := Localization.Away.isDomain (affineY_ne_zero W)
  exact IsLocalization.isDedekindDomain W.CoordinateRing
    (powers_le_nonZeroDivisors_of_noZeroDivisors (affineY_ne_zero W)) (Z W)

private theorem bracket_ne_zero : bracket W ≠ 0 := by
  intro h
  exact one_ne_zero (by rw [← origin_bracket W, h, map_zero])

private theorem neighborhood_isDomain : IsDomain (N W) := by
  letI : IsDomain (Z W) := Localization.Away.isDomain (affineY_ne_zero W)
  letI : IsDomain (C W) :=
    Function.Injective.isDomain (toZChart W).toRingHom
      (WeierstrassInfinityChartImage.toZChart_injective W)
  exact Localization.Away.isDomain (bracket_ne_zero W)

private theorem neighborhood_noetherian : IsNoetherianRing (N W) := by
  letI : IsNoetherianRing (C W) :=
    inferInstanceAs (IsNoetherianRing (AdjoinRoot (equation W)))
  exact IsLocalization.isNoetherianRing (Submonoid.powers (bracket W)) (N W) inferInstance

private theorem boundary_principal (P : Ideal (N W)) (hP : P.IsPrime) (hz : localZ W ∈ P) :
    P.IsPrincipal := by
  let g := localOrigin W
  have hg : Function.Surjective g := by
    intro a
    exact ⟨algebraMap K (N W) a, g.commutes a⟩
  have hMax : (RingHom.ker g.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective g.toRingHom hg
  have hRelation : localZ W * algebraMap (C W) (N W) (bracket W) = localX W ^ 3 := by
    simpa only [localX, localZ, map_mul, map_pow] using
      congrArg (algebraMap (C W) (N W)) (relation W)
  have hx : localX W ∈ P := by
    apply hP.mem_of_pow_mem 3
    rw [← hRelation]
    exact P.mul_mem_right _ hz
  have hLe : RingHom.ker g.toRingHom ≤ P := by
    change RingHom.ker (localOrigin W).toRingHom ≤ P
    rw [localOrigin_ker]
    exact P.span_singleton_le_iff_mem.mpr hx
  have hEq := hMax.eq_of_le hP.ne_top hLe
  refine ⟨localX W, ?_⟩
  exact hEq.symm.trans (localOrigin_ker W)

/-- The actual Y-chart affine neighborhood of the point at infinity is
Dedekind. Away from its principal boundary it is a localization of the
smooth affine chart, and the omitted ideal is the literal origin ideal. -/
theorem neighborhood_isDedekindDomain : IsDedekindDomain (N W) := by
  letI : IsDomain (N W) := neighborhood_isDomain W
  letI : IsNoetherianRing (N W) := neighborhood_noetherian W
  letI : IsDedekindDomain (Z W) := zOverlap_dedekind W
  letI hCZ : Algebra (C W) (Z W) := (toZChart W).toRingHom.toAlgebra
  have hChart : IsLocalization.Away (z W) (Z W) := by
    apply IsLocalization.isLocalization_of_algEquiv (S := YOverlap W) (Submonoid.powers (z W))
    refine AlgEquiv.ofCommutes (overlapEquiv W).toRingEquiv ?_
    intro a
    change toZOverlap W (algebraMap (C W) (YOverlap W) a) = toZChart W a
    unfold toZOverlap
    rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl
  letI := hChart
  let b := toZChart W (bracket W)
  let T := Localization.Away b
  have hb : b ≠ 0 := fun h => bracket_ne_zero W
    ((WeierstrassInfinityChartImage.toZChart_injective W) (h.trans (map_zero _).symm))
  letI : IsDomain T := Localization.Away.isDomain hb
  letI : IsDedekindDomain T := IsLocalization.isDedekindDomain (Z W)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hb) T
  letI hZT : Algebra (Z W) T := inferInstance
  letI hCT : Algebra (C W) T := ((algebraMap (Z W) T).comp (algebraMap (C W) (Z W))).toAlgebra
  letI : SMul (C W) (Z W) := hCZ.toSMul
  letI : SMul (Z W) T := hZT.toSMul
  letI : SMul (C W) T := hCT.toSMul
  letI : IsScalarTower (C W) (Z W) T := IsScalarTower.of_algebraMap_eq' rfl
  let f : N W →ₐ[C W] T :=
    IsLocalization.Away.liftAlgHom (bracket W) (f := Algebra.ofId (C W) T)
      (IsLocalization.Away.algebraMap_isUnit (S := T) b)
  letI hNT : Algebra (N W) T := f.toRingHom.toAlgebra
  letI : SMul (N W) T := hNT.toSMul
  letI : SMul (C W) (N W) := (inferInstance : Algebra (C W) (N W)).toSMul
  letI : IsScalarTower (C W) (N W) T :=
    IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  letI : IsLocalization.Away (localZ W) T :=
    IsLocalization.Away.commutes (N W) (Z W) T (bracket W) (z W)
  have hz : localZ W ≠ 0 := by
    intro h
    have hUnit := IsLocalization.Away.algebraMap_isUnit (S := T) (localZ W)
    rw [h, map_zero] at hUnit
    exact not_isUnit_zero hUnit
  exact DedekindPrincipalBoundary.of_open (S := T) (localZ W) hz (boundary_principal W)

end

end ManuscriptAudit.WeierstrassInfinityDedekind

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.WeierstrassInfinityDedekind.neighborhood_isDedekindDomain
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
