import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Ideal
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorFullExact
import PrimalitySheafVerification.ManuscriptAudit.AffineLineOpenDivisorHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericImageRestriction
import PrimalitySheafVerification.ManuscriptAudit.RatFuncGenericImageHigher
import PrimalitySheafVerification.ManuscriptAudit.RatFuncPrincipalOpen
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-! Ordinary étale H² vanishing on actual nonempty principal opens of the affine line. -/

namespace ManuscriptAudit.PrincipalOpenEtaleHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineLineDivisorSheaf EtaleObjectRestriction GenericEtaleUnitSections KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A (f : Polynomial K) := Localization.Away f
private abbrev U (f : Polynomial K) := Spec (CommRingCat.of (A K f))

private abbrev openMap (f : Polynomial K) : U K f ⟶ AffineLineDivisorSheaf.X K :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (A K f)))

private instance openMap_isOpenImmersion (f : Polynomial K) :
    IsOpenImmersion (openMap K f) := IsOpenImmersion.of_isLocalization f

/-- A polynomial principal-open ring is a principal ideal ring. -/
theorem principalIdealRing (f : Polynomial K) : IsPrincipalIdealRing (A K f) where
  principal I := by
    rw [← IsLocalization.map_under (Submonoid.powers f) (A K f) I]
    infer_instance

set_option maxHeartbeats 4500000 in
/-- The regular unit sheaf has zero H² on a nonempty actual principal open. -/
theorem units_HTwo_subsingleton (f : Polynomial K) (hf : f ≠ 0) :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (U K f)) 2) := by
  let p := openMap K f
  let B := A K f
  have hM : Submonoid.powers f ≤ nonZeroDivisors (Polynomial K) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hf)
  letI : IsDomain B := IsLocalization.isDomain_localization hM
  letI : IsIntegrallyClosed B := isIntegrallyClosed_of_isLocalization B (Submonoid.powers f) hM
  let a := RatFuncPrincipalOpen.toRatFunc K f hf
  letI : Algebra B (RatFunc K) := a.toAlgebra
  letI : IsScalarTower (Polynomial K) B (RatFunc K) := IsScalarTower.of_algebraMap_eq
    (fun x ↦ (RatFuncPrincipalOpen.toRatFunc_algebraMap K f hf x).symm)
  letI : IsFractionRing B (RatFunc K) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) B (RatFunc K)
  let j : Spec (CommRingCat.of (RatFunc K)) ⟶ U K f :=
    Spec.map (CommRingCat.ofHom (algebraMap B (RatFunc K)))
  let η := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (RatFunc K)))
  have hj : j ≫ p = η := by
    change Spec.map (CommRingCat.ofHom (algebraMap B (RatFunc K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B)) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (RatFuncPrincipalOpen.toRatFunc_algebraMap K f hf)
  let R := restriction p
  letI : R.IsLeftAdjoint := (restrictionAdjunction p).isLeftAdjoint
  letI : PreservesFiniteLimits R := restriction_preservesFiniteLimits p
  letI : R.Additive := R.additive_of_preserves_binary_products
  let S := (divisorSequence K (RatFunc K)).map R
  have hS : S.ShortExact := (divisorSequence_shortExact K (RatFunc K)).map_of_exact R
  have hDiv : Subsingleton (Sheaf.H S.X₃ 1) :=
    restrictedDivisor_HOne_subsingleton K (CommRingCat.of B) p
  have hGeneric : Subsingleton (Sheaf.H S.X₂ 2) := by
    let M := fullCoordinateUnitSheaf (Spec (CommRingCat.of (RatFunc K)))
    change Subsingleton (Sheaf.H
      (R.obj ((SmallEtaleBaseChange.directImage η AddCommGrpCat.{0}).obj M)) 2)
    rw [← hj]
    let e := OpenEtaleGenericImageRestriction.restrictionDirectImageIso p j M
    let eH := ((Sheaf.functorH (U K f).smallEtaleTopology 2).mapIso e).addCommGroupIsoToAddEquiv
    have h := RatFuncTsen.genericUnitImage_H_succ_subsingleton K B 1
    exact ⟨fun x y ↦ eH.injective (h.elim _ _)⟩
  have hi := SheafShortExactSections.HTwo_map_injective_of_HOne S hS hDiv
  let e := ((Sheaf.functorH (U K f).smallEtaleTopology 2).mapIso
    (restrictionUnitsIso p)).addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ e.symm.injective (hi (hGeneric.elim _ _))⟩

/-- The actual cyclic constant sheaf of invertible order has zero H²
on a nonempty principal open of the affine line. -/
theorem cyclic_HTwo_subsingleton (f : Polynomial K) (hf : f ≠ 0)
    (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf (U K f).smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 2) := by
  let B := A K f
  letI : IsDomain B := IsLocalization.isDomain_localization (M := Submonoid.powers f) (by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hf))
  letI : IsPrincipalIdealRing B := principalIdealRing K f
  let k : U K f ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K B))
  letI : NeZero d := NeZero.of_neZero_natCast K
  let S := KummerRelativeFull.sequence (U K f) d
  have hS : S.ShortExact := KummerRelativeFull.sequence_shortExact k d (Nat.pos_of_ne_zero (NeZero.ne d))
  let e := KummerRelativeFull.unitsIso (X := U K f) d
  let H (n : ℕ) := ((Sheaf.functorH (U K f).smallEtaleTopology n).mapIso e).addCommGroupIsoToAddEquiv
  have h₃ : Subsingleton (Sheaf.H S.X₃ 1) := by
    have h := unitHOne_subsingleton_of_pid B
    exact ⟨fun x y ↦ (H 1).symm.injective (h.elim _ _)⟩
  have h₂ : Subsingleton (Sheaf.H S.X₂ 2) := by
    have h := units_HTwo_subsingleton K f hf
    exact ⟨fun x y ↦ (H 2).symm.injective (h.elim _ _)⟩
  let eRoots : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let eCoefficients := (constantSheaf (U K f).smallEtaleTopology AddCommGrpCat.{0}).mapIso
    (eRoots.toAddCommGrpIso :
      KummerConstantCoefficients.coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let eFirst := eCoefficients.symm ≪≫ KummerRelativeFull.firstIso (d := d) k
  let eH := ((Sheaf.functorH (U K f).smallEtaleTopology 2).mapIso eFirst).addCommGroupIsoToAddEquiv
  have hi := SheafShortExactSections.HTwo_map_injective_of_HOne S hS h₃
  exact ⟨fun x y ↦ eH.injective (hi (h₂.elim _ _))⟩

end

end ManuscriptAudit.PrincipalOpenEtaleHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PrincipalOpenEtaleHTwo.units_HTwo_subsingleton,
      ``ManuscriptAudit.PrincipalOpenEtaleHTwo.cyclic_HTwo_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
