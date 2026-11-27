import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Ideal
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorFullExact
import PrimalitySheafVerification.ManuscriptAudit.AffineLineOpenDivisorHigher
import PrimalitySheafVerification.ManuscriptAudit.KummerCohomologyVanishing
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenEtaleHTwo
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericImageRestriction
import PrimalitySheafVerification.ManuscriptAudit.RatFuncGenericImageHigher
import PrimalitySheafVerification.ManuscriptAudit.RatFuncPrincipalOpen
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-! All positive unit-sheaf and higher cyclic étale cohomology of the actual principal open. -/

namespace ManuscriptAudit.PrincipalOpenEtaleAcyclic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineLineDivisorSheaf EtaleObjectRestriction GenericEtaleUnitSections KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

abbrev A (f : Polynomial K) := Localization.Away f
abbrev U (f : Polynomial K) := Spec (CommRingCat.of (A K f))

private abbrev openMap (f : Polynomial K) : U K f ⟶ AffineLineDivisorSheaf.X K :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (A K f)))

private instance openMap_isOpenImmersion (f : Polynomial K) :
    IsOpenImmersion (openMap K f) := IsOpenImmersion.of_isLocalization f

theorem units_H_succ_subsingleton (f : Polynomial K) (hf : f ≠ 0) (n : ℕ) :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (U K f)) (n + 1)) := by
  let B := A K f
  have hM : Submonoid.powers f ≤ nonZeroDivisors (Polynomial K) := by
    rintro _ ⟨i, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero i hf)
  letI : IsDomain B := IsLocalization.isDomain_localization hM
  cases n with
  | zero =>
    letI : IsPrincipalIdealRing B := PrincipalOpenEtaleHTwo.principalIdealRing K f
    exact KummerUnitsSheaf.unitHOne_subsingleton_of_pid B
  | succ n =>
    let p := openMap K f
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
    have hDiv : Subsingleton (Sheaf.H S.X₃ (n + 1)) :=
      restrictedDivisor_H_succ_subsingleton K (CommRingCat.of B) p n
    have hGeneric : Subsingleton (Sheaf.H S.X₂ (n + 2)) := by
      let M := fullCoordinateUnitSheaf (Spec (CommRingCat.of (RatFunc K)))
      change Subsingleton (Sheaf.H
        (R.obj ((SmallEtaleBaseChange.directImage η AddCommGrpCat.{0}).obj M)) (n + 2))
      rw [← hj]
      let e := OpenEtaleGenericImageRestriction.restrictionDirectImageIso p j M
      let eH := ((Sheaf.functorH (U K f).smallEtaleTopology (n + 2)).mapIso e).addCommGroupIsoToAddEquiv
      have h := RatFuncTsen.genericUnitImage_H_succ_subsingleton K B (n + 1)
      exact ⟨fun x y ↦ eH.injective (h.elim _ _)⟩
    let h := SheafCohomologyVanishingLeft.H_succ_subsingleton S hS (n + 1) hDiv hGeneric
    let e := ((Sheaf.functorH (U K f).smallEtaleTopology (n + 2)).mapIso
      (restrictionUnitsIso p)).addCommGroupIsoToAddEquiv
    exact ⟨fun x y ↦ e.symm.injective (h.elim _ _)⟩

theorem cyclic_H_add_two_subsingleton (f : Polynomial K) (hf : f ≠ 0)
    (d : ℕ) [NeZero (d : K)] (n : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (U K f).smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) (n + 2)) := by
  let k : U K f ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (A K f)))
  exact KummerCohomologyVanishing.cyclic_H_succ_subsingleton k d (n + 1)
    (units_H_succ_subsingleton K f hf n) (units_H_succ_subsingleton K f hf (n + 1))

end
end ManuscriptAudit.PrincipalOpenEtaleAcyclic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PrincipalOpenEtaleAcyclic.units_H_succ_subsingleton,
      ``ManuscriptAudit.PrincipalOpenEtaleAcyclic.cyclic_H_add_two_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
