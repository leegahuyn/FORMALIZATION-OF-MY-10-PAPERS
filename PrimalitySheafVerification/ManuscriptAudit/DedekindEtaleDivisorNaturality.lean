import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleDivisorCyclePullback
import PrimalitySheafVerification.ManuscriptAudit.DedekindEtaleGenericDivisor
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitNaturality

/-!
# Naturality of the divisor of actual generic-point unit sections

On integral affine charts the actual morphisms of the small étale site
preserve the principal divisor through étale restriction of cycles.
-/

namespace ManuscriptAudit.DedekindEtaleGenericDivisor

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleGenericField DedekindPrincipalDivisor KummerUnitsSheaf
open GenericEtaleUnitSections
open scoped TensorProduct

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B C F : Type) [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field F]
  [Algebra A B] [Algebra A C] [Algebra A F] [Algebra B C] [IsScalarTower A B C]
  [IsFractionRing A F] [Algebra.Etale A B] [Algebra.Etale A C] [Algebra.Etale B C]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Étale restriction of the actual direct-image units commutes with the
finite divisor of each section between integral affine charts. -/
theorem sectionDivisor_restrict (x : genericUnitSectionGroup A B F) :
    AffineEtaleClosedPoints.pullback B C (sectionDivisor A B F x) =
      sectionDivisor A C F ((genericUnitImage A F).obj.map
        (algebraEtaleMap (IsScalarTower.toAlgHom A B C)).op x) := by
  let L := F ⊗[A] B
  let M := F ⊗[A] C
  letI : Field L := (genericFiber_isField A B F).toField
  letI : Field M := (genericFiber_isField A C F).toField
  letI : IsFractionRing B L := genericFiber_isFractionRing A B F
  letI : IsFractionRing C M := genericFiber_isFractionRing A C F
  letI : IsDedekindDomain B := AffineEtaleOverDedekind.isDedekindDomain A B
  letI : IsDedekindDomain C := AffineEtaleOverDedekind.isDedekindDomain A C
  let f := IsScalarTower.toAlgHom A B C
  let ρ : L →+* M := (Algebra.TensorProduct.map (AlgHom.id A F) f).toRingHom
  let e := (genericUnitSectionsIso A B F).hom
  let e' := (genericUnitSectionsIso A C F).hom
  let r := (genericUnitImage A F).obj.map (algebraEtaleMap f).op
  have hρ (b : B) : ρ (algebraMap B L b) = algebraMap C M (algebraMap B C b) := by
    change (Algebra.TensorProduct.map (AlgHom.id A F) f) ((1 : F) ⊗ₜ[A] b) =
      (1 : F) ⊗ₜ[A] f b
    simp
  have h : e' (r x) = Additive.ofMul (Units.map ρ.toMonoidHom (e x).toMul) :=
    ConcreteCategory.congr_hom (genericUnitSectionsIso_naturality A B C F f) x
  change AffineEtaleClosedPoints.pullback B C (principalDivisor B L (e x)) =
    principalDivisor C M (e' (r x))
  rw [h]
  exact AffineEtaleClosedPoints.pullback_principalDivisor B C L M ρ hρ (e x)

end

end ManuscriptAudit.DedekindEtaleGenericDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.DedekindEtaleGenericDivisor.sectionDivisor_restrict
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
