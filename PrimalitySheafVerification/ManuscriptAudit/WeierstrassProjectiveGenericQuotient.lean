import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveGenericUnits
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityDedekind
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericUnitQuotient
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenEtaleMono
import PrimalitySheafVerification.ManuscriptAudit.SheafH1ConnectingExact

/-! The actual projective generic-unit quotient maps onto first unit
cohomology, and its kernel is the image of true rational units. -/

namespace ManuscriptAudit.WeierstrassProjectiveGenericQuotient

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeierstrassProjectiveClosure WeierstrassCartierInfinity WeierstrassInfinityChartAlgebra
open WeierstrassProjectiveGenericPoint WeierstrassProjectiveGenericUnits
open WeierstrassInfinityFunctionField OpenEtaleGenericUnitQuotient
open KummerUnitsSheaf SheafH1Descent SheafH1ConnectingExact
open EtaleTwoOpenHOne WeierstrassInfinityOpenCover

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev X := projectiveScheme W
private abbrev N := Neighborhood W

/-- The native function field with the algebra structure from the actual
infinity open immersion's generic point. -/
def neighborhoodFractionAlgebra : Algebra (N W) W.FunctionField :=
  ((functionFieldEquiv W).symm.toRingHom.comp
    (algebraMap (N W) (FractionRing (N W)))).toAlgebra

local instance : Algebra (N W) W.FunctionField := neighborhoodFractionAlgebra W
local instance : IsDedekindDomain (N W) := WeierstrassInfinityDedekind.neighborhood_isDedekindDomain W
local instance : IsOpenImmersion (neighborhoodOpen W) := neighborhoodOpen_isOpenImmersion W

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1200000 in
theorem neighborhood_isFractionRing : IsFractionRing (N W) W.FunctionField := by
  let e : FractionRing (N W) ≃ₐ[N W] W.FunctionField :=
    { toRingEquiv := (functionFieldEquiv W).symm
      commutes' := fun x => by
        change (functionFieldEquiv W).symm (algebraMap (N W) (FractionRing (N W)) x) =
          (functionFieldEquiv W).symm (algebraMap (N W) (FractionRing (N W)) x)
        rfl }
  exact IsFractionRing.of_algEquiv e

local instance : IsFractionRing (N W) W.FunctionField := neighborhood_isFractionRing W

/-- The true projective map from regular units to the generic-unit direct image. -/
def regularToGeneric : fullCoordinateUnitSheaf (X W) ⟶
    WeierstrassProjectiveGenericUnits.genericUnitImage W :=
  GenericEtaleUnitSections.pullbackToDirectImage (genericPoint W)

private theorem mono_of_genericFactor {Y U Z : Scheme.{0}} (j : U ⟶ Z) [IsOpenImmersion j]
    (g : Y ⟶ U) (f : Y ⟶ Z) (hf : f = g ≫ j)
    [Mono (GenericEtaleUnitSections.pullbackToDirectImage g)] :
    Mono ((OpenEtaleExtension.restriction j AddCommGrpCat.{0}).map
      (GenericEtaleUnitSections.pullbackToDirectImage f)) := by
  subst f
  exact mono_restriction j g

theorem regularToGeneric_mono : Mono (regularToGeneric W) := by
  apply TwoOpenEtaleMono.mono_of_restrictions (neighborhoodOpen W) (affineOpen W)
    (regularToGeneric W) (cover W)
  · letI : Mono (GenericEtaleUnitSections.pullbackToDirectImage (genericToNeighborhood W)) :=
      GenericEtaleUnitSections.genericPointUnitsHom_mono (N W) W.FunctionField
    exact mono_of_genericFactor (neighborhoodOpen W) (genericToNeighborhood W) (genericPoint W)
      (genericPoint_factors_infinity W)
  · letI : Mono (GenericEtaleUnitSections.pullbackToDirectImage (genericToAffine W)) :=
      GenericEtaleUnitSections.genericPointUnitsHom_mono W.CoordinateRing W.FunctionField
    exact mono_restriction (affineOpen W) (genericToAffine W)

local instance : Mono (regularToGeneric W) := regularToGeneric_mono W

/-- The actual sheaf quotient of generic units by regular units on the
projective curve. -/
abbrev quotient := cokernel (regularToGeneric W)
abbrev terminal := identityObject (X W)
private abbrev terminalIsTerminal := MorphismProperty.Over.mkIdTerminal @Etale (X W)

private abbrev seq := ShortComplex.cokernelSequence (regularToGeneric W)

private theorem short_exact : (seq W).ShortExact := by
  refine ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact (regularToGeneric W)) ?_ ?_
  · change Mono (regularToGeneric W)
    infer_instance
  · change Epi (cokernel.π (regularToGeneric W))
    infer_instance

/-- The actual connecting map from projective divisor sections to first
small étale unit cohomology. -/
def divisorConnecting :
    (quotient W).obj.obj (op (terminal W)) →+ Sheaf.H (fullCoordinateUnitSheaf (X W)) 1 :=
  ((short_exact W).extClass.postcomp _ (zero_add 1)).comp
    (Sheaf.H.equiv₀ (quotient W) (terminalIsTerminal W)).symm.toAddMonoidHom

theorem divisorConnecting_surjective : Function.Surjective (divisorConnecting W) := by
  intro c
  have hZero := genericUnitImage_HOne_subsingleton W
  have hc : c.comp (Ext.mk₀ (seq W).f) (add_zero 1) = 0 := hZero.allEq _ _
  let Z := (constantSheaf (X W).smallEtaleTopology AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))
  have h := Ext.covariant_sequence_exact₁' Z (short_exact W) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  obtain ⟨z, hz⟩ := (h c).1 hc
  refine ⟨Sheaf.H.equiv₀ (quotient W) (terminalIsTerminal W) z, ?_⟩
  change ((Sheaf.H.equiv₀ (quotient W) (terminalIsTerminal W)).symm
    (Sheaf.H.equiv₀ (quotient W) (terminalIsTerminal W) z)).comp
      (short_exact W).extClass (zero_add 1) = c
  rw [AddEquiv.symm_apply_apply]
  exact hz

/-- Vanishing of the genuine connecting class is precisely existence of
a global rational unit with that divisor. -/
theorem divisorConnecting_eq_zero (x : (quotient W).obj.obj (op (terminal W))) :
    divisorConnecting W x = 0 ↔
      ∃ z : (WeierstrassProjectiveGenericUnits.genericUnitImage W).obj.obj (op (terminal W)),
        (cokernel.π (regularToGeneric W)).hom.app (op (terminal W)) z = x :=
  connectingSection_eq_zero_iff (regularToGeneric W) (terminalIsTerminal W) x

end

end ManuscriptAudit.WeierstrassProjectiveGenericQuotient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveGenericQuotient.neighborhood_isFractionRing,
      ``ManuscriptAudit.WeierstrassProjectiveGenericQuotient.regularToGeneric_mono,
      ``ManuscriptAudit.WeierstrassProjectiveGenericQuotient.divisorConnecting_surjective,
      ``ManuscriptAudit.WeierstrassProjectiveGenericQuotient.divisorConnecting_eq_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
