import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Etale.Field
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleCohomologyAcyclic
import PrimalitySheafVerification.ManuscriptAudit.GaloisUnitSectionSequence
import PrimalitySheafVerification.ManuscriptAudit.RatFuncFiniteGaloisUnitPositive

/-!
# Positive étale unit cohomology of finite extensions of K(t)

Every étale field chart is a finite extension of the base field, so
Tsen's vanishing for all finite Galois sections applies uniformly.
The geometric skyscraper resolution gives the native sheaf cohomology
vanishing in every positive degree.
-/

namespace ManuscriptAudit.RatFuncTsen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EtaleObjectRestriction FieldEtaleCohomologyAcyclic GaloisCoverAction KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

theorem finiteExtension_etale_units_hasAcyclicGaloisSections
    (K B : Type) [Field K] [IsAlgClosed K] [Field B]
    [Algebra (RatFunc K) B] [FiniteDimensional (RatFunc K) B] :
    HasAcyclicGaloisSections B (fullCoordinateUnitSheaf (Spec (CommRingCat.of B))) := by
  intro F L _ _ _ _ _ j _ n
  let a := Spec.preimage j
  letI : Algebra B F := a.hom.toAlgebra
  have hJ : Etale (Spec.map a) := by
    rw [show Spec.map a = j from Spec.map_preimage j]
    infer_instance
  letI : Algebra.Etale B F := RingHom.etale_algebraMap.mp <| by
    change a.hom.Etale
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hJ
  letI : FiniteDimensional B F := Algebra.FormallyUnramified.finite_of_free B F
  letI : Algebra (RatFunc K) F :=
    ((algebraMap B F).comp (algebraMap (RatFunc K) B)).toAlgebra
  letI : IsScalarTower (RatFunc K) B F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : FiniteDimensional (RatFunc K) F := Module.Finite.trans (R := RatFunc K) B F
  let e := (sectionsFunctor F L).mapIso (restrictionUnitsIso j) ≪≫ unitSectionIso F L
  let eH := (groupCohomology.functor ℤ (L ≃ₐ[F] L) (n + 1)).mapIso e
  exact (ModuleCat.isZero_iff_subsingleton.mpr
    (finiteGalois_units_H_succ_subsingleton K F L n)).of_iso eH

/-- The unit sheaf on every finite extension field of K(t) has zero
actual small étale cohomology in all positive degrees. -/
theorem finiteExtension_etale_units_H_succ_subsingleton
    (K B : Type) [Field K] [IsAlgClosed K] [Field B]
    [Algebra (RatFunc K) B] [FiniteDimensional (RatFunc K) B] (n : ℕ) :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (Spec (CommRingCat.of B))) (n + 1)) :=
  FieldEtaleCohomologyAcyclic.H_succ_subsingleton B _
    (finiteExtension_etale_units_hasAcyclicGaloisSections K B) n

/-- Specialization to K(t). -/
theorem rationalFunction_etale_units_H_succ_subsingleton
    (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (Spec (CommRingCat.of (RatFunc K)))) (n + 1)) :=
  finiteExtension_etale_units_H_succ_subsingleton K (RatFunc K) n

end

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RatFuncTsen.finiteExtension_etale_units_H_succ_subsingleton,
      ``ManuscriptAudit.RatFuncTsen.rationalFunction_etale_units_H_succ_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
