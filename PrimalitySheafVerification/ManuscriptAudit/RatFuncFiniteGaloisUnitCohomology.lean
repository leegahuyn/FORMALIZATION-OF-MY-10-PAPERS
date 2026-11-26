import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FiniteIndexGroupCohomology
import PrimalitySheafVerification.ManuscriptAudit.RatFuncPGroupUnitCohomology

/-!
# Unit cohomology of finite Galois extensions over K(t)

Each Sylow subgroup is the Galois group over its fixed field. Its
second unit cohomology vanishes by the p-group argument, so the
finite-index detection theorem gives vanishing on the whole group.
-/

namespace ManuscriptAudit.RatFuncTsen

open CategoryTheory

/-- The actual second group cohomology of the unit representation vanishes
for every finite Galois extension of a finite extension of K(t). -/
theorem finiteGalois_units_HTwo_subsingleton (K F L : Type) [Field K] [IsAlgClosed K] [Field F]
    [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L] :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) := by
  apply FiniteIndexGroupCohomology.subsingleton_of_sylow
  intro p hp P
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup (L ≃ₐ[F] L) := P
  let M := IntermediateField.fixedField S
  letI : Algebra (RatFunc K) M :=
    ((algebraMap F M).comp (algebraMap (RatFunc K) F)).toAlgebra
  letI : IsScalarTower (RatFunc K) F M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : FiniteDimensional (RatFunc K) M := Module.Finite.trans (R := RatFunc K) F M
  letI : IsGalois M L := IsGalois.of_fixed_field L S
  have hP : IsPGroup p (L ≃ₐ[M] L) :=
    P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv S)
  have h := pGroup_units_HTwo_subsingleton K M L p hP
  let e := GaloisSubgroupUnitCohomology.fixedFieldCohomologyIso F L S 2
  have inj : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  exact ⟨fun x y ↦ inj (h.elim _ _)⟩

/-- Specialization to the rational function field itself. -/
theorem rationalFunction_finiteGalois_units_HTwo_subsingleton (K L : Type)
    [Field K] [IsAlgClosed K] [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [IsGalois (RatFunc K) L] :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits (RatFunc K) L) 2) :=
  finiteGalois_units_HTwo_subsingleton K (RatFunc K) L

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RatFuncTsen.finiteGalois_units_HTwo_subsingleton,
      ``ManuscriptAudit.RatFuncTsen.rationalFunction_finiteGalois_units_HTwo_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
