import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Unit cohomology for subgroups and their fixed fields

Restricting the original unit representation to a subgroup is the
same action as that of the Galois group over the subgroup's fixed
field. Hilbert 90 then gives degree-one vanishing for every subgroup.
-/

namespace ManuscriptAudit.GaloisSubgroupUnitCohomology

open CategoryTheory Rep groupCohomology

noncomputable section

variable (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]

/-- Shifting the base field to the fixed field identifies the actual
restricted unit cohomology groups. -/
def fixedFieldCohomologyIso (S : Subgroup (L ≃ₐ[F] L)) (n : ℕ) :
    groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits F L)) n ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) n := by
  let B := Rep.res S.subtype (Rep.ofAlgebraAutOnUnits F L)
  let A := Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L
  let e := IntermediateField.subgroupEquivAlgEquiv S
  apply groupCohomology.mapIso (A := A) (B := B) e
    (LinearEquiv.refl ℤ (Additive Lˣ)) _ n
  intro g
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Units.ext
  rfl

/-- The first cohomology of every subgroup with these unit coefficients
vanishes by Hilbert 90 over the fixed field. -/
theorem restricted_HOne_subsingleton (S : Subgroup (L ≃ₐ[F] L)) :
    Subsingleton (H1 (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits F L))) := by
  let e := fixedFieldCohomologyIso F L S 1
  have hInjective : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  exact ⟨fun x y ↦ hInjective (Subsingleton.elim _ _)⟩

end

end ManuscriptAudit.GaloisSubgroupUnitCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisSubgroupUnitCohomology.fixedFieldCohomologyIso,
      ``ManuscriptAudit.GaloisSubgroupUnitCohomology.restricted_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
