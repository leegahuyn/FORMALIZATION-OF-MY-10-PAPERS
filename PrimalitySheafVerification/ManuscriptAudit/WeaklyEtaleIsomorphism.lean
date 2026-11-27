import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-! The isomorphism step for weakly étale radicial surjections. -/

namespace ManuscriptAudit.WeaklyEtaleIsomorphism

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A quasi-compact weakly étale morphism with quasi-compact diagonal is
an isomorphism as soon as it is surjective and universally injective. -/
theorem isIso_of_surjective_of_universallyInjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [WeaklyEtale f] [QuasiCompact f] [QuasiCompact (pullback.diagonal f)]
    [Surjective f] [UniversallyInjective f] : IsIso f := by
  letI : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  letI : IsIso (pullback.diagonal f) := Flat.isIso_of_surjective_of_mono _
  letI : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact Flat.isIso_of_surjective_of_mono f

/-- This applies in particular when a weakly étale surjection is
injective on points and each residue field extension is purely inseparable. -/
theorem isIso_of_injective_of_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [WeaklyEtale f] [QuasiCompact f] [QuasiCompact (pullback.diagonal f)]
    [Surjective f] (hf : Function.Injective f)
    (hκ : ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable) : IsIso f := by
  letI : UniversallyInjective f :=
    ((tfae_universallyInjective f).out 2 0).mp ⟨hf, hκ⟩
  exact isIso_of_surjective_of_universallyInjective f

end ManuscriptAudit.WeaklyEtaleIsomorphism

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleIsomorphism.isIso_of_surjective_of_universallyInjective,
      ``ManuscriptAudit.WeaklyEtaleIsomorphism.isIso_of_injective_of_residueFieldMap] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
