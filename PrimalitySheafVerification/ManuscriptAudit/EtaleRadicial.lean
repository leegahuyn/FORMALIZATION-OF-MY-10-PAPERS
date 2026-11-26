import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

namespace ManuscriptAudit.EtaleRadicial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A surjective, universally injective étale morphism is an isomorphism. -/
theorem isIso_of_etale_of_surjective_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [Surjective f]
    [UniversallyInjective f] : IsIso f := by
  have hDiagonal : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  letI : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hDiagonal⟩
  letI : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨IsOpenImmersion.of_flat_of_mono f, inferInstance⟩

end ManuscriptAudit.EtaleRadicial

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleRadicial.isIso_of_etale_of_surjective_of_universallyInjective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
