import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! A surjective separated weakly étale radicial map is an isomorphism
when it is quasi-compact. In particular this applies to a weakly étale
affine universal homeomorphism. -/

namespace ManuscriptAudit.WeaklyEtaleRadicialIso

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual pullback of a monomorphism along itself is an isomorphism,
so faithful flat descent gives an isomorphism on the base. -/
theorem isIso_of_flat_surjective_qc_mono
    [Flat f] [Surjective f] [QuasiCompact f] [Mono f] : IsIso f :=
  MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := f)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    (inferInstanceAs (IsIso (pullback.fst f f)))

/-- Flatness and surjectivity of the closed diagonal make a weakly étale
radicial separated morphism a monomorphism. -/
theorem mono_of_weaklyEtale_of_universallyInjective
    [WeaklyEtale f] [UniversallyInjective f] [IsSeparated f] : Mono f := by
  letI : Surjective (pullback.diagonal f) := (UniversallyInjective.iff_diagonal f).mp inferInstance
  have hd : IsIso (pullback.diagonal f) :=
    isIso_of_flat_surjective_qc_mono (pullback.diagonal f)
  exact (pullback.isIso_diagonal_iff f).mp hd

theorem isIso_of_weaklyEtale_of_universallyInjective
    [WeaklyEtale f] [UniversallyInjective f] [IsSeparated f] [Surjective f] [QuasiCompact f] :
    IsIso f := by
  letI := mono_of_weaklyEtale_of_universallyInjective f
  exact isIso_of_flat_surjective_qc_mono f

end ManuscriptAudit.WeaklyEtaleRadicialIso

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleRadicialIso.isIso_of_flat_surjective_qc_mono,
      ``ManuscriptAudit.WeaklyEtaleRadicialIso.mono_of_weaklyEtale_of_universallyInjective,
      ``ManuscriptAudit.WeaklyEtaleRadicialIso.isIso_of_weaklyEtale_of_universallyInjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
