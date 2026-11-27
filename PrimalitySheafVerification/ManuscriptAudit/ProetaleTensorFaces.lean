import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor
import PrimalitySheafVerification.ManuscriptAudit.TwistedTensorEqualizer

/-! The three tensor face maps are the actual face morphisms of the
corresponding affine weakly étale charts. -/

namespace ManuscriptAudit.ProetaleTensorFaces

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor
open TwistedTensorEqualizer (Double Triple first second face01 face02 face12)

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] {R T V : Type u} [CommRing R] [CommRing T] [CommRing V]
  [Algebra A R] [Algebra A T] [Algebra A V]
  [WeaklyEtale (structureMap A R)] [WeaklyEtale (structureMap A T)]
  [WeaklyEtale (structureMap A V)]

/-- Contravariant composition of the actual algebra map arrows. -/
theorem arrow_comp (g : R →ₐ[A] T) (h : T →ₐ[A] V) :
    arrow A h ≫ arrow A g = arrow A (h.comp g) := by
  apply MorphismProperty.Over.Hom.ext
  change specMap A h ≫ specMap A g = specMap A (h.comp g)
  rw [← Spec.map_comp]
  rfl

variable (A) (B : Type u) [CommRing B] [Algebra A B] [WeaklyEtale (structureMap A B)]

/-- The first and second projections of the actual double overlap. -/
abbrev p₀ := arrow A (first A B)
abbrev p₁ := arrow A (second A B)

/-- The three pairwise projections from the actual tensor cube. -/
abbrev e₀₁ := arrow A (face01 A B)
abbrev e₀₂ := arrow A (face02 A B)
abbrev e₁₂ := arrow A (face12 A B)

theorem double_isPullback :
    IsPullback (p₀ A B) (p₁ A B) (toTerminal A B) (toTerminal A B) :=
  tensor_isPullback A B B

theorem face_first_first : e₀₂ A B ≫ p₀ A B = e₀₁ A B ≫ p₀ A B := by
  rw [arrow_comp, arrow_comp]
  congr 1

theorem face_second_first : e₁₂ A B ≫ p₀ A B = e₀₁ A B ≫ p₁ A B := by
  rw [arrow_comp, arrow_comp]
  congr 1

theorem face_second_second : e₁₂ A B ≫ p₁ A B = e₀₂ A B ≫ p₁ A B := by
  rw [arrow_comp, arrow_comp]
  congr 1

end
end ManuscriptAudit.ProetaleTensorFaces

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleTensorFaces.double_isPullback,
      ``ManuscriptAudit.ProetaleTensorFaces.face_first_first,
      ``ManuscriptAudit.ProetaleTensorFaces.face_second_first,
      ``ManuscriptAudit.ProetaleTensorFaces.face_second_second] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
