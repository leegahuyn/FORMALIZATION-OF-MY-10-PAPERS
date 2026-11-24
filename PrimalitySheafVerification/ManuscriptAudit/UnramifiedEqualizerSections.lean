import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Unramified.Basic

/-!
# Formally unramified sections of an algebra equalizer

If two algebra maps agree modulo a square-zero ideal, then any map from a
formally unramified algebra into their source factors through their actual
equalizer subalgebra.
-/

namespace ManuscriptAudit.UnramifiedEqualizerSections

variable {R A B P : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing P]
variable [Algebra R A] [Algebra R B] [Algebra R P]
variable [Algebra.FormallyUnramified R P]

/-- Formal unramifiedness forces a section to land in the algebra equalizer
of two maps that coincide after square-zero reduction. -/
def sectionsEquiv (J : Ideal B) (hJ : J ^ 2 = ⊥) (f g : A →ₐ[R] B)
    (hfg : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) :
    (P →ₐ[R] AlgHom.equalizer f g) ≃ (P →ₐ[R] A) where
  toFun t := (AlgHom.equalizer f g).val.comp t
  invFun t := t.codRestrict _ fun p => by
    apply (AlgHom.mem_equalizer f g _).2
    have h : f.comp t = g.comp t := by
      apply Algebra.FormallyUnramified.comp_injective J hJ
      apply AlgHom.ext
      intro z
      exact AlgHom.congr_fun hfg (t z)
    exact AlgHom.congr_fun h p
  left_inv t := AlgHom.ext fun _ => Subtype.ext rfl
  right_inv t := AlgHom.ext fun _ => rfl

end ManuscriptAudit.UnramifiedEqualizerSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.UnramifiedEqualizerSections.sectionsEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
