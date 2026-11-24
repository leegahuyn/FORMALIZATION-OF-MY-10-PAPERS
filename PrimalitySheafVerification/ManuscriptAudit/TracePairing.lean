import Lean.Util.CollectAxioms
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# The printed complex trace pairing

Paper 10, pp. 466 and 489, pairs two complex forms by applying a
linear trace to their product. Multiplication of those forms is complex
bilinear. A complex bilinear pairing vanishes if it also has a
conjugate-linear slot.
-/

namespace ManuscriptAudit.TracePairing

theorem paper10_sesquilinear_bilinear_pair_eq_zero {U V : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (B : U →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hs : (∀ (c : ℂ) (x : U) (y : V), B x (c • y) = star c * B x y) ∨
          (∀ (c : ℂ) (x : U) (y : V), B (c • x) y = star c * B x y)) :
    B = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change B x y = 0
  have h (c : ℂ) : c * B x y = star c * B x y := by
    rcases hs with hr | hl
    · simpa only [map_smul, smul_eq_mul] using hr c x y
    · simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using hl c x y
  have hi : Complex.I * B x y = -(Complex.I * B x y) := by
    simpa only [Complex.star_def, Complex.conj_I, neg_mul] using h Complex.I
  have hz : Complex.I * B x y + Complex.I * B x y = 0 :=
    (congrArg (fun z => z + Complex.I * B x y) hi).trans (neg_add_cancel _)
  rw [← two_mul, ← mul_assoc] at hz
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)

end ManuscriptAudit.TracePairing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.TracePairing.paper10_sesquilinear_bilinear_pair_eq_zero
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
