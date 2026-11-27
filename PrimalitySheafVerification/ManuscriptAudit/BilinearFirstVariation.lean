import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The two slots of a bilinear first variation

Physical PDF pp. 478–479, Proposition 4.1. Along a differentiable curvature
path, both slots of the leading quadratic expression contribute. For a symmetric
pairing the braided part of the curvature variation remains in the weak equation.
-/

namespace ManuscriptAudit.BilinearFirstVariation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem first_variation (B : V →L[ℝ] V →L[ℝ] ℝ)
    {F : ℝ → V} {t : ℝ} {v : V} (hF : HasDerivAt F v t) :
    HasDerivAt (fun s : ℝ => B (F s) (F s) / 2)
      ((B (F t) v + B v (F t)) / 2) t :=
  (ContinuousLinearMap.hasDerivAt_of_bilinear (B := B)
    (fun _ => hF) (fun _ => hF)).div_const 2

theorem printed_variation_iff (B : V →L[ℝ] V →L[ℝ] ℝ)
    {F : ℝ → V} {t : ℝ} {v : V} (hF : HasDerivAt F v t) :
    HasDerivAt (fun s : ℝ => B (F s) (F s) / 2) (B v (F t)) t ↔
      B (F t) v = B v (F t) := by
  constructor
  · intro h
    have hderiv := h.unique (first_variation B hF)
    linarith
  · intro h
    have hderiv : (B (F t) v + B v (F t)) / 2 = B v (F t) := by linarith
    exact hderiv ▸ first_variation B hF

theorem symmetric_variation_with_braid (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ x v, B x v = B v x)
    {F : ℝ → V} {t : ℝ} {d e : V} (hF : HasDerivAt F (d + e) t) :
    HasDerivAt (fun s : ℝ => B (F s) (F s) / 2)
      (B d (F t) + B e (F t)) t := by
  have h := (printed_variation_iff B hF).2 (hB (F t) (d + e))
  simpa only [map_add, ContinuousLinearMap.add_apply] using h

theorem weak_equation_with_braid (B : V →L[ℝ] V →L[ℝ] ℝ)
    (x d e : V) :
    (∀ other : ℝ, (B d x + B e x + other = 0 ↔ B d x + other = 0)) ↔
      B e x = 0 := by
  constructor
  · intro h
    have hz := (h (-B d x)).2 (by ring)
    linarith
  · intro hz other
    simp [hz]

end ManuscriptAudit.BilinearFirstVariation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.BilinearFirstVariation.first_variation,
      ``ManuscriptAudit.BilinearFirstVariation.printed_variation_iff,
      ``ManuscriptAudit.BilinearFirstVariation.symmetric_variation_with_braid,
      ``ManuscriptAudit.BilinearFirstVariation.weak_equation_with_braid] do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {axioms}"
