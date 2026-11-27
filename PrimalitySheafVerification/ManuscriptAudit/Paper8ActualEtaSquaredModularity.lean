import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Separation.Connected

/-!
# Native modularity up to a constant of the square of the eta product

The squared ratio is continuous and is a twelfth root of unity by the
native discriminant transformation. Connectedness gives its constant
value and thus the actual weight-one scalar.
-/

namespace ManuscriptAudit.Paper8ActualEtaSquaredModularity

open Matrix UpperHalfPlane Set
open scoped MatrixGroups

noncomputable section

def denominator (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (g 1 0 : ℂ) * z + (g 1 1 : ℂ)

def fractionalLinear (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / denominator g z

theorem denominator_eq (g : SL(2, ℤ)) (z : ℍ) :
    denominator g z = UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z :=
  (ModularGroup.denom_apply g z).symm

theorem denominator_ne_zero (g : SL(2, ℤ)) (z : ℍ) :
    denominator g z ≠ 0 := by
  rw [denominator_eq]
  exact UpperHalfPlane.denom_ne_zero _ _

theorem fractionalLinear_eq (g : SL(2, ℤ)) (z : ℍ) :
    fractionalLinear g z = ((g • z : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [fractionalLinear, denominator]

theorem eta_pow_twentyFour_transform (g : SL(2, ℤ)) (z : ℍ) :
    ModularForm.eta ((g • z : ℍ) : ℂ) ^ 24 =
      denominator g z ^ 12 * ModularForm.eta z ^ 24 := by
  have hg : (g : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨g, rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hg z
  change ModularForm.eta (((g : GL (Fin 2) ℝ) • z : ℍ) : ℂ) ^ 24 =
    (UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z) ^ (12 : ℤ) * ModularForm.eta z ^ 24 at h
  simpa only [denominator_eq, ← ModularGroup.sl_moeb, zpow_ofNat] using h

private def basePoint : ℍ := ⟨Complex.I, by simp⟩

private def squaredRatio (g : SL(2, ℤ)) (z : ℍ) : ℂ :=
  ModularForm.eta (g • z : ℍ) ^ 2 / (denominator g z * ModularForm.eta z ^ 2)

private theorem squaredRatio_pow (g : SL(2, ℤ)) (z : ℍ) :
    squaredRatio g z ^ 12 = 1 := by
  rw [squaredRatio, div_pow, mul_pow, ← pow_mul, ← pow_mul]
  change ModularForm.eta (g • z : ℍ) ^ 24 /
    (denominator g z ^ 12 * ModularForm.eta z ^ 24) = 1
  rw [eta_pow_twentyFour_transform]
  exact div_self (mul_ne_zero (pow_ne_zero _ (denominator_ne_zero g z))
    (pow_ne_zero _ (ModularForm.eta_ne_zero z.im_pos)))

private theorem squaredRatio_continuous (g : SL(2, ℤ)) : Continuous (squaredRatio g) := by
  have hEta : Continuous (fun z : ℍ => ModularForm.eta (z : ℂ)) := by
    refine continuous_iff_continuousAt.mpr (fun z => ?_)
    change ContinuousAt (ModularForm.eta ∘ (fun u : ℍ => (u : ℂ))) z
    exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt
  have hMap : Continuous (fun z : ℍ => g • z) := by
    simpa only [ModularGroup.sl_moeb] using
      (continuous_const_smul (g : GL (Fin 2) ℝ))
  have hD : Continuous (fun z : ℍ => denominator g (z : ℂ)) := by
    unfold denominator
    fun_prop
  exact ((hEta.comp hMap).pow 2).div (hD.mul (hEta.pow 2))
    (fun z => mul_ne_zero (denominator_ne_zero g z)
      (pow_ne_zero _ (ModularForm.eta_ne_zero z.im_pos)))

def squaredMultiplier (g : SL(2, ℤ)) : ℂ := squaredRatio g basePoint

theorem squaredMultiplier_ne_zero (g : SL(2, ℤ)) :
    squaredMultiplier g ≠ 0 := by
  unfold squaredMultiplier squaredRatio
  exact div_ne_zero (pow_ne_zero _ (ModularForm.eta_ne_zero (g • basePoint).im_pos))
    (mul_ne_zero (denominator_ne_zero g basePoint)
      (pow_ne_zero _ (ModularForm.eta_ne_zero basePoint.im_pos)))

theorem squaredMultiplier_pow_twelve (g : SL(2, ℤ)) :
    squaredMultiplier g ^ 12 = 1 :=
  squaredRatio_pow g basePoint

private theorem squaredRatio_eq (g : SL(2, ℤ)) (z : ℍ) :
    squaredRatio g z = squaredMultiplier g := by
  let p : Polynomial ℂ := Polynomial.X ^ (12 : ℕ) - Polynomial.C 1
  have hp : p ≠ 0 := by
    intro h
    have he := congrArg (fun q : Polynomial ℂ => q.coeff 12) h
    norm_num [p, Polynomial.coeff_X_pow, Polynomial.coeff_C] at he
  have hFin : (Set.range (squaredRatio g)).Finite := by
    refine (Polynomial.finite_setOf_isRoot hp).subset ?_
    rintro _ ⟨u, rfl⟩
    change p.IsRoot (squaredRatio g u)
    simp [p, Polynomial.IsRoot, squaredRatio_pow]
  have hPre := isPreconnected_range (squaredRatio_continuous g)
  have hSub : (Set.range (squaredRatio g)).Subsingleton := by
    by_contra h
    exact hFin.not_infinite (hPre.infinite_of_nontrivial (not_subsingleton_iff.mp h))
  exact hSub (Set.mem_range_self z) (Set.mem_range_self basePoint)

theorem eta_squared_transform (g : SL(2, ℤ)) (z : ℍ) :
    ModularForm.eta ((g • z : ℍ) : ℂ) ^ 2 =
      squaredMultiplier g * (denominator g z * ModularForm.eta z ^ 2) := by
  apply (div_eq_iff (mul_ne_zero (denominator_ne_zero g z)
    (pow_ne_zero _ (ModularForm.eta_ne_zero z.im_pos)))).mp
  exact squaredRatio_eq g z

end
end ManuscriptAudit.Paper8ActualEtaSquaredModularity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.denominator_eq,
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.fractionalLinear_eq,
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.eta_pow_twentyFour_transform,
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.squaredMultiplier_ne_zero,
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.squaredMultiplier_pow_twelve,
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.eta_squared_transform] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
