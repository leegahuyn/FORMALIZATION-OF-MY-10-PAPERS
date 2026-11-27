import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.AdditiveKernelComposition

/-! Geometric fixed kernels for a scalar times a nontrivial cubic rotation. -/

namespace ManuscriptAudit.CubicRotationalFixedKernel

open AdditiveKernelComposition TorsionFrobeniusModule

variable {G : Type*} [AddCommGroup G]

private theorem norm_pair (u v : AddMonoid.End G) (s : ℤ)
    (hSum : u + v = -1) (hProd : u * v = 1) :
    (1 - s • u) * (1 - s • v) = (1 + s + s * s) • (1 : AddMonoid.End G) := by
  apply AddMonoidHom.ext
  intro x
  change (x - s • v x) - s • u (x - s • v x) = (1 + s + s * s) • x
  have hS : u x + v x = -x := congrArg (fun t : AddMonoid.End G => t x) hSum
  have hP : u (v x) = x := congrArg (fun t : AddMonoid.End G => t x) hProd
  calc
    _ = x - (s • u x + s • v x) + (s * s) • x := by
      rw [map_sub, map_zsmul, zsmul_sub, smul_smul, hP]
      abel
    _ = _ := by
      rw [← zsmul_add, hS, zsmul_neg, sub_neg_eq_add, add_zsmul, add_zsmul, one_zsmul]

theorem norm_factor (r : AddMonoid.End G) (s : ℤ) (hCube : r ^ 3 = 1)
    (hQuad : r ^ 2 + r + 1 = 0) :
    (1 - s • r) * (1 - s • r ^ 2) = (1 + s + s * s) • (1 : AddMonoid.End G) ∧
    (1 - s • r ^ 2) * (1 - s • r) = (1 + s + s * s) • (1 : AddMonoid.End G) := by
  have hS : r ^ 2 + r = -1 := eq_neg_of_add_eq_zero_left hQuad
  have hL : r * r ^ 2 = 1 := by rw [← pow_succ', hCube]
  have hR : r ^ 2 * r = 1 := by rw [← pow_succ, hCube]
  exact ⟨norm_pair r (r ^ 2) s ((add_comm _ _).trans hS) hL, norm_pair (r ^ 2) r s hS hR⟩

private theorem intertwiners (r f : AddMonoid.End G) (s : ℤ) (hCube : r ^ 3 = 1)
    (hConj : f * r = r ^ 2 * f) :
    f * (1 - s • r) = (1 - s • r ^ 2) * f ∧
    f * (1 - s • r ^ 2) = (1 - s • r) * f := by
  have hConj₂ : f * r ^ 2 = r * f := by
    calc
      _ = (f * r) * r := by rw [pow_two, mul_assoc]
      _ = (r ^ 2 * f) * r := congrArg (fun t => t * r) hConj
      _ = r ^ 2 * (f * r) := mul_assoc _ _ _
      _ = r ^ 2 * (r ^ 2 * f) := congrArg (fun t => r ^ 2 * t) hConj
      _ = r * f := by
        rw [← mul_assoc, ← pow_add, show (2 : ℕ) + 2 = 3 + 1 by decide,
          pow_succ, hCube, one_mul]
  constructor
  · rw [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hConj]
  · rw [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hConj₂]

private def kernelMap (a b f : AddMonoid.End G) (h : f * a = b * f) : a.ker → b.ker :=
  fun x => ⟨f x.val, by
    change b (f x) = 0
    have he := congrArg (fun T : AddMonoid.End G => T x) h.symm
    change b (f x) = f (a x) at he
    rw [he, show a x = 0 from x.property, map_zero]⟩

theorem card_fixed (r f : AddMonoid.End G) (s : ℤ) (hCube : r ^ 3 = 1)
    (hQuad : r ^ 2 + r + 1 = 0) (hConj : f * r = r ^ 2 * f)
    (hF : Function.Injective f) (n : ℕ) (hN : (n : ℤ) = 1 + s + s * s) (hN₀ : 0 < n)
    (hSurj : Function.Surjective (nsmulAddMonoidHom n : G →+ G))
    (hCard : Nat.card (Torsion n G) = n ^ 2) :
    Nat.card ↥((1 - s • r).ker) = n := by
  let a : AddMonoid.End G := 1 - s • r
  let b : AddMonoid.End G := 1 - s • r ^ 2
  obtain ⟨h₁, h₂⟩ := norm_factor r s hCube hQuad
  have eN : (1 + s + s * s) • (1 : AddMonoid.End G) = nsmulAddMonoidHom n := by
    rw [← hN]
    apply AddMonoidHom.ext
    intro x
    change (n : ℤ) • x = n • x
    simp only [natCast_zsmul]
  have hAB : a.comp b = nsmulAddMonoidHom n := h₁.trans eN
  have hBA : b.comp a = nsmulAddMonoidHom n := h₂.trans eN
  have hb : Function.Surjective b := by
    intro x
    obtain ⟨y, hy⟩ := hSurj x
    exact ⟨a y, (congrArg (fun T : G →+ G => T y) hBA).trans hy⟩
  have hc : n ^ 2 = Nat.card ↥a.ker * Nat.card ↥b.ker := by
    rw [← hCard, Torsion, subgroup, ← hAB]
    exact card_ker_comp a b hb
  have ha₀ : Nat.card ↥a.ker ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    exact (pow_pos hN₀ _).ne' hc
  have hb₀ : Nat.card ↥b.ker ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact (pow_pos hN₀ _).ne' hc
  letI := Nat.finite_of_card_ne_zero ha₀
  letI := Nat.finite_of_card_ne_zero hb₀
  obtain ⟨ha, hb⟩ := intertwiners r f s hCube hConj
  have inj (u v : AddMonoid.End G) (h : f * u = v * f) :
      Function.Injective (kernelMap u v f h) :=
    fun _ _ he => Subtype.ext (hF (congrArg Subtype.val he))
  have hEq : Nat.card ↥a.ker = Nat.card ↥b.ker :=
    le_antisymm (Nat.card_le_card_of_injective _ (inj a b ha))
      (Nat.card_le_card_of_injective _ (inj b a hb))
  rw [← hEq, ← pow_two] at hc
  change Nat.card ↥a.ker = n
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · exact (ne_of_lt (Nat.pow_lt_pow_left h (by decide : (2 : ℕ) ≠ 0))) hc.symm
  · exact (ne_of_lt (Nat.pow_lt_pow_left h (by decide : (2 : ℕ) ≠ 0))) hc

end ManuscriptAudit.CubicRotationalFixedKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicRotationalFixedKernel.norm_factor,
      ``ManuscriptAudit.CubicRotationalFixedKernel.card_fixed] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
