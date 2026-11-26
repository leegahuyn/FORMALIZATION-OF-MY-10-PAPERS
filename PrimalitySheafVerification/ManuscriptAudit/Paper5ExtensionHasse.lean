import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualHasseWeil
import PrimalitySheafVerification.ManuscriptAudit.EllipticQuadraticRadius

/-! Hasse's bound and the local root radius in every finite extension. -/

namespace ManuscriptAudit.Paper5ExtensionHasse

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open CubicGeometricTorsion Paper5ExtensionRecurrence Paper5PrintedActualExtensionCounts
open Paper5ActualHasseWeil Paper5PrintedRecurrence

noncomputable section

theorem actual_extension_hasse {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    {A : ZMod p} (hA : A ≠ 0) :
    |(p : ℝ) ^ Module.finrank (ZMod p) E + 1 -
      (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℝ)| ≤
        2 * Real.sqrt ((p : ℝ) ^ Module.finrank (ZMod p) E) := by
  letI : CharP E p := charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p
  have hE : ringChar E ≠ 2 := by rw [ringChar.eq E p]; omega
  have hA' : algebraMap (ZMod p) E A ≠ 0 := by
    simpa only [map_zero] using (algebraMap (ZMod p) E).injective.ne hA
  have hc : Fintype.card E = p ^ Module.finrank (ZMod p) E := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card]
  have hh := CubicHasseBound.reducedCubic_hasse hE hA' (reducedK_good hp hA)
  rw [← printed_cubic_baseChange_eq_zero p A, hc, Nat.cast_pow] at hh
  exact hh

theorem actual_recurrence_hasse {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) (n : ℕ) :
    |(recurrence p (firstTrace p A) n : ℝ)| ≤ 2 * Real.sqrt ((p : ℝ) ^ n) := by
  cases n with
  | zero => norm_num [recurrence]
  | succ n =>
    classical
    let F := GaloisField p (n + 1)
    letI : Fintype F := Fintype.ofFinite F
    have hd : Module.finrank (ZMod p) F = n + 1 := GaloisField.finrank p n.succ_ne_zero
    have hc : Fintype.card F = p ^ (n + 1) := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p (n + 1) n.succ_ne_zero
    have hR := Paper5PrintedActualExtensionCounts.actual_extension_trace_eq_recurrence
      (E := F) hp hA
    rw [hc, hd] at hR
    have hr := congrArg (fun k : ℤ => (k : ℝ)) hR
    push_cast at hr
    change (p : ℝ) ^ (n + 1) + 1 -
      (Nat.card ((paper5TraceCurve p A).baseChange F).toProjective.Point : ℝ) =
        (recurrence p (firstTrace p A) (n + 1) : ℝ) at hr
    rw [← hr]
    simpa only [hd] using actual_extension_hasse (E := F) hp hA

theorem actual_recurrence_hasse_squared {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) (n : ℕ) :
    (recurrence p (firstTrace p A) n) ^ 2 ≤ 4 * (p : ℤ) ^ n := by
  have h := actual_recurrence_hasse hp hA n
  let a := (recurrence p (firstTrace p A) n : ℝ)
  let q := (p : ℝ) ^ n
  change |a| ≤ 2 * Real.sqrt q at h
  have h0 : 0 ≤ q := by positivity
  have hp' := mul_nonneg (sub_nonneg.mpr h)
    (add_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg q)) (abs_nonneg a))
  have hh : a ^ 2 ≤ 4 * q := by nlinarith [sq_abs a, Real.sq_sqrt h0]
  dsimp [a, q] at hh
  exact_mod_cast hh

theorem actual_extension_root_radius {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    {A : ZMod p} (hA : A ≠ 0) (z : ℂ)
    (hz : (EllipticQuadraticRadius.localPolynomial ((p : ℝ) ^ Module.finrank (ZMod p) E)
      ((p : ℝ) ^ Module.finrank (ZMod p) E + 1 -
        (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℝ))).IsRoot z) :
    ‖z‖ = 1 / Real.sqrt ((p : ℝ) ^ Module.finrank (ZMod p) E) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  exact (EllipticQuadraticRadius.all_roots_radius_iff _ _
    (pow_pos hpos _)).mpr (actual_extension_hasse (E := E) hp hA) z hz

end
end ManuscriptAudit.Paper5ExtensionHasse

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5ExtensionHasse.actual_extension_hasse,
      ``ManuscriptAudit.Paper5ExtensionHasse.actual_recurrence_hasse,
      ``ManuscriptAudit.Paper5ExtensionHasse.actual_recurrence_hasse_squared,
      ``ManuscriptAudit.Paper5ExtensionHasse.actual_extension_root_radius] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
