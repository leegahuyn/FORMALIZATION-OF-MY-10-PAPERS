import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import PrimalitySheafVerification.ManuscriptAudit.Paper5TwoAdicFrobenius

/-! Trace and determinant on the actual 2-adic Frobenius reduce to their finite values. -/

namespace ManuscriptAudit.Paper5TwoAdicCoefficients

open Paper5TwoAdicFrobenius Paper5TwoPowerFrobenius
open Module

noncomputable section

section Pair

variable {R S : Type*} [CommRing R] [CommRing S]

theorem trace_pair (f : Module.End R (R × R)) :
    LinearMap.trace R (R × R) f = (f (1, 0)).1 + (f (0, 1)).2 := by
  rw [LinearMap.trace_eq_matrix_trace R (Basis.finTwoProd R), Matrix.trace_fin_two]
  simp [LinearMap.toMatrix_apply]

theorem det_pair (f : Module.End R (R × R)) :
    LinearMap.det f = (f (1, 0)).1 * (f (0, 1)).2 - (f (0, 1)).1 * (f (1, 0)).2 := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd R), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

def mapPair (r : R →+* S) (a : R × R) : S × S := (r a.1, r a.2)

theorem map_trace_det (r : R →+* S) (f : Module.End R (R × R))
    (g : Module.End S (S × S))
    (h : ∀ a, mapPair r (f a) = g (mapPair r a)) :
    r (LinearMap.trace R (R × R) f) = LinearMap.trace S (S × S) g ∧
      r (LinearMap.det f) = LinearMap.det g := by
  have h₀ := h (1, 0)
  have h₁ := h (0, 1)
  have hh₀ : (r (f (1, 0)).1, r (f (1, 0)).2) = g (1, 0) := by
    simpa only [mapPair, Prod.fst, Prod.snd, map_one, map_zero] using h₀
  have hh₁ : (r (f (0, 1)).1, r (f (0, 1)).2) = g (0, 1) := by
    simpa only [mapPair, Prod.fst, Prod.snd, map_one, map_zero] using h₁
  have h00 : r (f (1, 0)).1 = (g (1, 0)).1 := congrArg Prod.fst hh₀
  have h10 : r (f (1, 0)).2 = (g (1, 0)).2 := congrArg Prod.snd hh₀
  have h01 : r (f (0, 1)).1 = (g (0, 1)).1 := congrArg Prod.fst hh₁
  have h11 : r (f (0, 1)).2 = (g (0, 1)).2 := congrArg Prod.snd hh₁
  constructor
  · rw [trace_pair, trace_pair, map_add, h00, h11]
  · rw [det_pair, det_pair, map_sub, map_mul, map_mul, h00, h11, h01, h10]

end Pair

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L] [IsAlgClosed L]

def trace (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) : ℤ_[2] :=
  LinearMap.trace ℤ_[2] (ℤ_[2] × ℤ_[2]) (coordinateFrobeniusPadic p L hp hA).toLinearMap

def determinant (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) : ℤ_[2] :=
  LinearMap.det (coordinateFrobeniusPadic p L hp hA).toLinearMap

theorem reduction_trace_det (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (n : ℕ) :
    PadicInt.toZModPow n (trace p L hp hA) =
      LinearMap.trace (ZMod (2 ^ n)) (ZMod (2 ^ n) × ZMod (2 ^ n))
        (coordinateFrobenius p L hp hA n).toLinearMap ∧
    PadicInt.toZModPow n (determinant p L hp hA) =
      LinearMap.det (coordinateFrobenius p L hp hA n).toLinearMap := by
  exact map_trace_det (PadicInt.toZModPow n)
    (coordinateFrobeniusPadic p L hp hA).toLinearMap (coordinateFrobenius p L hp hA n).toLinearMap
    (residue_coordinateFrobenius p L hp hA n)

theorem trace_eq_of_reductions (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (t : ℤ_[2])
    (ht : ∀ n, PadicInt.toZModPow n t =
      LinearMap.trace (ZMod (2 ^ n)) (ZMod (2 ^ n) × ZMod (2 ^ n))
        (coordinateFrobenius p L hp hA n).toLinearMap) :
    trace p L hp hA = t :=
  PadicInt.ext_of_toZModPow.mp fun n => (reduction_trace_det p L hp hA n).1.trans (ht n).symm

theorem determinant_eq_of_reductions (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (d : ℤ_[2])
    (hd : ∀ n, PadicInt.toZModPow n d =
      LinearMap.det (coordinateFrobenius p L hp hA n).toLinearMap) :
    determinant p L hp hA = d :=
  PadicInt.ext_of_toZModPow.mp fun n => (reduction_trace_det p L hp hA n).2.trans (hd n).symm

end
end ManuscriptAudit.Paper5TwoAdicCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5TwoAdicCoefficients.trace_pair,
      ``ManuscriptAudit.Paper5TwoAdicCoefficients.det_pair,
      ``ManuscriptAudit.Paper5TwoAdicCoefficients.map_trace_det,
      ``ManuscriptAudit.Paper5TwoAdicCoefficients.reduction_trace_det,
      ``ManuscriptAudit.Paper5TwoAdicCoefficients.trace_eq_of_reductions,
      ``ManuscriptAudit.Paper5TwoAdicCoefficients.determinant_eq_of_reductions] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
