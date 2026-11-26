import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.Paper9ThetaCuspPhases

/-!
# Cusp phases depend on the multiplier

On the actual group Γ(2), the sign of b/2 modulo two is a unitary
character. At the three cusp generators with scaling matrices
(1, S, TS), its values are (-1, 1, -1). A character twist preserves
the multiplier cocycle and changes the standard theta phase table
(1, 1, i) to (-1, 1, -i). The number of phase-one cusp generators
therefore depends on the chosen multiplier.
-/

namespace ManuscriptAudit.Paper9GammaTwoSign

open Matrix Matrix.SpecialLinearGroup
open LiteralCuspTruncation (GammaTwo)
open CompactModularCore (reduceTwo mem_gamma_iff_reduced_one)
open ModularGroup (S T)
open scoped MatrixGroups

noncomputable section

def halfUpperRight (g : GammaTwo) : ZMod 2 :=
  (((g : SL(2, ℤ)) 0 1 / 2 : ℤ) : ZMod 2)

private theorem halfUpperRight_one : halfUpperRight 1 = 0 := by decide

theorem halfUpperRight_mul (g h : GammaTwo) :
    halfUpperRight (g * h) = halfUpperRight g + halfUpperRight h := by
  have hg := CongruenceSubgroup.Gamma_mem.mp g.2
  have hh := CongruenceSubgroup.Gamma_mem.mp h.2
  obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((g : SL(2, ℤ)) 0 1) 2).mp hg.2.1
  obtain ⟨v, hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((h : SL(2, ℤ)) 0 1) 2).mp hh.2.1
  have hm : ((g * h : GammaTwo) : SL(2, ℤ)) 0 1 =
      2 * (((g : SL(2, ℤ)) 0 0) * v + u * ((h : SL(2, ℤ)) 1 1)) := by
    change (((g : SL(2, ℤ)).1) * ((h : SL(2, ℤ)).1)) 0 1 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two, hu, hv]
    ring
  have hmu : ((g : SL(2, ℤ)) 0 1) / 2 = u := by omega
  have hmv : ((h : SL(2, ℤ)) 0 1) / 2 = v := by omega
  have hmuv : (((g * h : GammaTwo) : SL(2, ℤ)) 0 1) / 2 =
      ((g : SL(2, ℤ)) 0 0) * v + u * ((h : SL(2, ℤ)) 1 1) := by omega
  simp only [halfUpperRight, hmu, hmv, hmuv, Int.cast_add, Int.cast_mul, hg.1, hh.2.2.2,
    one_mul, mul_one]
  exact add_comm _ _

private def modTwoSign (x : ZMod 2) : ℂ := if x = 0 then 1 else -1

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left
    simpa only [h, Nat.cast_zero] using (ZMod.natCast_zmod_val a).symm
  · right
    simpa only [h, Nat.cast_one] using (ZMod.natCast_zmod_val a).symm

private theorem modTwoSign_add (x y : ZMod 2) :
    modTwoSign (x + y) = modTwoSign x * modTwoSign y := by
  rcases zmod_two_cases x with rfl | rfl <;> rcases zmod_two_cases y with rfl | rfl <;>
    simp [modTwoSign, show (1 : ZMod 2) + 1 = 0 by decide]

/-- A genuine scalar unitary character of the entire actual group. -/
def upperRightSign : GammaTwo →* ℂ where
  toFun g := modTwoSign (halfUpperRight g)
  map_one' := by simp [halfUpperRight_one, modTwoSign]
  map_mul' g h := by rw [halfUpperRight_mul, modTwoSign_add]

theorem upperRightSign_unitary (g : GammaTwo) : ‖upperRightSign g‖ = 1 := by
  change ‖modTwoSign (halfUpperRight g)‖ = 1
  unfold modTwoSign
  split <;> simp

/-- Twisting a complex automorphy cocycle by the character preserves the
same cocycle equation. -/
theorem twist_preserves_cocycle {X : Type*} [MulAction GammaTwo X]
    (j : GammaTwo → X → ℂ)
    (hj : ∀ g h x, j (g * h) x = j g (h • x) * j h x)
    (g h : GammaTwo) (x : X) :
    upperRightSign (g * h) * j (g * h) x =
      (upperRightSign g * j g (h • x)) * (upperRightSign h * j h x) := by
  rw [map_mul, hj]
  ring

def cuspParabolicMatrix (i : Fin 3) : SL(2, ℤ) :=
  ThreeCuspNeighborhoods.chart i * T ^ (2 : ℕ) * (ThreeCuspNeighborhoods.chart i)⁻¹

private theorem translation_square_reduces : reduceTwo (T ^ (2 : ℕ)) = 1 := by decide

theorem cuspParabolic_mem (i : Fin 3) : cuspParabolicMatrix i ∈ GammaTwo := by
  apply (mem_gamma_iff_reduced_one _).mpr
  simp [cuspParabolicMatrix, translation_square_reduces]

def cuspParabolic (i : Fin 3) : GammaTwo :=
  ⟨cuspParabolicMatrix i, cuspParabolic_mem i⟩

private theorem cuspParabolic_upperRight (i : Fin 3) :
    (cuspParabolic i : SL(2, ℤ)) 0 1 = ![(2 : ℤ), 0, 2] i := by
  fin_cases i <;> decide

theorem upperRightSign_cuspParabolic (i : Fin 3) :
    upperRightSign (cuspParabolic i) = ![(-1 : ℂ), 1, -1] i := by
  change modTwoSign ((((cuspParabolic i : SL(2, ℤ)) 0 1 / 2 : ℤ) : ZMod 2)) = _
  rw [cuspParabolic_upperRight]
  fin_cases i <;> norm_num [modTwoSign]

/-- The standard Jacobi theta phase table after the actual character twist. -/
theorem twisted_theta_phases (i : Fin 3) :
    upperRightSign (cuspParabolic i) * Paper9ThetaCuspPhases.parabolicPhase i =
      ![(-1 : ℂ), 1, -Complex.I] i := by
  rw [upperRightSign_cuspParabolic]
  fin_cases i <;> norm_num [Paper9ThetaCuspPhases.parabolicPhase]

theorem twisted_theta_phase_one_iff (i : Fin 3) :
    upperRightSign (cuspParabolic i) * Paper9ThetaCuspPhases.parabolicPhase i = 1 ↔ i = 1 := by
  rw [twisted_theta_phases]
  have hn : (-Complex.I : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
  have hNegOne : (-1 : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
  fin_cases i <;> simp [hn, hNegOne]

end

end ManuscriptAudit.Paper9GammaTwoSign

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9GammaTwoSign.halfUpperRight_mul,
      ``ManuscriptAudit.Paper9GammaTwoSign.upperRightSign_unitary,
      ``ManuscriptAudit.Paper9GammaTwoSign.twist_preserves_cocycle,
      ``ManuscriptAudit.Paper9GammaTwoSign.cuspParabolic_mem,
      ``ManuscriptAudit.Paper9GammaTwoSign.upperRightSign_cuspParabolic,
      ``ManuscriptAudit.Paper9GammaTwoSign.twisted_theta_phases,
      ``ManuscriptAudit.Paper9GammaTwoSign.twisted_theta_phase_one_iff] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
