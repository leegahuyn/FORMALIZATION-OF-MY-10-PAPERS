import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.Cusps
import PrimalitySheafVerification.ManuscriptAudit.LiteralCuspTruncation

/-!
# The within-Γ(2) cusp transport required in Paper 9 cannot reach the other cusps

Physical p. 445, Proposition 13 requires a matrix in Γ(2) sending
infinity to each cusp. In Mathlib's actual boundary action, 0 and 1
are Γ(2) cusps. The parity of the first column excludes both targets.
-/

namespace ManuscriptAudit.Paper9CuspTransport

open Matrix SpecialLinearGroup OnePoint
open scoped MatrixGroups
open LiteralCuspTruncation (GammaTwo)

noncomputable section

abbrev boundaryGroup : Subgroup (GL (Fin 2) ℝ) :=
  (GammaTwo : Subgroup (GL (Fin 2) ℝ))

def infinity : OnePoint ℝ := ∞
def cuspZero : OnePoint ℝ := ((0 : ℝ) : OnePoint ℝ)
def cuspOne : OnePoint ℝ := ((1 : ℝ) : OnePoint ℝ)

theorem infinity_isCusp : IsCusp infinity boundaryGroup := by
  apply (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z boundaryGroup).2
  exact isCusp_SL2Z_iff.2 ⟨(∞ : OnePoint ℚ), by simp [infinity]⟩

theorem zero_isCusp : IsCusp cuspZero boundaryGroup := by
  apply (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z boundaryGroup).2
  exact isCusp_SL2Z_iff.2 ⟨((0 : ℚ) : OnePoint ℚ), by simp [cuspZero]⟩

theorem one_isCusp : IsCusp cuspOne boundaryGroup := by
  apply (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z boundaryGroup).2
  exact isCusp_SL2Z_iff.2 ⟨((1 : ℚ) : OnePoint ℚ), by simp [cuspOne]⟩

private theorem mapGL_entry (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g) i j = (g i j : ℝ) := by
  change ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
  rw [mapGL_coe_matrix]
  rfl

theorem infinity_not_sent_to_zero (g : GammaTwo) :
    mapGL ℝ (g : SL(2, ℤ)) • infinity ≠ cuspZero := by
  let A : SL(2, ℤ) := g
  have hA : A ∈ GammaTwo := g.property
  obtain ⟨ha, _, _, _⟩ := CongruenceSubgroup.Gamma_mem.mp hA
  change mapGL ℝ A • (∞ : OnePoint ℝ) ≠ ((0 : ℝ) : OnePoint ℝ)
  rw [OnePoint.smul_infty_eq_ite]
  split_ifs with hc
  · simp
  · intro hEq
    have hDiv := OnePoint.coe_injective hEq
    rw [mapGL_entry, mapGL_entry] at hDiv
    rw [mapGL_entry] at hc
    have hZero : (A 0 0 : ℝ) = 0 := by simpa only [zero_mul] using (div_eq_iff hc).mp hDiv
    have hInt : A 0 0 = 0 := by exact_mod_cast hZero
    rw [hInt] at ha
    norm_num at ha

theorem infinity_not_sent_to_one (g : GammaTwo) :
    mapGL ℝ (g : SL(2, ℤ)) • infinity ≠ cuspOne := by
  let A : SL(2, ℤ) := g
  have hA : A ∈ GammaTwo := g.property
  obtain ⟨ha, _, hc, _⟩ := CongruenceSubgroup.Gamma_mem.mp hA
  change mapGL ℝ A • (∞ : OnePoint ℝ) ≠ ((1 : ℝ) : OnePoint ℝ)
  rw [OnePoint.smul_infty_eq_ite]
  split_ifs with hd
  · simp
  · intro hEq
    have hDiv := OnePoint.coe_injective hEq
    rw [mapGL_entry, mapGL_entry] at hDiv
    rw [mapGL_entry] at hd
    have hSame : (A 0 0 : ℝ) = (A 1 0 : ℝ) := by
      simpa only [one_mul] using (div_eq_iff hd).mp hDiv
    have hInt : A 0 0 = A 1 0 := by exact_mod_cast hSame
    rw [hInt, hc] at ha
    norm_num at ha

theorem zero_not_sent_to_one (g : GammaTwo) :
    mapGL ℝ (g : SL(2, ℤ)) • cuspZero ≠ cuspOne := by
  let A : SL(2, ℤ) := g
  have hA : A ∈ GammaTwo := g.property
  obtain ⟨_, hb, _, hd⟩ := CongruenceSubgroup.Gamma_mem.mp hA
  change mapGL ℝ A • ((0 : ℝ) : OnePoint ℝ) ≠ ((1 : ℝ) : OnePoint ℝ)
  rw [OnePoint.smul_some_eq_ite]
  simp only [mul_zero, zero_add, mapGL_entry]
  split_ifs with hc
  · simp
  · intro hEq
    have hDiv := OnePoint.coe_injective hEq
    have hSame : (A 0 1 : ℝ) = (A 1 1 : ℝ) := by
      simpa only [one_mul] using (div_eq_iff hc).mp hDiv
    have hInt : A 0 1 = A 1 1 := by exact_mod_cast hSame
    rw [hInt, hd] at hb
    norm_num at hb

theorem printed_cusp_transport_refuted :
    ¬ ∀ a : OnePoint ℝ, IsCusp a boundaryGroup →
      ∃ g : GammaTwo, mapGL ℝ (g : SL(2, ℤ)) • infinity = a := by
  intro h
  obtain ⟨g, hg⟩ := h cuspZero zero_isCusp
  exact infinity_not_sent_to_zero g hg

end
end ManuscriptAudit.Paper9CuspTransport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspTransport.infinity_isCusp,
      ``ManuscriptAudit.Paper9CuspTransport.zero_isCusp,
      ``ManuscriptAudit.Paper9CuspTransport.one_isCusp,
      ``ManuscriptAudit.Paper9CuspTransport.infinity_not_sent_to_zero,
      ``ManuscriptAudit.Paper9CuspTransport.infinity_not_sent_to_one,
      ``ManuscriptAudit.Paper9CuspTransport.zero_not_sent_to_one,
      ``ManuscriptAudit.Paper9CuspTransport.printed_cusp_transport_refuted] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
