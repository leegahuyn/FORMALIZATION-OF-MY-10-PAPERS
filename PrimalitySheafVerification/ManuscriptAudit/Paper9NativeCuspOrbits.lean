import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspTransport
import PrimalitySheafVerification.ManuscriptAudit.ThreeCuspNeighborhoods

/-! The native Mathlib cusp orbit quotient for Γ(2) has representatives infinity, zero and one. -/

namespace ManuscriptAudit.Paper9NativeCuspOrbits

open Matrix SpecialLinearGroup ModularGroup OnePoint
open scoped MatrixGroups
open LiteralCuspTruncation (GammaTwo)
open Paper9CuspTransport
  (boundaryGroup infinity cuspZero cuspOne infinity_isCusp zero_isCusp one_isCusp
    infinity_not_sent_to_zero infinity_not_sent_to_one zero_not_sent_to_one)
open ThreeCuspNeighborhoods (chart coordinate_factorization)

noncomputable section

abbrev Cusp := cuspsSubMulAction boundaryGroup

private theorem mapGL_entry (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g) i j = (g i j : ℝ) := by
  change ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
  rw [mapGL_coe_matrix]
  rfl

theorem boundaryOrbit_eq_iff (a b : Cusp) :
    (Quotient.mk _ a : CuspOrbits boundaryGroup) = Quotient.mk _ b ↔
      ∃ g : GammaTwo, mapGL ℝ (g : SL(2, ℤ)) • (a : OnePoint ℝ) = (b : OnePoint ℝ) := by
  constructor
  · intro h
    have h' := Quotient.exact h.symm
    change ∃ γ : boundaryGroup, γ • a = b at h'
    obtain ⟨⟨w, hw⟩, he⟩ := h'
    change w ∈ GammaTwo.map (mapGL ℝ) at hw
    obtain ⟨g, hg, rfl⟩ := hw
    refine ⟨⟨g, hg⟩, ?_⟩
    exact congrArg (fun c : Cusp => (c : OnePoint ℝ)) he
  · rintro ⟨g, he⟩
    symm
    apply Quotient.sound
    change ∃ γ : boundaryGroup, γ • a = b
    let w : boundaryGroup := ⟨mapGL ℝ (g : SL(2, ℤ)), by
      change mapGL ℝ (g : SL(2, ℤ)) ∈ GammaTwo.map (mapGL ℝ)
      exact ⟨g, g.property, rfl⟩⟩
    exact ⟨w, Subtype.ext he⟩

def chartCusp (i : Fin 3) : Cusp :=
  ⟨mapGL ℝ (chart i) • infinity,
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z boundaryGroup).2
      (isCusp_SL2Z_iff'.2 ⟨chart i, rfl⟩)⟩

private theorem chartCusp_val_zero : (chartCusp 0 : OnePoint ℝ) = infinity := by
  change mapGL ℝ (chart 0) • infinity = infinity
  have h : chart 0 = 1 := rfl
  rw [h, map_one, one_smul]

private theorem chartCusp_val_one : (chartCusp 1 : OnePoint ℝ) = cuspZero := by
  change mapGL ℝ (chart 1) • (∞ : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ)
  have h : chart 1 = S := rfl
  have h10 : (mapGL ℝ S) 1 0 = 1 := by rw [mapGL_entry]; norm_num [ModularGroup.S]
  have h00 : (mapGL ℝ S) 0 0 = 0 := by rw [mapGL_entry]; norm_num [ModularGroup.S]
  rw [h, OnePoint.smul_infty_eq_ite]
  simp only [h10, h00, one_ne_zero, if_false, zero_div]

private theorem chartCusp_val_two : (chartCusp 2 : OnePoint ℝ) = cuspOne := by
  change mapGL ℝ (chart 2) • infinity = ((1 : ℝ) : OnePoint ℝ)
  have h : chart 2 = T * S := rfl
  have hs : mapGL ℝ S • infinity = cuspZero := chartCusp_val_one
  have h11 : (mapGL ℝ T) 1 1 = 1 := by rw [mapGL_entry]; norm_num [ModularGroup.T]
  have h01 : (mapGL ℝ T) 0 1 = 1 := by rw [mapGL_entry]; norm_num [ModularGroup.T]
  rw [h, map_mul, mul_smul, hs, cuspZero, OnePoint.smul_some_eq_ite]
  simp only [mul_zero, zero_add, h11, h01, one_ne_zero, if_false, div_one]

private theorem translation_fixes_infinity (m : ℤ) :
    mapGL ℝ (T ^ m) • (∞ : OnePoint ℝ) = ∞ := by
  rw [OnePoint.smul_infty_eq_self_iff, mapGL_entry]
  simp [ModularGroup.coe_T_zpow]

def classOfChart (i : Fin 3) : CuspOrbits boundaryGroup := Quotient.mk _ (chartCusp i)

theorem classOfChart_injective : Function.Injective classOfChart := by
  have h01 : classOfChart 0 ≠ classOfChart 1 := by
    intro h
    obtain ⟨g, hg⟩ := (boundaryOrbit_eq_iff (chartCusp 0) (chartCusp 1)).1 h
    rw [chartCusp_val_zero, chartCusp_val_one] at hg
    exact infinity_not_sent_to_zero g hg
  have h02 : classOfChart 0 ≠ classOfChart 2 := by
    intro h
    obtain ⟨g, hg⟩ := (boundaryOrbit_eq_iff (chartCusp 0) (chartCusp 2)).1 h
    rw [chartCusp_val_zero, chartCusp_val_two] at hg
    exact infinity_not_sent_to_one g hg
  have h12 : classOfChart 1 ≠ classOfChart 2 := by
    intro h
    obtain ⟨g, hg⟩ := (boundaryOrbit_eq_iff (chartCusp 1) (chartCusp 2)).1 h
    rw [chartCusp_val_one, chartCusp_val_two] at hg
    exact zero_not_sent_to_one g hg
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals
    first
    | rfl
    | exact (h01 h).elim
    | exact (h01 h.symm).elim
    | exact (h02 h).elim
    | exact (h02 h.symm).elim
    | exact (h12 h).elim
    | exact (h12 h.symm).elim

theorem classOfChart_surjective : Function.Surjective classOfChart := by
  intro b
  refine Quotient.inductionOn b ?_
  intro a
  have ha : IsCusp (a : OnePoint ℝ) boundaryGroup := a.property
  have hSL := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z boundaryGroup).1 ha
  obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.1 hSL
  obtain ⟨i, m, γ, hFactor⟩ := coordinate_factorization g
  refine ⟨i, (boundaryOrbit_eq_iff (chartCusp i) a).2 ⟨γ, ?_⟩⟩
  change mapGL ℝ (γ : SL(2, ℤ)) • (mapGL ℝ (chart i) • infinity) = (a : OnePoint ℝ)
  rw [hg, hFactor, map_mul, map_mul, mul_smul, mul_smul, translation_fixes_infinity]

def chartEquiv : Fin 3 ≃ CuspOrbits boundaryGroup :=
  Equiv.ofBijective classOfChart ⟨classOfChart_injective, classOfChart_surjective⟩

theorem cusp_orbit_card : Nat.card (CuspOrbits boundaryGroup) = 3 := by
  rw [← Nat.card_congr chartEquiv]
  simp

end
end ManuscriptAudit.Paper9NativeCuspOrbits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9NativeCuspOrbits.boundaryOrbit_eq_iff,
      ``ManuscriptAudit.Paper9NativeCuspOrbits.classOfChart_injective,
      ``ManuscriptAudit.Paper9NativeCuspOrbits.classOfChart_surjective,
      ``ManuscriptAudit.Paper9NativeCuspOrbits.cusp_orbit_card] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
