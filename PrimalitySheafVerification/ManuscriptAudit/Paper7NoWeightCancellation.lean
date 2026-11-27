import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import PrimalitySheafVerification.ManuscriptAudit.ReciprocalWeight

/-! Distinct exact weights prevent cancellation between the two parity products. -/

namespace ManuscriptAudit.Paper7NoWeightCancellation

open Matrix Polynomial Paper07
open scoped BigOperators

noncomputable section

variable {ι : ℕ → Type} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]

def evenProduct (I : Finset ℕ) (F : ∀ i, Matrix (ι i) (ι i) ℂ) : ℂ[X] := by
  classical
  exact ∏ i ∈ I.filter (fun i => Even i), (F i).charpolyRev

def oddProduct (I : Finset ℕ) (F : ∀ i, Matrix (ι i) (ι i) ℂ) : ℂ[X] := by
  classical
  exact ∏ i ∈ I.filter (fun i => ¬ Even i), (F i).charpolyRev

theorem common_reciprocal_root_weight_eq {q : ℝ} (hq : 1 < q)
    {i j : ℕ} (F : ∀ r, Matrix (ι r) (ι r) ℂ) (w : ℕ → ℝ)
    (hi : ∀ α : ℂ, (F i).charpoly.IsRoot α → ‖α‖ = q ^ (w i / 2))
    (hj : ∀ α : ℂ, (F j).charpoly.IsRoot α → ‖α‖ = q ^ (w j / 2))
    {z : ℂ} (hzi : (F i).charpolyRev.IsRoot z) (hzj : (F j).charpolyRev.IsRoot z) :
    w i = w j := by
  have he := (hi z⁻¹ ((charpolyRev_isRoot_iff (F i) z).mp hzi).2).symm.trans
    (hj z⁻¹ ((charpolyRev_isRoot_iff (F j) z).mp hzj).2)
  have hp := (Real.strictMono_rpow_of_base_gt_one hq).injective he
  linarith only [hp]

theorem parity_products_coprime (I : Finset ℕ) (F : ∀ i, Matrix (ι i) (ι i) ℂ)
    {q : ℝ} (hq : 1 < q) (w : ℕ → ℝ) (hW : Set.InjOn w (↑I : Set ℕ))
    (hPure : ∀ i ∈ I, ∀ α : ℂ, (F i).charpoly.IsRoot α → ‖α‖ = q ^ (w i / 2)) :
    IsCoprime (evenProduct I F) (oddProduct I F) := by
  classical
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ
    (evenProduct I F) (oddProduct I F)).mpr
  intro z
  by_contra! h
  obtain ⟨he, ho⟩ := h
  rw [evenProduct, map_prod] at he
  rw [oddProduct, map_prod] at ho
  obtain ⟨i, hi, hri⟩ := Finset.prod_eq_zero_iff.mp he
  obtain ⟨j, hj, hrj⟩ := Finset.prod_eq_zero_iff.mp ho
  obtain ⟨hiI, hiEven⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjI, hjOdd⟩ := Finset.mem_filter.mp hj
  have hRi : (F i).charpolyRev.IsRoot z := by
    exact hri
  have hRj : (F j).charpolyRev.IsRoot z := by
    exact hrj
  have hij : i = j :=
    hW hiI hjI (common_reciprocal_root_weight_eq hq F w (hPure i hiI) (hPure j hjI) hRi hRj)
  exact hjOdd (hij ▸ hiEven)

end
end ManuscriptAudit.Paper7NoWeightCancellation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7NoWeightCancellation.common_reciprocal_root_weight_eq,
      ``ManuscriptAudit.Paper7NoWeightCancellation.parity_products_coprime] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
