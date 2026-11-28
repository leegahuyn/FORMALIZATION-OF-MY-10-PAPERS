import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsCounting
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeRayleighCount

/-! The variational count for the actual unshifted realization uses the
original energy on the same form domain. -/

namespace ManuscriptAudit.Paper10UnshiftedRayleighCount

open Paper10FriedrichsResolvent Paper10FriedrichsEigenbasis
open Paper10RelativeRayleighCount

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The counted labels of the actual unshifted graph agree with the strict
Rayleigh count for the original unshifted form. -/
theorem isRayleighCount
    (J : D →L[ℝ] H) (hJ : DenseRange J) (hInj : Function.Injective J)
    (hK : IsCompactOperator J)
    (b : HilbertBasis (EigenIndex J) ℝ H)
    (hb : ∀ i, (b i, i.1 • b i) ∈ (realization J).graph)
    (Q : D → ℝ) (c R : ℝ) (hQ : ∀ u, ‖u‖^2 = Q u + c * ‖J u‖^2) :
    IsRayleighCount Q (fun u => ‖J u‖^2) R
      (Nat.card {i : EigenIndex J // i.1 - c < R}) := by
  let E : {i : EigenIndex J // i.1 < R+c} ≃ {i : EigenIndex J // i.1-c < R} :=
    { toFun := fun i => ⟨i.val, sub_lt_iff_lt_add.mpr i.property⟩
      invFun := fun i => ⟨i.val, sub_lt_iff_lt_add.mp i.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  have hCard := Nat.card_congr E
  have hBound (u : D) :
      Q u < R * ‖J u‖^2 ↔ ‖u‖^2 < (R+c) * ‖J u‖^2 := by
    rw [hQ u, add_mul, add_lt_add_iff_right]
  obtain ⟨⟨V, hV, hVR⟩, hMax⟩ :=
    Paper10FriedrichsCounting.variational_count J hJ hInj hK b hb (R+c)
  refine ⟨⟨V, hV.trans hCard, fun u hu => (hBound u).mpr (hVR u hu)⟩, ?_⟩
  intro W hW
  exact (hMax W (fun u hu => (hBound u).mp (hW u hu))).trans hCard.le

end
end ManuscriptAudit.Paper10UnshiftedRayleighCount

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10UnshiftedRayleighCount.isRayleighCount
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
