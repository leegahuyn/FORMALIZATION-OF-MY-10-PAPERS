import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicAllGoodFiniteFieldTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5GoodPrimeTateInverse

/-! Actual relative inverse Frobenius and its algebraic dual over the coefficient field. -/

namespace ManuscriptAudit.CubicFiniteFieldTateInverse

open Module PowerTateModule
open CubicNonsplitThreeAdicTrace (GeometricPoints)
open CubicAllGoodFiniteFieldTate (basis relative relative_eq_power power_trace_det)
open CubicSplitExtensionTraceRecurrence (signedTrace)
open Paper5GeometricFrobeniusInverse (determinant_baseChange)
open RankTwoInverseTrace FrobeniusDualConvention
open scoped TensorProduct Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (E L D : Type)
  [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E] [CharP E p]
  [Field L] [DecidableEq L] [Algebra E L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [Algebra.IsAlgebraic (ZMod p) L]
  [Field D] [Fintype D] [DecidableEq D] [Algebra E D]
  [Algebra (ZMod p) D] [CharP D p] [IsScalarTower (ZMod p) E D]
  [Algebra D L] [IsScalarTower E D L]
variable (l : ℕ) [Fact l.Prime]

abbrev RationalTate (A : E) :=
  ℚ_[l] ⊗[ℤ_[l]] Tate l (GeometricPoints E L A)

/-- Both the geometric inverse and its dual have the exact arithmetic coefficients
over every relative good finite field and every coefficient prime distinct from the characteristic. -/
theorem relative_inverse_dual_coefficients (hp : 5 ≤ p) (hl : p ≠ l)
    {A : E} (hA : A ≠ 0) :
    let t : ℚ_[l] := signedTrace (algebraMap E D A)
    let q : ℚ_[l] := Fintype.card D
    ∃ e : RationalTate E L l A ≃ₗ[ℚ_[l]] RationalTate E L l A,
      e.toLinearMap = (relative E L l D A).baseChange ℚ_[l] ∧
      LinearMap.trace ℚ_[l] (RationalTate E L l A) e.symm.toLinearMap = t/q ∧
      LinearMap.det e.symm.toLinearMap = q⁻¹ ∧
      LinearMap.trace ℚ_[l] (Module.Dual ℚ_[l] (RationalTate E L l A)) (dualAction e.symm) = t ∧
      LinearMap.det (dualAction e.symm) = q := by
  let G := relative E L l D A
  let F := G.baseChange ℚ_[l]
  let t : ℚ_[l] := signedTrace (algebraMap E D A)
  let q : ℚ_[l] := Fintype.card D
  let B := basis p E L l hp hA hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let b := Algebra.TensorProduct.basis ℚ_[l] B
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  have h := power_trace_det p E L l D hp hA hl
  dsimp only at h
  have hTG : LinearMap.trace ℤ_[l] _ G = (signedTrace (algebraMap E D A) : ℤ_[l]) := by
    dsimp only [G]
    rw [relative_eq_power]
    exact h.1
  have hDG : LinearMap.det G = (Fintype.card D : ℤ_[l]) := by
    dsimp only [G]
    rw [relative_eq_power]
    exact h.2
  have ht : LinearMap.trace ℚ_[l] (RationalTate E L l A) F = t := by
    dsimp only [F, t]
    rw [LinearMap.trace_baseChange, hTG, map_intCast]
  have hd : LinearMap.det F = q := by
    dsimp only [F, q]
    rw [determinant_baseChange B, hDG, map_natCast]
  have hq : q ≠ 0 := by
    change (Fintype.card D : ℚ_[l]) ≠ 0
    exact_mod_cast (show Fintype.card D ≠ 0 from Fintype.card_pos.ne')
  let e := LinearMap.equivOfDetNeZero F (hd.symm ▸ hq)
  have he : e.toLinearMap = F := rfl
  have hDual := inverse_generator_coefficients b e
  rw [he, ht, hd] at hDual
  refine ⟨e, he, ?_, ?_, hDual.1, hDual.2⟩
  · apply (eq_div_iff hq).mpr
    have hi := determinant_mul_trace_inverse b e
    rw [he, ht, hd] at hi
    exact (mul_comm _ _).trans hi
  · rw [LinearEquiv.det_coe_symm, he, hd]

end
end ManuscriptAudit.CubicFiniteFieldTateInverse

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicFiniteFieldTateInverse.relative_inverse_dual_coefficients
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
