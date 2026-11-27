import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.NumberTheory.Padics.RingHoms

/-! The exact index of an injective rank-two p-adic map is its determinant valuation. -/

namespace ManuscriptAudit.PadicDeterminantIndex

open Module Submodule

noncomputable section

variable (l : ℕ) [Fact l.Prime]

private theorem unit_valuation (u : ℤ_[l]ˣ) : (u : ℤ_[l]).valuation = 0 := by
  have h := PadicInt.valuation_mul u.ne_zero (u⁻¹ : ℤ_[l]ˣ).ne_zero
  have he : (u : ℤ_[l]) * ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := u.mul_inv
  rw [he, PadicInt.valuation_one] at h
  omega

private theorem valuation_associated {x y : ℤ_[l]} (h : Associated x y) :
    x.valuation = y.valuation := by
  obtain ⟨u, hu⟩ := h
  by_cases hx : x = 0
  · rw [hx, zero_mul] at hu
    rw [hx, ← hu]
  · rw [← hu, PadicInt.valuation_mul hx u.ne_zero, unit_valuation, add_zero]

/-- A nonzero principal ideal has quotient of order p to the generator's valuation. -/
theorem card_quotient_span (x : ℤ_[l]) (hx : x ≠ 0) :
    Nat.card (ℤ_[l] ⧸ Ideal.span ({x} : Set ℤ_[l])) = l ^ x.valuation := by
  let u := PadicInt.unitCoeff hx
  let a := (l : ℤ_[l]) ^ x.valuation
  have h : Ideal.span ({x} : Set ℤ_[l]) = Ideal.span ({a} : Set ℤ_[l]) := by
    calc
      _ = Ideal.span ({(u : ℤ_[l]) * a} : Set ℤ_[l]) :=
        congrArg (fun y : ℤ_[l] => Ideal.span ({y} : Set ℤ_[l])) (PadicInt.unitCoeff_spec hx)
      _ = _ := Ideal.span_singleton_mul_left_unit u.isUnit a
  let f : ℤ_[l] →+* ZMod (l ^ x.valuation) := PadicInt.toZModPow x.valuation
  let e := (Ideal.quotEquivOfEq (h.trans (PadicInt.ker_toZModPow x.valuation).symm)).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective f))
  exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)

/-- The index formula uses the actual cokernel of the native p-adic linear map. -/
theorem card_quotient_range {V : Type*} [AddCommGroup V] [Module ℤ_[l] V]
    (B : Basis (Fin 2) ℤ_[l] V) (f : Module.End ℤ_[l] V) (hf : Function.Injective f) :
    Nat.card (V ⧸ LinearMap.range f) = l ^ (LinearMap.det f).valuation := by
  let N := LinearMap.range f
  let e : V ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective f hf
  have h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] V := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs B h
  let D := Submodule.smithNormalFormTopBasis B h
  let C := Submodule.smithNormalFormBotBasis B h
  let e' : V ≃ₗ[ℤ_[l]] N := D.equiv C (Equiv.refl _)
  let F : Module.End ℤ_[l] V := N.subtype.comp e'.toLinearMap
  have hAssoc : Associated (LinearMap.det f) (LinearMap.det F) :=
    LinearMap.associated_det_comp_equiv N.subtype e e'
  have ha (i : Fin 2) : F (D i) = a i • D i := by
    change (D.equiv C (Equiv.refl _) (D i) : V) = _
    rw [D.equiv_apply, Equiv.refl_apply]
    exact Submodule.smithNormalFormBotBasis_def B h i
  have hM : LinearMap.toMatrix D D F = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hDet : LinearMap.det F = a 0 * a 1 := by
    rw [← LinearMap.det_toMatrix D, hM, Matrix.det_diagonal, Fin.prod_univ_two]
  have ha₀ : a 0 ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero B h 0
  have ha₁ : a 1 ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero B h 1
  have hVal : (LinearMap.det f).valuation = (a 0).valuation + (a 1).valuation := by
    rw [valuation_associated l hAssoc, hDet, PadicInt.valuation_mul ha₀ ha₁]
  let c := N.quotientEquivPiSpan B h
  change Nat.card (V ⧸ N) = _
  rw [Nat.card_congr c.toEquiv, Nat.card_pi, Fin.prod_univ_two]
  rw [card_quotient_span l (a 0) ha₀, card_quotient_span l (a 1) ha₁, ← pow_add, hVal]

end
end ManuscriptAudit.PadicDeterminantIndex

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicDeterminantIndex.card_quotient_span,
      ``ManuscriptAudit.PadicDeterminantIndex.card_quotient_range] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
