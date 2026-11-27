import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeFrobeniusSigns
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! Actual finite-field point counts modulo three on the centered cubic. -/

namespace ManuscriptAudit.CubicThreePointCounts

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicThreeTorsionOrdinate CubicThreeFrobeniusSigns

noncomputable section

variable {E : Type*} [Field E] [DecidableEq E]

abbrev SquareRoots (A : E) := {y : E // y ^ 2 = A}

private abbrev AffineCoordinates (A : E) := {xy : E × E // xy.2 ^ 2 = xy.1 ^ 3 + A}

private abbrev Nonvertical (A : E) := {xy : AffineCoordinates A // xy.val.1 ≠ 0}

private def verticalEquiv (A : E) :
    {xy : AffineCoordinates A // xy.val.1 = 0} ≃ SquareRoots A where
  toFun xy := ⟨xy.val.val.2, by simpa [xy.property] using xy.val.property⟩
  invFun y := ⟨⟨(0, y.val), by simpa using y.property⟩, rfl⟩
  left_inv xy := Subtype.ext (Subtype.ext (Prod.ext xy.property.symm rfl))
  right_inv y := Subtype.ext rfl

private def pointCoordinates (A : E) (hΔ : (shortCubic (0 : E) A).Δ ≠ 0) :
    (shortCubic (0 : E) A).toProjective.Point ≃ Option (AffineCoordinates A) :=
  (Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : E) A).toProjective)).toEquiv.trans
    ((Affine.nonsingularPointEquiv (Curve A)).trans
      (Equiv.optionCongr (Equiv.subtypeEquivRight
        (fun xy : E × E => nonsingular_iff hΔ xy.1 xy.2))))

private abbrev CubeImage (A : E) :=
  {c : E × E // (∃ x : E, x ^ 3 = c.1 ∧ x ≠ 0) ∧ c.2 ^ 2 = c.1 + A}

private def nonverticalEquiv (A : E) :
    Nonvertical A ≃ Σ c : CubeImage A, {x : E // x ^ 3 = c.val.1} where
  toFun xy := ⟨⟨(xy.val.val.1 ^ 3, xy.val.val.2),
    ⟨xy.val.val.1, rfl, xy.property⟩, xy.val.property⟩, ⟨xy.val.val.1, rfl⟩⟩
  invFun
    | ⟨c, x⟩ => ⟨⟨(x.val, c.val.2), by rw [x.property]; exact c.property.2⟩, by
        obtain ⟨r, hr, hr₀⟩ := c.property.1
        intro h0
        have hx0 : x.val = 0 := h0
        have hx : x.val ^ 3 = c.val.1 := x.property
        rw [hx0, zero_pow (by decide : (3 : ℕ) ≠ 0)] at hx
        exact (pow_ne_zero 3 hr₀) (hr.trans hx.symm)⟩
  left_inv xy := rfl
  right_inv := by
    rintro ⟨⟨⟨c, y⟩, hc⟩, ⟨x, hx⟩⟩
    change x ^ 3 = c at hx
    subst c
    rfl

private def cubicUnityEquiv {z : E} (hz : IsPrimitiveRoot z 3) :
    Fin 3 ≃ {x : E // x ^ 3 = 1} :=
  Equiv.ofBijective (fun i => ⟨z ^ i.val, by rw [← pow_mul, Nat.mul_comm, pow_mul,
    hz.pow_eq_one, one_pow]⟩) (by
    constructor
    · intro i j h
      exact Fin.ext (hz.pow_inj i.isLt j.isLt (congrArg Subtype.val h))
    · intro x
      obtain ⟨i, hi, he⟩ := hz.eq_pow_of_pow_eq_one x.property
      exact ⟨⟨i, hi⟩, Subtype.ext he⟩)

private def cubeFiberEquiv (c r : E) (h : r ^ 3 = c) (hr : r ≠ 0) :
    {x : E // x ^ 3 = c} ≃ {x : E // x ^ 3 = 1} where
  toFun x := ⟨x.val / r, by rw [div_pow, x.property, ← h, div_self (pow_ne_zero _ hr)]⟩
  invFun x := ⟨x.val * r, by rw [mul_pow, x.property, one_mul, h]⟩
  left_inv x := Subtype.ext (div_mul_cancel₀ _ hr)
  right_inv x := Subtype.ext (mul_div_cancel_right₀ _ hr)

variable [Fintype E]

private theorem nonvertical_card_dvd_three (A : E) {z : E} (hz : IsPrimitiveRoot z 3) :
    3 ∣ Nat.card (Nonvertical A) := by
  classical
  let e (c : CubeImage A) : {x : E // x ^ 3 = c.val.1} ≃ Fin 3 :=
    (cubeFiberEquiv c.val.1 c.property.1.choose c.property.1.choose_spec.1
      c.property.1.choose_spec.2).trans (cubicUnityEquiv hz).symm
  let eqv := (nonverticalEquiv A).trans (Equiv.sigmaEquivProdOfEquiv e)
  letI : Fintype (CubeImage A) := Fintype.ofFinite _
  rw [Nat.card_congr eqv, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
  exact dvd_mul_left 3 _

private theorem point_count_split (A : E) (hΔ : (shortCubic (0 : E) A).Δ ≠ 0) :
    Nat.card (shortCubic (0 : E) A).toProjective.Point =
      Nat.card (SquareRoots A) + Nat.card (Nonvertical A) + 1 := by
  classical
  let e : AffineCoordinates A ≃ (SquareRoots A ⊕ Nonvertical A) :=
    (Equiv.sumCompl (fun xy : AffineCoordinates A => xy.val.1 = 0)).symm.trans
      (Equiv.sumCongr (verticalEquiv A) (Equiv.refl _))
  letI : Fintype (SquareRoots A) := Fintype.ofFinite _
  letI : Fintype (Nonvertical A) := Fintype.ofFinite _
  rw [Nat.card_congr ((pointCoordinates A hΔ).trans (Equiv.optionCongr e)),
    Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sum,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]

private def cubeEquiv (hq : Fintype.card E % 3 = 2) : E ≃ E := by
  let q := Fintype.card E
  let d := (2 * q - 1) / 3
  have he : 3 * d = (q - 1) * 2 + 1 := by
    dsimp [d, q]
    omega
  have hpow (x : E) : x ^ (3 * d) = x := by
    by_cases hx : x = 0
    · rw [hx, zero_pow (by omega : 3 * d ≠ 0)]
    · rw [he, pow_add, pow_one, pow_mul, FiniteField.pow_card_sub_one_eq_one x hx,
        one_pow, one_mul]
  refine ⟨fun x => x ^ 3, fun x => x ^ d, fun x => ?_, fun x => ?_⟩
  · simpa only [← pow_mul] using hpow x
  · simpa only [← pow_mul, Nat.mul_comm d (3 : ℕ)] using hpow x

private def cubicGraphEquiv (A : E) (hq : Fintype.card E % 3 = 2) : AffineCoordinates A ≃ E := by
  let e := cubeEquiv hq
  refine ⟨fun xy => xy.val.2, fun y => ⟨(e.symm (y ^ 2 - A), y), ?_⟩, ?_, fun _ => rfl⟩
  · change y ^ 2 = (e.symm (y ^ 2 - A)) ^ 3 + A
    have he : (e.symm (y ^ 2 - A)) ^ 3 = y ^ 2 - A := e.apply_symm_apply _
    rw [he, sub_add_cancel]
  · rintro ⟨⟨x, y⟩, h⟩
    refine Subtype.ext (Prod.ext (e.injective ?_) rfl)
    rw [e.apply_symm_apply]
    change y ^ 2 - A = x ^ 3
    exact sub_eq_iff_eq_add.mpr h

/-- When cubing is a bijection, the native projective point count is exactly q+1. -/
theorem projective_count_residue_two (A : E) (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq : Fintype.card E % 3 = 2) :
    Nat.card (shortCubic (0 : E) A).toProjective.Point = Fintype.card E + 1 := by
  let e := (pointCoordinates A (shortCubic_discriminant_ne_zero h₂ h₃ hA)).trans
    (Equiv.optionCongr (cubicGraphEquiv A hq))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option]

/-- For q congruent to one, the native signed point trace is 1 minus the square root count mod 3. -/
theorem signed_count_residue_one (A : E) (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq : Fintype.card E % 3 = 1) :
    (((Fintype.card E : ℤ) + 1 - (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ)) :
      ZMod 3) = 1 - (Nat.card (SquareRoots A) : ZMod 3) := by
  obtain ⟨z, hz⟩ := finite_exists_primitive_cube_root hq
  have hn : (Nat.card (Nonvertical A) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (nonvertical_card_dvd_three A hz)
  have hq' : (Fintype.card E : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod (Fintype.card E) 3, hq, Nat.cast_one]
  rw [point_count_split A (shortCubic_discriminant_ne_zero h₂ h₃ hA)]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
    hn, hq']
  ring

end
end ManuscriptAudit.CubicThreePointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreePointCounts.projective_count_residue_two,
      ``ManuscriptAudit.CubicThreePointCounts.signed_count_residue_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
