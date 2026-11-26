import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiBound

/-! The native cubic character counts every fiber of the cube map. -/

namespace ManuscriptAudit.CubicCharacterMultiplicity

open CubicJacobiBound

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem orderThree_not_one {χ : MulChar F ℂ} (hχ : orderOf χ = 3) : χ ≠ 1 := by
  intro e
  rw [e, orderOf_one] at hχ
  exact (by decide : (1 : ℕ) ≠ 3) hχ

private theorem orderThree_pow_three {χ : MulChar F ℂ} (hχ : orderOf χ = 3) : χ ^ 3 = 1 := by
  simpa only [hχ] using pow_orderOf_eq_one χ

private theorem orderThree_value {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {z : F}
    (hz : z ≠ 0) : χ z ^ 3 = 1 := by
  rw [← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0) z, orderThree_pow_three hχ,
    MulChar.one_apply hz.isUnit]

private theorem cube_iff_character_one {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {z : F}
    (hz : z ≠ 0) : (∃ x : F, x ^ 3 = z) ↔ χ z = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ≠ 0 := by
      intro he
      apply hz
      simp [he]
    rw [map_pow, orderThree_value hχ hx]
  · intro he
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    let u := Units.mk0 z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    have hgen_ne : χ.toUnitHom g ≠ 1 := by
      intro eg
      apply orderThree_not_one hχ
      apply MulChar.equivToUnitHom.injective
      change χ.toUnitHom = (1 : MulChar F ℂ).toUnitHom
      apply (MonoidHom.eq_iff_eq_on_generator hg _ _).mpr
      rw [eg]
      apply Units.ext
      change (1 : ℂ) = (1 : MulChar F ℂ) (g : F)
      exact (MulChar.one_apply_coe g).symm
    have hord : orderOf (χ.toUnitHom g) = 3 := by
      apply (orderOf_eq_prime_iff (p := 3)).mpr
      refine ⟨Units.ext ?_, hgen_ne⟩
      change χ (g : F) ^ 3 = 1
      exact orderThree_value hχ g.ne_zero
    have hu : χ.toUnitHom u = 1 := Units.ext he
    have hzpow : (χ.toUnitHom g) ^ k = 1 := by
      rw [← map_zpow, hk, hu]
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hzpow
    rw [hord] at hd
    obtain ⟨a, ha⟩ := hd
    have hx : (g ^ a) ^ (3 : ℕ) = u := by
      calc
        _ = (g ^ a) ^ (3 : ℤ) := rfl
        _ = g ^ (a * (3 : ℤ)) := (zpow_mul g a 3).symm
        _ = g ^ k := congrArg (fun j : ℤ => g ^ j) ((mul_comm a 3).trans ha.symm)
        _ = u := hk
    exact ⟨(g ^ a : Fˣ), congrArg (fun v : Fˣ => (v : F)) hx⟩

private def cubeFiberUnits {z : F} (hz : z ≠ 0) :
    {x : F // x ^ 3 = z} ≃ {u : Fˣ // u ^ (3 : ℕ) = Units.mk0 z hz} where
  toFun x := ⟨Units.mk0 x.val (by
    intro h
    apply hz
    simpa [h] using x.property.symm), Units.ext x.property⟩
  invFun u := ⟨u.val, congrArg (fun v : Fˣ => (v : F)) u.property⟩
  left_inv _ := rfl
  right_inv u := Subtype.ext (Units.ext rfl)

private def unitFiberKernel (u : Fˣ) :
    {x : Fˣ // x ^ (3 : ℕ) = u ^ (3 : ℕ)} ≃ (powMonoidHom 3 : Fˣ →* Fˣ).ker where
  toFun x := ⟨x.val * u⁻¹, by
    change (x.val * u⁻¹) ^ (3 : ℕ) = 1
    rw [mul_pow, inv_pow, x.property, mul_inv_cancel]⟩
  invFun y := ⟨y.val * u, by
    have hy : y.val ^ (3 : ℕ) = 1 := y.property
    rw [mul_pow, hy, one_mul]⟩
  left_inv x := Subtype.ext (by change x.val * u⁻¹ * u = x.val; simp [mul_assoc])
  right_inv y := Subtype.ext (by change y.val * u * u⁻¹ = y.val; simp [mul_assoc])

private theorem cubeMultiplicity_eq_three (hdiv : 3 ∣ Fintype.card F - 1)
    {z : F} (hz : z ≠ 0) (h : ∃ x : F, x ^ 3 = z) : cubeMultiplicity z = 3 := by
  obtain ⟨x, hx⟩ := h
  have hn : x ≠ 0 := by
    intro h
    apply hz
    simpa [h] using hx.symm
  let u := Units.mk0 x hn
  have hu : Units.mk0 z hz = u ^ (3 : ℕ) := Units.ext hx.symm
  have he := Nat.card_congr (cubeFiberUnits hz)
  rw [hu] at he
  have hGcd : (Fintype.card F - 1).gcd 3 = 3 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd hdiv (dvd_refl 3))
  calc
    _ = Nat.card {x : F // x ^ 3 = z} := Nat.card_eq_fintype_card.symm
    _ = _ := he
    _ = Nat.card (powMonoidHom 3 : Fˣ →* Fˣ).ker := Nat.card_congr (unitFiberKernel u)
    _ = (Nat.card Fˣ).gcd 3 := IsCyclic.card_powMonoidHom_ker (Fˣ) 3
    _ = 3 := by rw [Nat.card_eq_fintype_card, Fintype.card_units, hGcd]

/-- Every cube fiber has exactly the multiplicity given by the order-three character. -/
theorem cubeMultiplicity_character (hdiv : 3 ∣ Fintype.card F - 1)
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (z : F) :
    (cubeMultiplicity z : ℂ) = 1 + χ z + (χ ^ 2) z := by
  classical
  rcases eq_or_ne z 0 with rfl | hz
  · letI : Unique {x : F // x ^ 3 = 0} :=
      { default := ⟨0, by simp⟩
        uniq := fun x => Subtype.ext (by
          by_contra h
          exact pow_ne_zero 3 h x.property) }
    rw [χ.map_zero, (χ ^ 2).map_zero]
    simp [cubeMultiplicity]
  · rw [MulChar.pow_apply' χ (by decide : (2 : ℕ) ≠ 0)]
    by_cases h : χ z = 1
    · rw [cubeMultiplicity_eq_three hdiv hz ((cube_iff_character_one hχ hz).mpr h), h]
      norm_num
    · have hc : ¬ ∃ x : F, x ^ 3 = z :=
        fun hx => h ((cube_iff_character_one hχ hz).mp hx)
      letI : IsEmpty {x : F // x ^ 3 = z} := ⟨fun x => hc ⟨x.val, x.property⟩⟩
      have hf : (χ z - 1) * (1 + χ z + χ z ^ 2) = 0 := by
        calc
          _ = χ z ^ 3 - 1 := by ring
          _ = 0 := by rw [orderThree_value hχ hz, sub_self]
      have hb : 1 + χ z + χ z ^ 2 = 0 :=
        (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr h)
      have hzero : cubeMultiplicity z = 0 := by simp [cubeMultiplicity]
      rw [hzero, Nat.cast_zero, hb]

theorem exists_orderThree_character (hdiv : 3 ∣ Fintype.card F - 1) :
    ∃ χ : MulChar F ℂ, orderOf χ = 3 :=
  MulChar.exists_mulChar_orderOf F hdiv (Complex.isPrimitiveRoot_exp 3 (by decide))

end
end ManuscriptAudit.CubicCharacterMultiplicity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CubicCharacterMultiplicity.cubeMultiplicity_character,
      ``ManuscriptAudit.CubicCharacterMultiplicity.exists_orderThree_character] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
