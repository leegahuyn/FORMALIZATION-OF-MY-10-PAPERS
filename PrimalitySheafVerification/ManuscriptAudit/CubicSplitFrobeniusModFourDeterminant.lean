import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.FieldTheory.Finite.Extension
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitFrobeniusModFourPatterns
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitCubicExtensionTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicQuadraticTwistCounts
import PrimalitySheafVerification.ManuscriptAudit.QuadraticTwistModFourCount

/-! The actual determinant of split centered Frobenius modulo four. -/

namespace ManuscriptAudit.CubicSplitFrobeniusModFourDeterminant

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicTwoPowerTorsion
open CubicSplitTwoPowerFrobenius CubicNonsplitThreeAdicTrace TorsionFrobeniusModule

noncomputable section

private theorem card_subtype_of_all {X : Type*} {P : X → Prop} (h : ∀ x, P x) :
    Nat.card {x : X // P x} = Nat.card X :=
  Nat.card_congr
    { toFun := Subtype.val
      invFun := fun x => ⟨x, h x⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl }

private theorem fix_two_of_four {G : Type*} [AddCommGroup G] (f : AddMonoid.End G)
    (h : ∀ x : Torsion 4 G, (2 : ℕ) • x = 0 →
      (mapLinear 4 f ^ 3) x = x ∧ -(mapLinear 4 f ^ 3) x = x) (P : Torsion 2 G) :
    (mapLinear 2 f ^ 3) P = P ∧ -(mapLinear 2 f ^ 3) P = P := by
  have h2 : (2 : ℕ) • P.val = 0 := P.property
  let Q : Torsion 4 G := ⟨P.val, by
    change (4 : ℕ) • P.val = 0
    rw [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul', h2, nsmul_zero]⟩
  have hQ : (2 : ℕ) • Q = 0 := Subtype.ext h2
  exact ⟨Subtype.ext (congrArg Subtype.val (h Q hQ).1),
    Subtype.ext (congrArg Subtype.val (h Q hQ).2)⟩

private theorem finite_points {E : Type*} [Field E] [Fintype E] [DecidableEq E] (B : E) :
    Finite (Curve B).Point := by
  letI : Finite (WithZero {xy : E × E // (Curve B).Nonsingular xy.1 xy.2}) := by
    change Finite (Option {xy : E × E // (Curve B).Nonsingular xy.1 xy.2})
    infer_instance
  exact Finite.of_injective _ (Curve B).nonsingularPointEquiv.injective

private theorem card_eq_projective {E : Type*} [Field E] [DecidableEq E] (B : E) :
    Nat.card (Curve B).Point = Nat.card (shortCubic (0 : E) B).toProjective.Point :=
  Nat.card_congr
    (Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : E) B).toProjective)).symm.toEquiv

variable (K E L : Type*) [Field K] [Fintype K] [Field E] [Fintype E] [DecidableEq E]
  [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K E] [Algebra K L] [Algebra E L]

theorem determinant_eq_card_of_cubic_extension {A z : K} {d : E}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3)
    (hd : ¬ IsSquare d)
    (hCompat : algebraMap E L (algebraMap K E A) = algebraMap K L A)
    (hCard : Fintype.card E = (Fintype.card K) ^ 3)
    {k : ℕ} (hq : Fintype.card E = 6 * k + 1) :
    LinearMap.det (levelFrobenius K L A 2) = (Fintype.card K : ZMod 4) := by
  let F := levelFrobenius K L A 2
  let f := arithmeticPointFrobenius K L A
  let a := algebraMap K E A
  let b := d ^ 3 * a
  obtain ⟨hFix, hPat⟩ :=
    CubicSplitFrobeniusModFourPatterns.native_cube_fixed_patterns K L h₂ h₃ hA hz
  have h4 := CubicSplitCubicExtensionTorsion.cubic_extension_count_pair K E L
    4 h₂ h₃ hA hd hCompat hCard hq
  have h2 := CubicSplitCubicExtensionTorsion.cubic_extension_count_pair K E L
    2 h₂ h₃ hA hd hCompat hCard hq
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hAL : algebraMap K L A ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  have h2geom : Nat.card (Torsion 2 (GeometricPoints K L A)) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans (affine_twoPower_card h₂L h₃L hAL 1)
  have hFix2 := fix_two_of_four f hFix
  have h2a : Nat.card (Torsion 2 (Curve a).Point) = 4 :=
    h2.1.trans ((card_subtype_of_all (fun P => (hFix2 P).1)).trans h2geom)
  have h2b : Nat.card (Torsion 2 (Curve b).Point) = 4 :=
    h2.2.trans ((card_subtype_of_all (fun P => (hFix2 P).2)).trans h2geom)
  have h₂E : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr h₂
  have h₃E : (3 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr h₃
  have ha : a ≠ 0 := (map_ne_zero (algebraMap K E)).mpr hA
  have hSum : Nat.card (Curve a).Point + Nat.card (Curve b).Point =
      2 * (Fintype.card E + 1) := by
    rw [card_eq_projective a, card_eq_projective b]
    exact CubicQuadraticTwistCounts.projective_card_add h₂E h₃E ha hd
  letI : Finite (Curve a).Point := finite_points a
  letI : Finite (Curve b).Point := finite_points b
  have hdet : LinearMap.det F = (Fintype.card E : ZMod 4) := by
    apply QuadraticTwistModFourCount.determinant_eq_of_count_pair
      (Fintype.card E) (LinearMap.det F) h2a h2b hSum
    rw [h4.1, h4.2]
    exact hPat
  have hcases : LinearMap.det F = 1 ∨ LinearMap.det F = 3 := by
    rcases hPat with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hCube : ∀ x : ZMod 4, x ^ 3 = 1 ∨ x ^ 3 = 3 → x ^ 3 = x := by decide
  have hdPow : LinearMap.det F = (Fintype.card K : ZMod 4) ^ 3 := by
    simpa only [hCard, Nat.cast_pow] using hdet
  exact hdPow.trans (hCube _ (hdPow ▸ hcases))

/-- Over every finite split base of characteristic different from two and three, the
determinant of actual arithmetic Frobenius on geometric four-torsion is the field size. -/
theorem native_determinant_eq_card {A z : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3) :
    LinearMap.det (levelFrobenius K L A 2) = (Fintype.card K : ZMod 4) := by
  classical
  let p := ringChar K
  letI : CharP K p := ringChar.charP K
  letI : Fact (Nat.Prime p) := ⟨CharP.char_is_prime K p⟩
  let E := FiniteField.Extension K p 3
  letI : Fintype E := Fintype.ofFinite E
  let i : E →ₐ[K] L := IsAlgClosed.lift
  letI : Algebra E L := i.toRingHom.toAlgebra
  have hCompat : algebraMap E L (algebraMap K E A) = algebraMap K L A := i.commutes A
  have hCard : Fintype.card E = (Fintype.card K) ^ 3 := by
    have hN : Nat.card E = Nat.card K ^ 3 := FiniteField.natCard_extension K p 3
    simpa only [Nat.card_eq_fintype_card] using hN
  have h₂E : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr h₂
  have hchar : ringChar E ≠ 2 := by
    intro he
    exact h₂E ((ringChar.spec E 2).mpr (by simpa only [he] using (dvd_rfl : (2 : ℕ) ∣ 2)))
  obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare hchar
  obtain ⟨s, hs⟩ := FiniteField.odd_card_of_char_ne_two hchar
  have hzE := hz.map_of_injective (algebraMap K E).injective
  have hdv : 3 ∣ Fintype.card E - 1 := by
    rw [hzE.eq_orderOf]
    exact orderOf_dvd_of_pow_eq_one
      (FiniteField.pow_card_sub_one_eq_one _ (hzE.ne_zero (by decide)))
  have hq : Fintype.card E = 6 * (Fintype.card E / 6) + 1 := by
    have hpos : 0 < Fintype.card E := Fintype.card_pos
    omega
  exact determinant_eq_card_of_cubic_extension K E L h₂ h₃ hA hz hd hCompat hCard hq

end
end ManuscriptAudit.CubicSplitFrobeniusModFourDeterminant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSplitFrobeniusModFourDeterminant.determinant_eq_card_of_cubic_extension,
      ``ManuscriptAudit.CubicSplitFrobeniusModFourDeterminant.native_determinant_eq_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
