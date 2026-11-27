import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicHermitianRegularPoints
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsion

/-! For the centered nonsplit cubic the actual square of Frobenius is multiplication by −q. -/

namespace ManuscriptAudit.CubicHermitianFrobeniusSquare

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion
open CubicThreeTorsion CubicThreeTorsionCard CubicThreeTorsionOrdinate
open CubicHermitianCoordinates CubicHermitianFiniteInputs CubicHermitianRegularPoints

noncomputable section

private theorem add_nsmul_eq_zero_of_dvd {G : Type*} [AddCommGroup G]
    {q d : ℕ} (h : d ∣ q + 1) (P : G) (hP : d • P = 0) : q • P + P = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [← succ_nsmul, Nat.succ_eq_add_one, hk, Nat.mul_comm d k, mul_nsmul, hP, nsmul_zero]

variable (E K : Type*) [Field E] [Fintype E] [Field K] [Algebra E K] [IsAlgClosed K] [DecidableEq K]

local notation "q" => Fintype.card E
local notation "Q" => (q * q)

theorem some_frobenius_relation {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1)
    {x y : K} (hP : (Centered (algebraMap E K A)).Nonsingular x y)
    (hP' : (Centered (algebraMap E K A)).Nonsingular (x ^ Q) (y ^ Q)) :
    q • (Affine.Point.some x y hP : (Centered (algebraMap E K A)).Point) +
      Affine.Point.some (x ^ Q) (y ^ Q) hP' = 0 := by
  let c := algebraMap E K A
  have hc : c ≠ 0 := by simpa only [c, map_zero] using (algebraMap E K).injective.ne hA
  have h₂' : (2 : K) ≠ 0 := by simpa using (algebraMap E K).injective.ne h₂
  have h₃' : (3 : K) ≠ 0 := by simpa using (algebraMap E K).injective.ne h₃
  have hΔ := shortCubic_discriminant_ne_zero h₂' h₃' hc
  have hXY : y ^ 2 = x ^ 3 + c := (nonsingular_iff hΔ x y).mp hP
  have hQ : Q ≠ 0 := Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero
  by_cases hx : x = 0
  · have hyA : y ^ 2 = c := by simpa [hx] using hXY
    have hy₀ : y ≠ 0 := fun h => hc (by simpa [h] using hyA.symm)
    have hd : 3 ∣ q + 1 := by omega
    have hy' : y ^ Q = y := root_frobenius_sq_fixed E K (by omega : 2 ∣ q + 1) hA hyA
    have hx' : x ^ Q = x := by rw [hx, zero_pow hQ]
    have he : Affine.Point.some (x ^ Q) (y ^ Q) hP' =
        (Affine.Point.some x y hP : (Centered c).Point) := by
      rw [Affine.Point.some.injEq]
      exact ⟨hx', hy'⟩
    rw [he]
    apply add_nsmul_eq_zero_of_dvd hd
    exact (three_nsmul_affine_some_iff h₂' h₃' hΔ hP).mpr
      ⟨hy₀, by rw [hx, zero_mul]⟩
  by_cases hy : y = 0
  · have hxA : x ^ 3 = algebraMap E K (-A) := by
      rw [map_neg]
      exact eq_neg_iff_add_eq_zero.mpr (by simpa [hy, c] using hXY.symm)
    have hd : 2 ∣ q + 1 := by omega
    have hx' : x ^ Q = x :=
      root_frobenius_sq_fixed E K (by omega : 3 ∣ q + 1) (neg_ne_zero.mpr hA) hxA
    have hy' : y ^ Q = y := by rw [hy, zero_pow hQ]
    have he : Affine.Point.some (x ^ Q) (y ^ Q) hP' =
        (Affine.Point.some x y hP : (Centered c).Point) := by
      rw [Affine.Point.some.injEq]
      exact ⟨hx', hy'⟩
    rw [he]
    exact add_nsmul_eq_zero_of_dvd hd _ ((two_nsmul_affine_some_iff h₂' hP).mpr hy)
  exact frobenius_product_relation E K hA hq3 hq2 hΔ hx hy hP hP'

/-- The genuine q-power endomorphism on geometric points squares to multiplication by −q. -/
theorem frobenius_sq_eq_neg_card {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1) (P : ((Curve A).baseChange K).Point) :
    let F := Affine.Point.map (W' := Curve A) (FiniteField.frobeniusAlgHom E K)
    F (F P) = -(q • P) := by
  let g := FiniteField.frobeniusAlgHom E K
  let W := Curve A
  let F := Affine.Point.map (W' := W) g
  change F (F P) = -(q • P)
  let Relation (V : Affine K) : Prop := ∀ (x y : K)
    (h : V.Nonsingular x y) (h' : V.Nonsingular (x ^ Q) (y ^ Q)),
      q • (Affine.Point.some x y h : V.Point) + Affine.Point.some (x ^ Q) (y ^ Q) h' = 0
  have hW : W.baseChange K = Centered (algebraMap E K A) :=
    CubicNonsplitFrobeniusTrace.centered_baseChange E K A
  have hCentered : Relation (Centered (algebraMap E K A)) :=
    fun _ _ => some_frobenius_relation E K h₂ h₃ hA hq3 hq2
  have hRel : Relation (W.baseChange K) := Eq.mpr (congrArg Relation hW) hCentered
  cases P with
  | zero => simp
  | some x y h =>
    have h₁ := (W.baseChange_nonsingular (f := g) g.injective x y).mpr h
    have h₂ := (W.baseChange_nonsingular (f := g) g.injective (g x) (g y)).mpr h₁
    have h' : (W.baseChange K).Nonsingular (x ^ Q) (y ^ Q) := by
      change (W.baseChange K).Nonsingular ((x ^ q) ^ q) ((y ^ q) ^ q) at h₂
      simpa only [← pow_mul] using h₂
    have he : F (F (Affine.Point.some x y h)) = Affine.Point.some (x ^ Q) (y ^ Q) h' := by
      dsimp only [F]
      rw [Affine.Point.map_some, Affine.Point.map_some, Affine.Point.some.injEq]
      change ((x ^ q) ^ q = x ^ Q) ∧ ((y ^ q) ^ q = y ^ Q)
      exact ⟨(pow_mul x q q).symm, (pow_mul y q q).symm⟩
    rw [he]
    apply eq_neg_iff_add_eq_zero.mpr
    exact (add_comm _ _).trans (hRel x y h h')

end
end ManuscriptAudit.CubicHermitianFrobeniusSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicHermitianFrobeniusSquare.some_frobenius_relation,
      ``ManuscriptAudit.CubicHermitianFrobeniusSquare.frobenius_sq_eq_neg_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
