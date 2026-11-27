import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EightTorsionDeterminantFromFixed
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitQuarticCount
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitTwoAdicModFour

/-! Actual prime-field Frobenius has determinant p modulo eight in the nonsplit centered family. -/

namespace ManuscriptAudit.Paper5NonsplitModEight

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open TorsionFrobeniusModule TwoPowerTorsionTower WeierstrassFrobeniusTorsionFixed
open Paper5NonsplitFrobeniusModFour Paper5NonsplitQuarticCount Paper5NonsplitTwoAdicModFour
open Paper5TwoAdicCoefficients FourTorsionDeterminantTools EightTorsionDeterminantFromFixed

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

private def extensionEmbedding (n : ℕ) : GaloisField p n →ₐ[ZMod p] L := by
  classical
  let E := GaloisField p n
  letI : Fintype E := Fintype.ofFinite E
  letI : Algebra.IsAlgebraic (ZMod p) E := ⟨fun x => ⟨
    (X ^ Fintype.card E - X : (ZMod p)[X]),
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card,
    by simp [FiniteField.pow_card]⟩⟩
  exact IsAlgClosed.lift

private theorem finite_points (E : Type*) [Field E] [Finite E] [Algebra (ZMod p) E]
    (W : Affine (ZMod p)) : Finite (W.baseChange E).Point := by
  classical
  letI : Finite (WithZero {xy : E × E // (W.baseChange E).Nonsingular xy.1 xy.2}) := by
    change Finite (Option {xy : E × E // (W.baseChange E).Nonsingular xy.1 xy.2})
    infer_instance
  exact Finite.of_injective _ (Affine.nonsingularPointEquiv (W.baseChange E)).injective

private def centeredLevelBasis (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (n : ℕ) :
    Module.Basis (Fin 2) (ZMod (2 ^ n)) (GeometricTorsion p L (2 ^ n) A) := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  obtain ⟨h₂, h₃⟩ := small_char p L hp
  have hAL : algebraMap (ZMod p) L A ≠ 0 := (map_ne_zero (algebraMap (ZMod p) L)).mpr hA
  change Module.Basis (Fin 2) (ZMod (2 ^ n)) (PowerTorsion ((Curve A).baseChange L).Point n)
  rw [CubicNonsplitFrobeniusTrace.centered_baseChange]
  exact CubicTwoPowerTorsionBasis.affineBasis h₂ h₃ hAL n

private theorem trace_zero_at_level (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (n : ℕ) :
    LinearMap.trace (ZMod (2 ^ n)) (GeometricTorsion p L (2 ^ n) A)
      (frobeniusLinear (2 ^ n) p L (Curve A)) = 0 := by
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have hq : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hr
  exact CubicNonsplitFrobeniusTrace.actual_trace_zero (ZMod p) L h₂ h₃ hA hq n

private theorem rational_torsion_card_le (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (n : ℕ)
    {E : Type*} [Field E] [Algebra (ZMod p) E] [DecidableEq E] (i : E →ₐ[ZMod p] L) :
    Nat.card (Torsion (2 ^ n) ((Curve A).baseChange E).Point) ≤ 4 ^ n := by
  have hG := geo_card_twoPower p L hp hA n
  letI : Finite (GeometricTorsion p L (2 ^ n) A) := Nat.finite_of_card_ne_zero
    (by rw [hG]; exact pow_ne_zero _ (by decide : (4 : ℕ) ≠ 0))
  rw [← hG]
  exact Nat.card_le_card_of_injective _ (pointMap_injective (2 ^ n) (Curve A) i)

private theorem quadratic_det (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (hp₄ : p % 4 = 3)
    (hd₄ : reduceEightFour (LinearMap.det (frobeniusLinear 8 p L (Curve A))) = 3) :
    LinearMap.det (frobeniusLinear 8 p L (Curve A)) = (p : ZMod 8) := by
  classical
  letI : Fact (1 < (8 : ℕ)) := ⟨by decide⟩
  let E := GaloisField p 2
  letI : Fintype E := Fintype.ofFinite E
  let W := Curve A
  let i := extensionEmbedding p L 2
  let H := (W.baseChange E).Point
  letI : Finite H := finite_points p E W
  let V := GeometricTorsion p L 8 A
  let F := frobeniusLinear 8 p L W
  let j : Torsion 8 H →+ V := (pointMap 8 W i).toAddMonoidHom
  have hj : Function.Injective j := pointMap_injective 8 W i
  have hd : Module.finrank (ZMod p) E = 2 := GaloisField.finrank p (n := 2) (by decide)
  have hFix (v : V) : F (F v) = v ↔ ∃ P : Torsion 8 H, j P = v := by
    have hh := fixed_iff_rational 8 p L E i W v
    rw [hd, pow_two] at hh
    exact hh
  have hV : Nat.card V = 64 := geo_card_twoPower p L hp hA 3
  have hKer : Nat.card (Torsion 4 H) ≤ 16 := rational_torsion_card_le p L hp hA 2 i
  have hScalar (v : V) : F (F v) = (-LinearMap.det F) • v :=
    square_apply_of_trace_zero (centeredLevelBasis p L hp hA 3) F
      (trace_zero_at_level p L hp hr hA 3) v
  exact residue_of_quadratic_fixed p hp₄ (LinearMap.det F) hd₄ (quadratic_count p hp hr hA hd)
    hV hKer j hj (fun v => F (F v)) hFix hScalar

private theorem quartic_det (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (hp₄ : p % 4 = 1)
    (hd₄ : reduceEightFour (LinearMap.det (frobeniusLinear 8 p L (Curve A))) = 1)
    (hReduction : reduceSixteenEight (LinearMap.det (frobeniusLinear 16 p L (Curve A))) =
      LinearMap.det (frobeniusLinear 8 p L (Curve A))) :
    LinearMap.det (frobeniusLinear 8 p L (Curve A)) = (p : ZMod 8) := by
  classical
  letI : Fact (1 < (16 : ℕ)) := ⟨by decide⟩
  let E := GaloisField p 4
  letI : Fintype E := Fintype.ofFinite E
  let W := Curve A
  let i := extensionEmbedding p L 4
  let H := (W.baseChange E).Point
  letI : Finite H := finite_points p E W
  let V := GeometricTorsion p L 16 A
  let F := frobeniusLinear 16 p L W
  let j : Torsion 16 H →+ V := (pointMap 16 W i).toAddMonoidHom
  have hj : Function.Injective j := pointMap_injective 16 W i
  have hd : Module.finrank (ZMod p) E = 4 := GaloisField.finrank p (n := 4) (by decide)
  have hFix (v : V) : (F ^ 4) v = v ↔ ∃ P : Torsion 16 H, j P = v := by
    have hh := fixed_iff_rational 16 p L E i W v
    rw [hd] at hh
    exact hh
  have hV : Nat.card V = 256 := geo_card_twoPower p L hp hA 4
  have hKer : Nat.card (Torsion 8 H) ≤ 64 := rational_torsion_card_le p L hp hA 3 i
  have hSq (v : V) : F (F v) = (-LinearMap.det F) • v :=
    square_apply_of_trace_zero (centeredLevelBasis p L hp hA 4) F
      (trace_zero_at_level p L hp hr hA 4) v
  have hScalar (v : V) : (F ^ 4) v = (LinearMap.det F) ^ 2 • v := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_two, pow_two]
    change F (F (F (F v))) = _
    rw [hSq (F (F v)), hSq v, smul_smul, neg_mul_neg] <;> simp only [pow_two]
  exact residue_of_quartic_fixed p hp₄ _ (LinearMap.det F) hd₄ hReduction
    (quartic_count p hp hr hA hd) hV hKer j hj (fun v : V => (F ^ 4) v) hFix hScalar

/-- The native Frobenius determinant modulo eight is the prime itself. -/
theorem determinant_eq_prime (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    LinearMap.det (frobeniusLinear 8 p L (Curve A)) = (p : ZMod 8) := by
  let d := determinant p L hp hA
  have hNative (n : ℕ) : PadicInt.toZModPow n d =
      LinearMap.det (frobeniusLinear (2 ^ n) p L (Curve A)) :=
    determinant_reduction_eq_native p L hp hA n
  have h₈ : PadicInt.toZModPow 3 d = LinearMap.det (frobeniusLinear 8 p L (Curve A)) :=
    hNative 3
  have h₁₆ : PadicInt.toZModPow 4 d = LinearMap.det (frobeniusLinear 16 p L (Curve A)) :=
    hNative 4
  have h₈₄ : reduceEightFour (LinearMap.det (frobeniusLinear 8 p L (Curve A))) = (p : ZMod 4) := by
    rw [← h₈]
    exact (RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow 2 3 (by decide)) d).trans
      (determinant_reduction_eq_prime p L hp hr hA)
  have h₁₆₈ : reduceSixteenEight (LinearMap.det (frobeniusLinear 16 p L (Curve A))) =
      LinearMap.det (frobeniusLinear 8 p L (Curve A)) := by
    rw [← h₁₆, ← h₈]
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow 3 4 (by decide)) d
  have hOdd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hOdd
  have hCases : p % 4 = 3 ∨ p % 4 = 1 := by omega
  rcases hCases with h | h
  · rw [← ZMod.natCast_mod p 4, h, Nat.cast_ofNat] at h₈₄
    exact quadratic_det p L hp hr hA h h₈₄
  · rw [← ZMod.natCast_mod p 4, h, Nat.cast_one] at h₈₄
    exact quartic_det p L hp hr hA h h₈₄ h₁₆₈

theorem adic_determinant_reduction (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    PadicInt.toZModPow 3 (determinant p L hp hA) = (p : ZMod 8) :=
  (determinant_reduction_eq_native p L hp hA 3).trans (determinant_eq_prime p L hp hr hA)

theorem charpoly_mod_eight (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    letI := Module.Free.of_basis (centeredLevelBasis p L hp hA 3)
    letI := Module.Finite.of_basis (centeredLevelBasis p L hp hA 3)
    (frobeniusLinear 8 p L (Curve A)).charpoly = X ^ 2 + C (p : ZMod 8) := by
  letI : Fact (1 < (8 : ℕ)) := ⟨by decide⟩
  let B := centeredLevelBasis p L hp hA 3
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let F := frobeniusLinear 8 p L (Curve A)
  have ht : LinearMap.trace (ZMod 8) (GeometricTorsion p L (2 ^ 3) A) F = 0 :=
    trace_zero_at_level p L hp hr hA 3
  have hd : LinearMap.det F = (p : ZMod 8) := determinant_eq_prime p L hp hr hA
  change F.charpoly = _
  rw [← LinearMap.charpoly_toMatrix F B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod 8) B, LinearMap.det_toMatrix B,
    ht, hd, map_zero, zero_mul, sub_zero]

end
end ManuscriptAudit.Paper5NonsplitModEight

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5NonsplitModEight.determinant_eq_prime,
      ``ManuscriptAudit.Paper5NonsplitModEight.adic_determinant_reduction,
      ``ManuscriptAudit.Paper5NonsplitModEight.charpoly_mod_eight] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
