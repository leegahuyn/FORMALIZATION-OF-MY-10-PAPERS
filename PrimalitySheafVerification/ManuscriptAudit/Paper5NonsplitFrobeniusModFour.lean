import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantFromFixed
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitExtensionRecurrence
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusTorsionFixed

/-! The actual supersingular Frobenius characteristic polynomial modulo four. -/

namespace ManuscriptAudit.Paper5NonsplitFrobeniusModFour

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion
open CubicThreeTorsionOrdinate CubicTwoPowerTorsion TorsionFrobeniusModule TwoPowerTorsionTower
open Paper5NonsplitExtensionRecurrence Paper5PrintedRecurrence WeierstrassFrobeniusTorsionFixed
open FourTorsionDeterminantFromFixed
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve paper5_traceCurve_trace_eq_zero)

noncomputable section

variable (p : ℕ) [Fact p.Prime]

theorem small_char (K : Type*) [Field K] [CharP K p] (hp : 5 ≤ p) :
    (2 : K) ≠ 0 ∧ (3 : K) ≠ 0 := by
  have hsmall (n : ℕ) (h₀ : 0 < n) (hn : n < p) : (n : K) ≠ 0 :=
    (CharP.cast_eq_zero_iff K p n).not.mpr
      (fun h => (Nat.not_le_of_lt hn) (Nat.le_of_dvd h₀ h))
  exact ⟨by simpa only [Nat.cast_ofNat] using hsmall 2 (by decide) (by omega),
    by simpa only [Nat.cast_ofNat] using hsmall 3 (by decide) (by omega)⟩

theorem printed_eq_centered (A : ZMod p) :
    paper5TraceCurve p A = shortCubic (0 : ZMod p) A := by
  simp [paper5TraceCurve, shortCubic, ZMod.natCast_self]

/-- The actual quadratic extension has exactly (p+1)^2 nonsingular affine-model group points. -/
theorem quadratic_count (hp : 5 ≤ p) (hr : p % 3 = 2)
    {A : ZMod p} (hA : A ≠ 0) {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] (hd : Module.finrank (ZMod p) E = 2) :
    Nat.card ((Curve A).baseChange E).Point = (p + 1) ^ 2 := by
  have h := actual_extension_trace_eq_recurrence_of_mod_two (E := E) hp hr hA
  have hCard : Fintype.card E = p ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hd]
  have hRec : recurrence p 0 2 = -2 * (p : ℤ) := by
    simpa using zero_recurrence_at_even p 1
  rw [paper5_traceCurve_trace_eq_zero hp hr hA, hd, hRec, hCard] at h
  push_cast at h
  have he : (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ) =
      ((p : ℤ) + 1) ^ 2 := by nlinarith
  have hc : Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point = (p + 1) ^ 2 := by
    exact_mod_cast he
  rw [printed_eq_centered p A] at hc
  exact (Nat.card_congr (Projective.Point.toAffineAddEquiv
    (W := ((shortCubic (0 : ZMod p) A).baseChange E).toProjective)).symm.toEquiv).trans hc

variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

private theorem geometric_curve_eq (A : ZMod p) :
    (Curve A).baseChange L = Curve (algebraMap (ZMod p) L A) := by
  simp [Curve, CubicAffine, shortCubic, WeierstrassCurve.baseChange, WeierstrassCurve.map]

abbrev GeometricTorsion (m : ℕ) (A : ZMod p) := Torsion m ((Curve A).baseChange L).Point

theorem geo_card_twoPower (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (n : ℕ) :
    Nat.card (GeometricTorsion p L (2 ^ n) A) = 4 ^ n := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  obtain ⟨h₂, h₃⟩ := small_char p L hp
  have hAL : algebraMap (ZMod p) L A ≠ 0 := (map_ne_zero (algebraMap (ZMod p) L)).mpr hA
  change Nat.card (Torsion (2 ^ n) ((Curve A).baseChange L).Point) = _
  rw [geometric_curve_eq p L A]
  exact (Nat.card_congr (carrierEquiv (2 ^ n) _)).trans (affine_twoPower_card h₂ h₃ hAL n)

def fourBasis (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    Module.Basis (Fin 2) (ZMod 4) (GeometricTorsion p L 4 A) := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  obtain ⟨h₂, h₃⟩ := small_char p L hp
  have hAL : algebraMap (ZMod p) L A ≠ 0 := (map_ne_zero (algebraMap (ZMod p) L)).mpr hA
  change Module.Basis (Fin 2) (ZMod (2 ^ 2)) (PowerTorsion ((Curve A).baseChange L).Point 2)
  rw [geometric_curve_eq p L A]
  exact CubicTwoPowerTorsionBasis.affineBasis h₂ h₃ hAL 2

theorem trace_zero_mod_four (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    LinearMap.trace (ZMod 4) (GeometricTorsion p L 4 A) (frobeniusLinear 4 p L (Curve A)) = 0 := by
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have hq : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hr
  exact CubicNonsplitFrobeniusTrace.actual_trace_zero (ZMod p) L h₂ h₃ hA hq 2

/-- The determinant of actual prime-field Frobenius on geometric E[4] is p modulo four. -/
theorem determinant_eq_prime (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    LinearMap.det (frobeniusLinear 4 p L (Curve A)) = (p : ZMod 4) := by
  classical
  let E := GaloisField p 2
  letI : Fintype E := Fintype.ofFinite E
  let W := Curve A
  have hd : Module.finrank (ZMod p) E = 2 := GaloisField.finrank p (n := 2) (by decide)
  letI : Algebra.IsAlgebraic (ZMod p) E := ⟨fun x => ⟨
    (X ^ Fintype.card E - X : (ZMod p)[X]),
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card,
    by simp [FiniteField.pow_card]⟩⟩
  let i : E →ₐ[ZMod p] L := IsAlgClosed.lift
  let H := (W.baseChange E).Point
  letI : Finite (WithZero {xy : E × E // (W.baseChange E).Nonsingular xy.1 xy.2}) := by
    change Finite (Option {xy : E × E // (W.baseChange E).Nonsingular xy.1 xy.2})
    infer_instance
  letI : Finite H := Finite.of_injective _ (Affine.nonsingularPointEquiv (W.baseChange E)).injective
  let V := GeometricTorsion p L 4 A
  have hV : Nat.card V = 16 := geo_card_twoPower p L hp hA 2
  letI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; decide)
  let F : V ≃ₗ[ZMod 4] V := frobeniusLinearEquiv 4 p L W
  have hG₂ : Nat.card (GeometricTorsion p L 2 A) = 4 := geo_card_twoPower p L hp hA 1
  letI : Finite (GeometricTorsion p L 2 A) := Nat.finite_of_card_ne_zero (by rw [hG₂]; decide)
  have hKer : Nat.card (Torsion 2 H) ≤ 4 := by
    rw [← hG₂]
    exact Nat.card_le_card_of_injective _ (pointMap_injective 2 W i)
  let j : Torsion 4 H →+ V := (pointMap 4 W i).toAddMonoidHom
  have hj : Function.Injective j := pointMap_injective 4 W i
  have hFix (v : V) : F (F v) = v ↔ ∃ P : Torsion 4 H, j P = v := by
    have he := fixed_iff_rational 4 p L E i W v
    rw [hd, pow_two] at he
    exact he
  have hOdd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  exact determinant_eq_of_fixed_card p hOdd (fourBasis p L hp hA) F
    (trace_zero_mod_four p L hp hr hA) hV (quadratic_count p hp hr hA hd) hKer j hj hFix

/-- In the nonsplit family the actual characteristic polynomial modulo four is T²+p. -/
theorem charpoly_mod_four (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    letI := Module.Free.of_basis (fourBasis p L hp hA)
    letI := Module.Finite.of_basis (fourBasis p L hp hA)
    (frobeniusLinear 4 p L (Curve A)).charpoly = X ^ 2 + C (p : ZMod 4) := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  let B := fourBasis p L hp hA
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let F := frobeniusLinear 4 p L (Curve A)
  change F.charpoly = _
  rw [← LinearMap.charpoly_toMatrix F B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod 4) B, LinearMap.det_toMatrix B,
    trace_zero_mod_four p L hp hr hA, determinant_eq_prime p L hp hr hA,
    map_zero, zero_mul, sub_zero]

end
end ManuscriptAudit.Paper5NonsplitFrobeniusModFour

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5NonsplitFrobeniusModFour.quadratic_count,
      ``ManuscriptAudit.Paper5NonsplitFrobeniusModFour.trace_zero_mod_four,
      ``ManuscriptAudit.Paper5NonsplitFrobeniusModFour.determinant_eq_prime,
      ``ManuscriptAudit.Paper5NonsplitFrobeniusModFour.charpoly_mod_four] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
