import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusCharacteristicAllPoints
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitPrimeNoPadicScalar
import PrimalitySheafVerification.ManuscriptAudit.RankTwoCoefficientIdentification
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitTateFixedValuation

/-! The full characteristic polynomial of native arithmetic 2-adic and 3-adic Frobenius
for every good split prime-field centered cubic. -/

namespace ManuscriptAudit.CubicSplitPrimeTateCoefficients

open Polynomial Module FiniteFieldPointCount CubicNonsplitThreeAdicTrace
open PowerTorsionTower PowerTateModule PowerTateRankTwo Paper5NonsplitFrobeniusModFour
open CubicFrobeniusTranscendentalRelation
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [DecidableEq L]

/-- The full Tate module of the actual centered cubic has its native rank-two basis. -/
def basis (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    Module.Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := by
  let G := GeometricPoints (ZMod p) L A
  obtain ⟨h₂K, h₃K⟩ := small_char p (ZMod p) hp
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂K
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃K
  have hAL : algebraMap (ZMod p) L A ≠ 0 := (map_ne_zero (algebraMap (ZMod p) L)).mpr hA
  by_cases h : l = 2
  · subst l
    let B := CubicTwoPowerTorsionBasis.affineBasis h₂ h₃ hAL 1
    let hs := CubicDoublingSurjective.affine_doubling_surjective h₂ h₃ hAL
    exact (Basis.finTwoProd ℤ_[2]).map (padicPairEquiv 2 G B hs)
  · have he : l = 3 := hl.resolve_left h
    subst l
    have hLevel : Nat.card (PowerTorsion 3 G 1) = 9 :=
      CubicThreeAdicTate.affine_threePower_card h₂ h₃ hAL 1
    let B := FirstPrimeTorsionBasis.basis 3 G (by
      change Nat.card (PowerTorsion 3 G 1) = 9
      exact hLevel)
    let hs := CubicTriplingSurjective.affine_tripling_surjective h₂ h₃ hAL
    exact (Basis.finTwoProd ℤ_[3]).map (padicPairEquiv 3 G B hs)

/-- Arithmetic Frobenius on the full native Tate module, with its actual transition maps. -/
def native (A : ZMod p) (l : ℕ) [Fact l.Prime] :
    Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) :=
  endMap l (arithmeticPointFrobenius (ZMod p) L A)

theorem arithmeticTrace_eq (A : ZMod p) :
    arithmeticTrace (ZMod p) A =
      (p : ℤ) + 1 - Nat.card (shortCubic (0 : ZMod p) A).toProjective.Point := by
  simp only [arithmeticTrace, ZMod.card]

/-- Transport the exact arithmetic characteristic relation through the actual Tate endomorphism. -/
theorem native_relation (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] :
    native p L A l ^ 2 -
      (arithmeticTrace (ZMod p) A : ℤ_[l]) • native p L A l +
      (p : ℤ_[l]) • (1 : Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))) = 0 := by
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ringChar.eq (ZMod p) p]; omega
  have h := CubicFrobeniusCharacteristicAllPoints.characteristic_relation (ZMod p) L h₂ h₃ hchar hA
  have he := congrArg (endMap l) h
  simp only [characteristicError, map_pow, map_sub, map_add, map_zsmul, map_one, map_zero] at he
  rw [ZMod.card] at he
  let S := Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))
  let F : S := native p L A l
  let t := arithmeticTrace (ZMod p) A
  change F ^ 2 - t • F + (p : ℤ) • (1 : S) = 0 at he
  have ht : (t : S) = (t : ℤ_[l]) • (1 : S) := by
    rw [← Algebra.algebraMap_eq_smul_one, map_intCast]
  have hq : (p : S) = (p : ℤ_[l]) • (1 : S) := by
    rw [← Algebra.algebraMap_eq_smul_one, map_natCast]
  change F ^ 2 - (t : ℤ_[l]) • F + (p : ℤ_[l]) • (1 : S) = 0
  calc
    _ = F ^ 2 - (t : S) * F + (p : S) := by
      rw [ht, hq, smul_mul_assoc, one_mul]
    _ = 0 := by simpa only [zsmul_eq_mul, mul_one, Int.cast_natCast] using he

/-- Exact signed arithmetic trace and determinant p, on the native 2-adic or 3-adic Tate module. -/
theorem trace_det (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] _ (native p L A l) = (arithmeticTrace (ZMod p) A : ℤ_[l]) ∧
      LinearMap.det (native p L A l) = (p : ℤ_[l]) := by
  apply RankTwoCoefficientIdentification.linear_trace_det (basis p L hp hA l hl)
  · intro r
    rw [arithmeticTrace_eq]
    exact CubicSplitPrimeNoPadicScalar.no_scalar_root p hp hs hA l hl r
  · exact native_relation p L hp hA l

/-- Exact full characteristic polynomial on the native geometric Tate module. -/
theorem charpoly (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let B := basis p L hp hA l hl
    letI : Module.Free ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := Module.Free.of_basis B
    letI : Module.Finite ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := Module.Finite.of_basis B
    (native p L A l).charpoly =
      X ^ 2 - C (arithmeticTrace (ZMod p) A : ℤ_[l]) * X + C (p : ℤ_[l]) := by
  apply RankTwoCoefficientIdentification.linear_charpoly (basis p L hp hA l hl)
  · intro r
    rw [arithmeticTrace_eq]
    exact CubicSplitPrimeNoPadicScalar.no_scalar_root p hp hs hA l hl r
  · exact native_relation p L hp hA l

end

end ManuscriptAudit.CubicSplitPrimeTateCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicSplitPrimeTateCoefficients.basis,
      ``ManuscriptAudit.CubicSplitPrimeTateCoefficients.native_relation,
      ``ManuscriptAudit.CubicSplitPrimeTateCoefficients.trace_det,
      ``ManuscriptAudit.CubicSplitPrimeTateCoefficients.charpoly] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
