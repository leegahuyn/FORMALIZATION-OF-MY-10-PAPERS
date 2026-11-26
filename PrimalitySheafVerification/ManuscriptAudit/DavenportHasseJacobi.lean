import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.JacobiSum.Basic
import PrimalitySheafVerification.ManuscriptAudit.DavenportHasseLift

/-! Norm lifting for complex Jacobi sums of finite fields. -/

namespace ManuscriptAudit.DavenportHasseJacobi

open LanglandsFirstMainLemma

noncomputable section

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

private theorem normMulChar_mul (χ φ : MulChar F ℂ) :
    normMulChar F E (χ * φ) = normMulChar F E χ * normMulChar F E φ := by
  apply MulChar.ext
  intro u
  simp only [normMulChar_apply, MulChar.mul_apply]

/-- The field norm induces a multiplicative map on characters. -/
def normCharacter : MulChar F ℂ →* MulChar E ℂ where
  toFun := normMulChar F E
  map_one' := by
    apply MulChar.ext
    intro u
    have hu : IsUnit (Algebra.norm F (u : E)) := u.isUnit.map (Algebra.norm F)
    simp [normMulChar_apply, MulChar.one_apply hu]
  map_mul' := normMulChar_mul

theorem normCharacter_injective : Function.Injective (normCharacter (F := F) (E := E)) := by
  intro χ φ h
  apply MulChar.ext
  intro a
  obtain ⟨b, hb⟩ := FiniteField.unitsMap_norm_surjective F E a
  have hbval : Algebra.norm F (b : E) = (a : F) := congrArg Units.val hb
  have he := DFunLike.congr_fun h (b : E)
  change χ (Algebra.norm F (b : E)) = φ (Algebra.norm F (b : E)) at he
  simpa only [hbval] using he

/-- Negative Jacobi sums satisfy a power law under the actual norm pullback. -/
theorem negative_jacobi_lift (χ φ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (hχφ : χ * φ ≠ 1) :
    -jacobiSum (normMulChar F E χ) (normMulChar F E φ) =
      (-jacobiSum χ φ) ^ Module.finrank F E := by
  let ψE := traceAddChar F E ψ
  have hψE : ψE ≠ 1 := (traceAddChar_ne_one_iff F E ψ).mpr hψ
  have hχφE : normMulChar F E χ * normMulChar F E φ ≠ 1 := by
    rw [← normMulChar_mul]
    exact (normMulChar_ne_one_iff F E (χ * φ)).mpr hχφ
  have hbase :
      (-gaussSum (χ * φ) ψ) * (-jacobiSum χ φ) = (-gaussSum χ ψ) * (-gaussSum φ ψ) := by
    simpa only [neg_mul_neg] using jacobiSum_mul_nontrivial hχφ ψ
  have hext :
      (-gaussSum (normMulChar F E (χ * φ)) ψE) *
        (-jacobiSum (normMulChar F E χ) (normMulChar F E φ)) =
          (-gaussSum (normMulChar F E χ) ψE) * (-gaussSum (normMulChar F E φ) ψE) := by
    rw [normMulChar_mul]
    simpa only [neg_mul_neg] using jacobiSum_mul_nontrivial hχφE ψE
  have hn : -gaussSum (normMulChar F E (χ * φ)) ψE ≠ 0 :=
    neg_ne_zero.mpr (LanglandsFirstMainLemma.gaussSum_ne_zero hψE)
  apply mul_left_cancel₀ hn
  calc
    _ = _ := hext
    _ = ((-gaussSum χ ψ) * (-gaussSum φ ψ)) ^ Module.finrank F E := by
      dsimp only [ψE]
      rw [DavenportHasseLift.ordinary_gauss_lift χ ψ hψ,
        DavenportHasseLift.ordinary_gauss_lift φ ψ hψ, ← mul_pow]
    _ = _ := by
      rw [← hbase, mul_pow]
      exact congrArg (fun z : ℂ => z * (-jacobiSum χ φ) ^ Module.finrank F E)
        (DavenportHasseLift.ordinary_gauss_lift (K := E) (χ * φ) ψ hψ).symm

/-- On a base-field scalar the lifted character is the corresponding power. -/
theorem norm_character_algebraMap (χ : MulChar F ℂ) (a : F) :
    normMulChar F E χ (algebraMap F E a) = (χ a) ^ Module.finrank F E := by
  rw [normMulChar_apply, Algebra.norm_algebraMap, map_pow]

end

/-- The complex exponential gives a nontrivial additive character on each prime field. -/
theorem primeField_additiveCharacter {p : ℕ} [Fact p.Prime] :
    ∃ ψ : AddChar (ZMod p) ℂ, ψ ≠ 1 := by
  refine ⟨ZMod.stdAddChar, ?_⟩
  intro h
  have he := DFunLike.congr_fun h (1 : ZMod p)
  have h0 := (ZMod.stdAddChar : AddChar (ZMod p) ℂ).map_zero_eq_one
  have h1 : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 1 = 1 := by simpa using he
  exact one_ne_zero (ZMod.injective_stdAddChar (h1.trans h0.symm))

end ManuscriptAudit.DavenportHasseJacobi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.DavenportHasseJacobi.normCharacter_injective,
      ``ManuscriptAudit.DavenportHasseJacobi.negative_jacobi_lift,
      ``ManuscriptAudit.DavenportHasseJacobi.norm_character_algebraMap,
      ``ManuscriptAudit.DavenportHasseJacobi.primeField_additiveCharacter] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
