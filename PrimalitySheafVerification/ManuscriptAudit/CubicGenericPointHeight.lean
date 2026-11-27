import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericAbscissaPair
import PrimalitySheafVerification.ManuscriptAudit.CubicKummerDegreeParallelogram
import PrimalitySheafVerification.ManuscriptAudit.CubicKummerPoints
import PrimalitySheafVerification.ManuscriptAudit.IntegerHeightQuadraticMap

/-! The quadratic height on the actual centered cubic's anti-invariant generic points. -/

namespace ManuscriptAudit.CubicGenericPointHeight

open Polynomial WeierstrassCurve CubicGenericFunctionField CubicGenericAntiInvariant
open CubicGenericAbscissaPair CubicKummerQuadratic CubicKummerSymmetricHeight
open CubicKummerDegreeParallelogram CubicKummerPoints

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] (A : K)

/-- The rational abscissa degree of an actual anti-invariant point. -/
def height (P : antiInvariant A) : ℕ := pairHeight (polynomialPair A P.val)

theorem height_zero : height A 0 = 0 := by
  simp [height, polynomialPair, pairHeight]

private theorem evaluated_symmetric (h₂ : (2 : K) ≠ 0) (P Q : antiInvariant A) :
    ∃ c : Model A, c ≠ 0 ∧ ∀ i,
      coeffMap A (symmetric (polynomialPair A P.val) (polynomialPair A Q.val) i) =
        c * (P.val.sym2x Q.val i) := by
  obtain ⟨p, hp, hP⟩ := polynomialPair_xRep A h₂ P.property
  obtain ⟨q, hq, hQ⟩ := polynomialPair_xRep A h₂ Q.property
  refine ⟨p * q, mul_ne_zero hp hq, ?_⟩
  have hL := map_symmetric (coeffMap A) (polynomialPair A P.val) (polynomialPair A Q.val)
  have hP' : coeffMap A ∘ polynomialPair A P.val = fun i => p * P.val.xRep i := funext hP
  have hQ' : coeffMap A ∘ polynomialPair A Q.val = fun i => q * Q.val.xRep i := funext hQ
  rw [hP', hQ'] at hL
  intro i
  change (coeffMap A ∘ symmetric (polynomialPair A P.val)
    (polynomialPair A Q.val)) i = _
  rw [← hL]
  change symmetric (fun j => p * P.val.xRep j) (fun j => q * Q.val.xRep j) i =
    p * q * symmetric P.val.xRep Q.val.xRep i
  fin_cases i <;> simp [symmetric] <;> ring

private theorem forms_scale {S : Type*} [CommRing S] (a t : S) (v : Fin 3 → S) :
    forms a (fun j => t * v j) = fun i => t ^ 2 * forms a v i := by
  funext i
  fin_cases i <;> simp [forms] <;> ring

/-- The actual group law gives the exact degree parallelogram, including infinity. -/
theorem height_parallelogram (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (P Q : antiInvariant A) :
    height A (P + Q) + height A (P - Q) = 2 * height A P + 2 * height A Q := by
  let a := polynomialPair A P.val
  let b := polynomialPair A Q.val
  let p := polynomialPair A (P + Q).val
  let m := polynomialPair A (P - Q).val
  obtain ⟨cIn, hcIn, hIn⟩ := evaluated_symmetric A h₂ P Q
  obtain ⟨cOut, hcOut, hOut⟩ := evaluated_symmetric A h₂ (P + Q) (P - Q)
  have h₂' : (2 : Model A) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (Model A))).mpr h₂
  have h₃' : (3 : Model A) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (Model A))).mpr h₃
  have hA' := (map_ne_zero (algebraMap K (Model A))).mpr hA
  obtain ⟨cK, hcK, hK⟩ := sym2x_add_sub h₂' h₃' hA' P.val Q.val
  have hMap := map_forms (coeffMap A) (C A) (symmetric a b)
  rw [coeffMap_C] at hMap
  have hIn' : coeffMap A ∘ symmetric a b = fun i => cIn * P.val.sym2x Q.val i := funext hIn
  rw [hIn', forms_scale, hK] at hMap
  let c := (cIn ^ 2 * cK) / cOut
  have hEq (i : Fin 3) : coeffMap A (forms (C A) (symmetric a b) i) =
      c * coeffMap A (symmetric p m i) := by
    change (coeffMap A ∘ forms (C A) (symmetric a b)) i = _
    rw [← hMap]
    change cIn ^ 2 * (cK * ((P.val + Q.val).sym2x (P.val - Q.val) i)) =
      c * coeffMap A (symmetric p m i)
    rw [show coeffMap A (symmetric p m i) = cOut *
      ((P.val + Q.val).sym2x (P.val - Q.val) i) from hOut i]
    dsimp only [c]
    rw [← mul_assoc ((cIn ^ 2 * cK) / cOut), div_mul_cancel₀ _ hcOut]
    ring
  exact degree_parallelogram h₂ h₃ hA
    (polynomialPair_rootFree A P.val) (polynomialPair_rootFree A Q.val)
    (polynomialPair_rootFree A (P + Q).val) (polynomialPair_rootFree A (P - Q).val)
    (div_ne_zero (mul_ne_zero (pow_ne_zero _ hcIn) hcK) hcOut) hEq

/-- The literal rational abscissa height is a native integer quadratic map. -/
def quadraticHeight (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    QuadraticMap ℤ (antiInvariant A) ℤ :=
  IntegerHeightQuadraticMap.ofParallelogram (fun P => (height A P : ℤ))
    (by exact_mod_cast height_zero A)
    (fun P Q => by exact_mod_cast height_parallelogram A h₂ h₃ hA P Q)

end

end ManuscriptAudit.CubicGenericPointHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericPointHeight.height_zero,
      ``ManuscriptAudit.CubicGenericPointHeight.height_parallelogram,
      ``ManuscriptAudit.CubicGenericPointHeight.quadraticHeight] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
