import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericFrobeniusHeight
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusCoordinateEvaluation
import PrimalitySheafVerification.ManuscriptAudit.RationalIdentityHeight

/-! The actual anti-invariant point heights of the two Frobenius secants. -/

namespace ManuscriptAudit.CubicGenericSecantHeight

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace
open CubicGenericFunctionField CubicGenericAntiInvariant CubicGenericAbscissaPair CubicGenericPointHeight
open CubicGenericFrobeniusHeight CubicFrobeniusSecantPoints CubicFrobeniusCoordinateEvaluation
open CubicFrobeniusDifferenceDegree RationalSubstitutionDegree RationalIdentityHeight

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [Fintype K] (A : K)

/-- The generic point regarded as an element of the anti-invariant subgroup. -/
def genericAntiPoint (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    antiInvariant A :=
  ⟨genericPoint A h₂ h₃ hA, genericPoint_mem_antiInvariant A h₂ h₃ hA⟩

theorem genericAntiPoint_xRep (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    (genericAntiPoint A h₂ h₃ hA).val.xRep = ![genericX A, 1] := rfl

theorem height_eq_of_xRep (P : antiInvariant A) (r : RatFunc K)
    (hRep : P.val.xRep = ![algebraMap (RatFunc K) (Model A) r, 1]) :
    height A P = rationalDegree r := by
  obtain ⟨P, hP⟩ := P
  cases P with
  | zero =>
    have he := congrFun hRep 1
    change (0 : Model A) = 1 at he
    exact (zero_ne_one he).elim
  | some x y hp =>
    have he := congrFun hRep 0
    change x = algebraMap (RatFunc K) (Model A) r at he
    have hx : x.re = r := congrArg QuadraticAlgebra.re he
    change rationalDegree x.re = rationalDegree r
    rw [hx]

/-- The two native Frobenius secants evaluate by rational substitution at every nonconstant point. -/
theorem generic_secant_xRep {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (P : antiInvariant A) (r : RatFunc K) (hr : ¬ ∃ c : K, r = RatFunc.C c)
    (hRep : P.val.xRep = ![algebraMap (RatFunc K) (Model A) r, 1]) :
    let F := frobenius A
    let e := algebraMap (RatFunc K) (Model A)
    (F P + P).val.xRep = ![e (substitute r hr (sumCoordinate k A)), 1] ∧
    (F P - P).val.xRep = ![e (substitute r hr (coordinate K k A)), 1] := by
  obtain ⟨P, hP⟩ := P
  cases P with
  | zero =>
    have he := congrFun hRep 1
    change (0 : Model A) = 1 at he
    exact (zero_ne_one he).elim
  | some x y hp =>
    let e := algebraMap (RatFunc K) (Model A)
    have he := congrFun hRep 0
    change x = e r at he
    subst x
    have h₂' : (2 : Model A) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K (Model A))).mpr h₂
    have h₃' : (3 : Model A) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K (Model A))).mpr h₃
    have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂' h₃'
      ((map_ne_zero (algebraMap K (Model A))).mpr hA)
    have hy := (nonsingular_iff hΔ (e r) y).mp hp
    have hx : (e r) ^ Fintype.card K ≠ e r := by
      intro heq
      apply power_ne_of_nonconstant r hr
      apply e.injective
      rwa [map_pow]
    obtain ⟨hPlus, hMinus⟩ := secant_xRep K (Model A) hq A (e r) y hp hy hx
    obtain ⟨hEvalPlus, hEvalMinus⟩ := evaluations (Model A) r hr k A
    rw [hEvalPlus] at hPlus
    rw [hEvalMinus] at hMinus
    exact ⟨hPlus, hMinus⟩

/-- At the generic point, F(P)−P has degree the actual projective point count. -/
theorem generic_difference_height {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hchar : ringChar K ≠ 2) (hA : A ≠ 0) :
    let P := genericAntiPoint A h₂ h₃ hA
    height A (frobenius A P - P) = Nat.card (FiniteFieldPointCount.shortCubic (0 : K) A).toProjective.Point := by
  let P := genericAntiPoint A h₂ h₃ hA
  obtain ⟨_, hRep⟩ := generic_secant_xRep A hq h₂ h₃ hA P RatFunc.X
    (X_nonconstant (K := K)) (genericAntiPoint_xRep A h₂ h₃ hA)
  rw [substitute_identity] at hRep
  calc
    height A (frobenius A P - P) = rationalDegree (coordinate K k A) :=
      height_eq_of_xRep A _ _ hRep
    _ = Module.finrank (IntermediateField.adjoin K {coordinate K k A}) (RatFunc K) :=
      (RatFunc.finrank_eq_max_natDegree (coordinate K k A)).symm
    _ = _ := finrank_adjoin_coordinate K hq hk h₂ h₃ hchar hA

/-- At the generic point, F(P)+P has the actual sum secant rational degree. -/
theorem generic_sum_xRep {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    let P := genericAntiPoint A h₂ h₃ hA
    (frobenius A P + P).val.xRep =
      ![algebraMap (RatFunc K) (Model A) (sumCoordinate k A), 1] := by
  let P := genericAntiPoint A h₂ h₃ hA
  obtain ⟨hRep, _⟩ := generic_secant_xRep A hq h₂ h₃ hA P RatFunc.X
    (X_nonconstant (K := K)) (genericAntiPoint_xRep A h₂ h₃ hA)
  rwa [substitute_identity] at hRep

end

end ManuscriptAudit.CubicGenericSecantHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericSecantHeight.genericAntiPoint_xRep,
      ``ManuscriptAudit.CubicGenericSecantHeight.height_eq_of_xRep,
      ``ManuscriptAudit.CubicGenericSecantHeight.generic_secant_xRep,
      ``ManuscriptAudit.CubicGenericSecantHeight.generic_difference_height,
      ``ManuscriptAudit.CubicGenericSecantHeight.generic_sum_xRep] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
