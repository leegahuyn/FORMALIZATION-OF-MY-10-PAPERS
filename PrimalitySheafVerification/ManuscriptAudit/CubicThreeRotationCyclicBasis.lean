import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.ThreePowerTorsionBasis

/-! The cube-root rotation admits cyclic bases at all genuine three-power levels. -/

namespace ManuscriptAudit.CubicThreeRotationCyclicBasis

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicCubeRotation
open CubicThreeTorsionBasis TorsionFrobeniusModule ThreePowerTorsionBasis
open Module

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] {A z : K}

variable (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
  (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (D : FlexPair A)

abbrev rotation (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (m : ℕ) : Module.End (ZMod m) (Torsion m (Curve A).Point) :=
  mapLinear m (rotate z hz (CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA))

include hz₁

private theorem cycleIndependent :
    LinearIndependent (ZMod 3) ![horizontal h₂ h₃ hA D, rotation h₂ h₃ hA hz 3 (horizontal h₂ h₃ hA D)] := by
  let U := horizontal h₂ h₃ hA D
  let S := rotation h₂ h₃ hA hz 3
  let x := fun P : T₃ A => abscissa (inclusion 3 _ P)
  have hxU : x U = D.x := abscissa_horizontal h₂ h₃ hA D
  have hxO : x 0 = 0 := by simp [x, abscissa]
  have hxNeg (P : T₃ A) : x (-P) = x P := by simp only [x, map_neg, abscissa_neg]
  have hxS : x (S U) = z * D.x := by
    change abscissa (rotate z hz
      (CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA) (U : (Curve A).Point)) = _
    rw [rotate_abscissa]
    exact congrArg (fun a : K => z * a) hxU
  have hz₀ : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hnez : z * D.x ≠ D.x := by
    intro h
    have hprod : (z - 1) * D.x = 0 := by rw [sub_mul, one_mul, h, sub_self]
    exact mul_ne_zero (sub_ne_zero.mpr hz₁) D.x_ne hprod
  have hU : U ≠ 0 := by
    intro h
    exact D.x_ne (hxU.symm.trans ((congrArg x h).trans hxO))
  have hSU : S U ≠ 0 := by
    intro h
    exact mul_ne_zero hz₀ D.x_ne (hxS.symm.trans ((congrArg x h).trans hxO))
  have hnot : x (S U) ≠ x U := by rw [hxS, hxU]; exact hnez
  change LinearIndependent (ZMod 3) ![U, S U]
  refine (linearIndependent_fin2 (K := ZMod 3)).mpr ⟨by simpa using hSU, ?_⟩
  intro c hc
  change c • S U = U at hc
  rcases scalar_cases c with rfl | rfl | rfl
  · exact hU (by simpa only [zero_smul] using hc.symm)
  · exact hnot (congrArg x (by simpa only [one_smul] using hc))
  · rw [neg_one_smul] at hc
    exact hnot ((hxNeg (S U)).symm.trans (congrArg x hc))

def baseBasis : Module.Basis (Fin 2) (ZMod 3) (T₃ A) :=
  letI := finite_torsion h₂ h₃ hA
  basisOfLinearIndependentOfCardEqFinrank (cycleIndependent h₂ h₃ hA hz hz₁ D)
    (by rw [finrank_torsion h₂ h₃ hA, Fintype.card_fin])

@[simp] theorem baseBasis_zero :
    baseBasis h₂ h₃ hA hz hz₁ D 0 = horizontal h₂ h₃ hA D := by
  simp [baseBasis]

@[simp] theorem baseBasis_one :
    baseBasis h₂ h₃ hA hz hz₁ D 1 = rotation h₂ h₃ hA hz 3 (horizontal h₂ h₃ hA D) := by
  simp [baseBasis]

/-- A lift of the horizontal order-three point and its rotation form a basis at the higher level. -/
theorem exists_cyclic_basis_of_lift (n : ℕ)
    (hCard : Nat.card (Level (Curve A).Point (n + 1)) = 9 ^ (n + 1))
    (P : Level (Curve A).Point (n + 1))
    (hP : (3 ^ n : ℕ) • (P : (Curve A).Point) = (horizontal h₂ h₃ hA D : (Curve A).Point)) :
    ∃ B : Module.Basis (Fin 2) (ZMod (3 ^ (n + 1))) (Level (Curve A).Point (n + 1)),
      rotation h₂ h₃ hA hz (3 ^ (n + 1)) (B 0) = B 1 := by
  let G := (Curve A).Point
  let B₀ := baseBasis h₂ h₃ hA hz hz₁ D
  let S := rotation h₂ h₃ hA hz (3 ^ (n + 1))
  let Q := S P
  let r := rotate z hz (CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂ h₃ hA)
  have hP' : (3 ^ n : ℕ) • (P : G) = (B₀ 0 : G) := by
    rw [show B₀ 0 = _ from baseBasis_zero h₂ h₃ hA hz hz₁ D]
    exact hP
  have hQ : (3 ^ n : ℕ) • (Q : G) = (B₀ 1 : G) := by
    rw [show B₀ 1 = _ from baseBasis_one h₂ h₃ hA hz hz₁ D]
    change (3 ^ n : ℕ) • r (P : G) = r (horizontal h₂ h₃ hA D : G)
    rw [← map_nsmul, hP]
  let e := equivOfLifts G B₀ n hCard P Q hP' hQ
  let B := (Module.Basis.finTwoProd (ZMod (3 ^ (n + 1)))).map e
  have he₀ : B 0 = P := by simp [B, e, equivOfLifts_apply]
  have he₁ : B 1 = Q := by simp [B, e, equivOfLifts_apply]
  refine ⟨B, ?_⟩
  change S (B 0) = B 1
  rw [he₀, he₁]

end
end ManuscriptAudit.CubicThreeRotationCyclicBasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeRotationCyclicBasis.baseBasis,
      ``ManuscriptAudit.CubicThreeRotationCyclicBasis.exists_cyclic_basis_of_lift] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
