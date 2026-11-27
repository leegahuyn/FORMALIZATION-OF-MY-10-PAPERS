import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCyclicBasis
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeRotationCyclicBasis
import PrimalitySheafVerification.ManuscriptAudit.PowerTateEvaluationSurjective
import PrimalitySheafVerification.ManuscriptAudit.CubicTriplingSurjective

/-! The native cube-root rotation is nonscalar on the 2-adic and 3-adic Tate modules. -/

namespace ManuscriptAudit.CubicRotationTateRankTwo

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open PowerTorsionTower TorsionFrobeniusModule PowerTateModule PowerTateRankTwo
open PowerTateEvaluationSurjective CubicDoublingSurjective CubicTriplingSurjective

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {A z : K}
variable (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
variable (hz : z ^ 3 = 1) (hz₁ : z ≠ 1)

abbrev rotation : AddMonoid.End (Curve A).Point :=
  CubicCubeRotation.rotate z hz (shortCubic_discriminant_ne_zero h₂ h₃ hA)

variable (l : ℕ) [Fact l.Prime]

include hz₁ in
theorem exists_cyclic_first_basis (hl : l = 2 ∨ l = 3) :
    ∃ B : Module.Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l (Curve A).Point 1),
      mapLinear (l ^ 1) (rotation h₂ h₃ hA hz) (B 0) = B 1 := by
  rcases hl with rfl | rfl
  · exact CubicRotationCyclicBasis.exists_rotation_basis h₂ h₃ hA hz hz₁ 0
  · let D := Classical.choice (CubicThreeTorsionBasis.flexPair_nonempty h₂ hA)
    let B := CubicThreeRotationCyclicBasis.baseBasis h₂ h₃ hA hz hz₁ D
    refine ⟨B, ?_⟩
    change CubicThreeRotationCyclicBasis.rotation h₂ h₃ hA hz 3 (B 0) = B 1
    simp only [B, CubicThreeRotationCyclicBasis.baseBasis_zero, CubicThreeRotationCyclicBasis.baseBasis_one]

def firstBasis (hl : l = 2 ∨ l = 3) :
    Module.Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l (Curve A).Point 1) :=
  (exists_cyclic_first_basis h₂ h₃ hA hz hz₁ l hl).choose

include h₂ h₃ hA in
theorem scalar_surjective (hl : l = 2 ∨ l = 3) :
    Function.Surjective (fun P : (Curve A).Point => l • P) := by
  rcases hl with rfl | rfl
  · exact affine_doubling_surjective h₂ h₃ hA
  · exact affine_tripling_surjective h₂ h₃ hA

def tateBasis (hl : l = 2 ∨ l = 3) : Module.Basis (Fin 2) ℤ_[l] (Tate l (Curve A).Point) :=
  (Module.Basis.finTwoProd ℤ_[l]).map (padicPairEquiv l (Curve A).Point
    (firstBasis h₂ h₃ hA hz hz₁ l hl) (scalar_surjective h₂ h₃ hA l hl))

include hz₁ in
theorem rotation_not_scalar (hl : l = 2 ∨ l = 3) :
    ¬∃ c : ℤ_[l], endMap l (rotation h₂ h₃ hA hz) =
      c • (1 : Module.End ℤ_[l] (Tate l (Curve A).Point)) := by
  rintro ⟨c, hc⟩
  let G := (Curve A).Point
  let B := firstBasis h₂ h₃ hA hz hz₁ l hl
  let r := rotation h₂ h₃ hA hz
  letI : Fact (1 < (l ^ 1 : ℕ)) := ⟨by simpa only [pow_one] using (Fact.out : l.Prime).one_lt⟩
  have hB : mapLinear (l ^ 1) r (B 0) = B 1 :=
    (exists_cyclic_first_basis h₂ h₃ hA hz hz₁ l hl).choose_spec
  have h := scalar_reduction l G B (scalar_surjective h₂ h₃ hA l hl) r c hc 1
  have he := congrArg (fun f : Module.End (ZMod (l ^ 1)) (PowerTorsion l G 1) => f (B 0)) h
  change mapLinear (l ^ 1) r (B 0) = PadicInt.toZModPow 1 c • B 0 at he
  rw [hB] at he
  have hw := congrArg (fun v : PowerTorsion l G 1 => B.repr v (1 : Fin 2)) he
  exact (one_ne_zero : (1 : ZMod (l ^ 1)) ≠ 0) (by simpa [Module.Basis.repr_self] using hw)

end
end ManuscriptAudit.CubicRotationTateRankTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicRotationTateRankTwo.exists_cyclic_first_basis,
      ``ManuscriptAudit.CubicRotationTateRankTwo.tateBasis,
      ``ManuscriptAudit.CubicRotationTateRankTwo.rotation_not_scalar] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
