import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSignedTwistTate

/-! Compute both Tate coefficients from a sextic residue and a certified reference endomorphism. -/

namespace ManuscriptAudit.CubicSexticTwistCoefficientFormula

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicFrobeniusSexticTwists CubicOrdinatePreservingTwist CubicSignedTwistTate PowerTateModule

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

def rotationIndex (z v : K) : Fin 3 :=
  if v ^ 2 = 1 then 0 else if v ^ 2 = z then 1 else 2

def ordinateSign (v : K) : ℤ :=
  if v ^ 3 = 1 then 1 else -1

def predictedTrace (z v : K) (a b : ℤ) : ℤ :=
  let c := signedCoefficients (rotationIndex z v) (ordinateSign v) a b
  2 * c.1 - c.2

private theorem rotationIndex_spec {z v : K} (h : ∃ j : Fin 3, z ^ j.val = v ^ 2) :
    v ^ 2 = z ^ (rotationIndex z v).val := by
  unfold rotationIndex
  split
  · rename_i he
    change v ^ 2 = z ^ (0 : ℕ)
    simpa only [pow_zero] using he
  · rename_i h₀
    split
    · rename_i he
      change v ^ 2 = z ^ (1 : ℕ)
      simpa only [pow_one] using he
    · rename_i h₁
      obtain ⟨j, hj⟩ := h
      fin_cases j
      · change z ^ (0 : ℕ) = v ^ 2 at hj
        exact (h₀ (by simpa only [pow_zero] using hj.symm)).elim
      · change z ^ (1 : ℕ) = v ^ 2 at hj
        exact (h₁ (by simpa only [pow_one] using hj.symm)).elim
      · exact hj.symm

private theorem ordinateSign_spec {v : K} (h : v ^ 3 = 1 ∨ v ^ 3 = -1) :
    (ordinateSign v = 1 ∨ ordinateSign v = -1) ∧ v ^ 3 = (ordinateSign v : K) := by
  unfold ordinateSign
  split
  · rename_i he
    exact ⟨Or.inl rfl, by simpa only [Int.cast_one] using he⟩
  · rename_i he
    exact ⟨Or.inr rfl, by simpa only [Int.cast_neg, Int.cast_one] using h.resolve_left he⟩

variable {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L] [DecidableEq L]

/-- The explicit coefficient formula applies to every twist of a certified reference. -/
theorem trace_det (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0) {A B : K}
    (hA : A ≠ 0) (hB : B ≠ 0) {k : ℕ} (hq : Fintype.card K = 6 * k + 1)
    {z : K} (hz : IsPrimitiveRoot z 3) (a b : ℤ)
    (hF : arithmeticFrobenius K L A =
      a • (1 : AddMonoid.End (Geometric K L A)) +
        b • (pointRotation (hz.map_of_injective (algebraMap K L).injective).pow_eq_one
          (shortCubic_discriminant_ne_zero h₂ h₃ ((map_ne_zero (algebraMap K L)).mpr hA)) :
            AddMonoid.End (Geometric K L A)))
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric K L B))
      (endMap l (arithmeticFrobenius K L B)) = (predictedTrace z (parameter A B k) a b : ℤ_[l]) ∧
    LinearMap.det (endMap l (arithmeticFrobenius K L B)) =
      ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℤ_[l]) := by
  let i := algebraMap K L
  let v := parameter A B k
  have hΔA := shortCubic_discriminant_ne_zero h₂ h₃ ((map_ne_zero i).mpr hA)
  have hΔB := shortCubic_discriminant_ne_zero h₂ h₃ ((map_ne_zero i).mpr hB)
  have hzL := hz.map_of_injective i.injective
  obtain ⟨j, hj, hSign⟩ := rotation_sign hA hB hz hq
  have hRot := rotationIndex_spec ⟨j, hj⟩
  obtain ⟨hε, hY⟩ := ordinateSign_spec hSign
  have hX' : (i v) ^ 2 = (i z) ^ (rotationIndex z v).val := by
    simpa only [map_pow] using congrArg i hRot
  have hY' : (i v) ^ 3 = (ordinateSign v : L) := by
    simpa only [map_pow, map_intCast] using congrArg i hY
  exact CubicSignedTwistTate.trace_det h₂ h₃ A B hA hB hq hΔA hΔB (i z)
    hzL.pow_eq_one (hzL.ne_one (by decide)) (rotationIndex z v) hX'
    (ordinateSign v) hε hY' a b hF l hl

end
end ManuscriptAudit.CubicSexticTwistCoefficientFormula

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSexticTwistCoefficientFormula.trace_det
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
