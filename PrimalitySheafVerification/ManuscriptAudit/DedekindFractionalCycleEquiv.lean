import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrincipalDivisor

/-! Nonzero fractional ideals and finite height-one cycles are the same
native divisor group of an affine Dedekind domain. -/

namespace ManuscriptAudit.DedekindFractionalCycleEquiv

open IsDedekindDomain DedekindPrincipalDivisor FractionalIdeal
open scoped nonZeroDivisors

noncomputable section

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F]

private abbrev I := FractionalIdeal R⁰ F

/-- The actual height-one valuations of a unit fractional ideal. -/
def cycleMap : Additive (I R F)ˣ →+ (HeightOneSpectrum R →₀ ℤ) where
  toFun a := idealCycle R F a.toMul.val
  map_zero' := by
    ext v
    exact count_one F v
  map_add' a b := by
    ext v
    exact count_mul F v a.toMul.ne_zero b.toMul.ne_zero

private theorem cycleMap_bijective : Function.Bijective (cycleMap R F) := by
  constructor
  · intro a b h
    apply Additive.ext
    apply Units.ext
    have hCounts (v : HeightOneSpectrum R) : count F v a.toMul.val = count F v b.toMul.val :=
      congrArg (fun d : HeightOneSpectrum R →₀ ℤ => d v) h
    calc
      _ = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : I R F) ^ count F v a.toMul.val :=
        (finprod_heightOneSpectrum_factorization' F a.toMul.ne_zero).symm
      _ = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : I R F) ^ count F v b.toMul.val := by
        simp only [hCounts]
      _ = _ := finprod_heightOneSpectrum_factorization' F b.toMul.ne_zero
  · intro d
    obtain ⟨J, hJ, hd⟩ := idealCycle_surjective_nonzero R F d
    exact ⟨Additive.ofMul (Units.mk0 J hJ), hd⟩

/-- The native finite-cycle identification of the unit fractional ideals. -/
def cycleEquiv : Additive (I R F)ˣ ≃+ (HeightOneSpectrum R →₀ ℤ) :=
  AddEquiv.ofBijective (cycleMap R F) (cycleMap_bijective R F)

theorem cycleEquiv_principal (x : Additive Fˣ) :
    (cycleEquiv R F).symm (principalDivisor R F x) =
      Additive.ofMul (Units.mk0 (spanSingleton R⁰ (x.toMul : F))
        (spanSingleton_ne_zero_iff.mpr x.toMul.ne_zero)) := by
  apply (cycleEquiv R F).injective
  rw [AddEquiv.apply_symm_apply]
  rfl

end

end ManuscriptAudit.DedekindFractionalCycleEquiv

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DedekindFractionalCycleEquiv.cycleEquiv,
      ``ManuscriptAudit.DedekindFractionalCycleEquiv.cycleEquiv_principal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
