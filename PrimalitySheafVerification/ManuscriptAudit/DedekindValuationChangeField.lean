import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrincipalOrder

/-! The actual height-one valuations and principal divisors are invariant
under the native identification of two fraction fields of the same ring. -/

namespace ManuscriptAudit.DedekindValuationChangeField

open IsDedekindDomain DedekindPrincipalDivisor DedekindPrincipalOrder WithZero

noncomputable section

variable (R F L : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field F] [Field L] [Algebra R F] [Algebra R L] [IsFractionRing R F] [IsFractionRing R L]
  (g : F →+* L) (hg : ∀ a : R, g (algebraMap R F a) = algebraMap R L a)

include hg in
/-- A base-preserving fraction-field homomorphism leaves each true
height-one valuation unchanged. -/
theorem valuation_map (v : HeightOneSpectrum R) (x : F) :
    v.valuation L (g x) = v.valuation F x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R x
  rw [map_div₀, hg, hg, Valuation.map_div, Valuation.map_div,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

include hg in
/-- The actual principal-divisor cycle is unchanged on changing fraction fields. -/
theorem principalDivisor_map (u : Additive Fˣ) :
    principalDivisor R L (Additive.ofMul (Units.map g.toMonoidHom u.toMul)) =
      principalDivisor R F u := by
  apply Finsupp.ext
  intro v
  rw [principalDivisor_apply, principalDivisor_apply]
  exact congrArg (fun q => -log q) (valuation_map R F L g hg v (u.toMul : F))

end

end ManuscriptAudit.DedekindValuationChangeField

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DedekindValuationChangeField.valuation_map,
      ``ManuscriptAudit.DedekindValuationChangeField.principalDivisor_map] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"

