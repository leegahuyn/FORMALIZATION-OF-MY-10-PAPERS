import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrincipalDivisor
import PrimalitySheafVerification.ManuscriptAudit.EtaleDivisorOrder

/-!
# Restriction of the actual principal-divisor coefficients

The ideal multiplicity in the global Dedekind ring equals the normalized
order in the localization. For a fraction its divisor coefficient is the
difference of the numerator and denominator orders. Étale restriction
therefore preserves the coefficient at a point lying over the original
height-one point.
-/

namespace ManuscriptAudit.EtaleDivisorOrder

open DedekindPrincipalDivisor Ideal IsDedekindDomain IsDiscreteValuationRing IsLocalRing
open scoped nonZeroDivisors

noncomputable section

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- The order of a regular section at a height-one point, with infinity at zero. -/
abbrev regularOrder (p : HeightOneSpectrum R) (a : R) : ℕ∞ :=
  emultiplicity p.asIdeal (Ideal.span {a})

private local instance localDVR (p : HeightOneSpectrum R) :
    IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain p.ne_bot _

/-- The global ideal order is the additive order in the actual local ring. -/
theorem local_addVal_eq_regularOrder (p : HeightOneSpectrum R) (a : R) :
    addVal (Localization.AtPrime p.asIdeal)
      (algebraMap R (Localization.AtPrime p.asIdeal) a) = regularOrder R p a := by
  let RP := Localization.AtPrime p.asIdeal
  letI : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal p.isPrime p.ne_bot
  obtain ⟨t, ht⟩ := exists_irreducible RP
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  change (n : ℕ∞) ≤ addVal RP (algebraMap R RP a) ↔
    (n : ℕ∞) ≤ emultiplicity p.asIdeal (Ideal.span {a})
  rw [← ht.addVal_pow n, addVal_le_iff_dvd, ← Ideal.mem_span_singleton,
    ← Ideal.span_singleton_pow, ← ht.maximalIdeal_eq, ← pow_dvd_iff_le_emultiplicity,
    Ideal.dvd_span_singleton]
  change a ∈ (maximalIdeal RP ^ n).under R ↔ a ∈ p.asIdeal ^ n
  rw [IsLocalization.AtPrime.under_maximalIdeal_pow p.asIdeal]

/-- Étale restriction preserves the order of a regular section at lying-over
height-one points. -/
theorem regularOrder_algebraMap (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra R S] [Algebra.Etale R S] (p : HeightOneSpectrum R) (q : HeightOneSpectrum S)
    [q.asIdeal.LiesOver p.asIdeal] (a : R) :
    regularOrder S q (algebraMap R S a) = regularOrder R p a := by
  rw [← local_addVal_eq_regularOrder S q, ← local_addVal_eq_regularOrder R p]
  rw [← Localization.localRingHom_to_map p.asIdeal q.asIdeal (algebraMap R S)
    (Ideal.LiesOver.over : p.asIdeal = q.asIdeal.comap (algebraMap R S))]
  exact localRingHom_addVal R S p q _

private theorem regularOrder_toNat (p : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) :
    (regularOrder R p a).toNat =
      (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span ({a} : Set R))).factors := by
  classical
  have ha' : (Ideal.span {a} : Ideal R) ≠ 0 := by
    rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
    exact ha
  change (emultiplicity p.asIdeal (Ideal.span {a})).toNat = _
  rw [Ideal.count_associates_factors_eq ha' p.isPrime p.ne_bot,
    emultiplicity_eq_count_normalizedFactors p.irreducible ha', normalize_eq, ENat.toNat_coe]

/-- The coefficient of a fraction is the difference of the two normalized orders. -/
theorem principalDivisor_coeff_div (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    (p : HeightOneSpectrum R) (v : Additive Fˣ) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (v.toMul : F) = algebraMap R F a / algebraMap R F b) :
    principalDivisor R F v p =
      (regularOrder R p a).toNat - ((regularOrder R p b).toNat : ℤ) := by
  classical
  let I := FractionalIdeal.spanSingleton R⁰ (v.toMul : F)
  have hI : I ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr v.toMul.ne_zero
  have hDiv : I = FractionalIdeal.spanSingleton R⁰ (algebraMap R F b)⁻¹ *
      ((Ideal.span {a} : Ideal R) : FractionalIdeal R⁰ F) := by
    dsimp [I]
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      h, div_eq_mul_inv, mul_comm (algebraMap R F a)]
  change FractionalIdeal.count F p I = _
  rw [FractionalIdeal.count_well_defined F p hI hDiv, regularOrder_toNat R p ha,
    regularOrder_toNat R p hb]

/-- The coefficient of a principal divisor is preserved under étale
restriction to each height-one point over the given point. -/
theorem principalDivisor_coeff_map (S F G : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra R S] [Algebra.Etale R S] [Field F] [Field G] [Algebra R F] [Algebra S G]
    [IsFractionRing R F] [IsFractionRing S G]
    (p : HeightOneSpectrum R) (q : HeightOneSpectrum S) [q.asIdeal.LiesOver p.asIdeal]
    (ρ : F →+* G) (hρ : ∀ a : R, ρ (algebraMap R F a) = algebraMap S G (algebraMap R S a))
    (u : Additive Fˣ) :
    principalDivisor S G (Additive.ofMul (Units.map ρ.toMonoidHom u.toMul)) q =
      principalDivisor R F u p := by
  obtain ⟨a, b, hb₀, hu⟩ := IsFractionRing.div_surjective R (u.toMul : F)
  have ha : a ≠ 0 := by
    intro h
    rw [h, map_zero, zero_div] at hu
    exact u.toMul.ne_zero hu.symm
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb₀
  have hne (x : R) (hx : x ≠ 0) : algebraMap R S x ≠ 0 := by
    intro h
    have H := hρ x
    rw [h, map_zero] at H
    exact hx ((IsFractionRing.injective R F) (ρ.injective (H.trans (map_zero ρ).symm)))
  let v := Additive.ofMul (Units.map ρ.toMonoidHom u.toMul)
  have hv : (v.toMul : G) = algebraMap S G (algebraMap R S a) /
      algebraMap S G (algebraMap R S b) := by
    change ρ (u.toMul : F) = _
    rw [← hu, map_div₀, hρ, hρ]
  change principalDivisor S G v q = _
  rw [principalDivisor_coeff_div S G q v (hne a ha) (hne b hb) hv,
    principalDivisor_coeff_div R F p u ha hb hu.symm,
    regularOrder_algebraMap R S p q, regularOrder_algebraMap R S p q]

end

end ManuscriptAudit.EtaleDivisorOrder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleDivisorOrder.local_addVal_eq_regularOrder,
      ``ManuscriptAudit.EtaleDivisorOrder.regularOrder_algebraMap,
      ``ManuscriptAudit.EtaleDivisorOrder.principalDivisor_coeff_div,
      ``ManuscriptAudit.EtaleDivisorOrder.principalDivisor_coeff_map] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
