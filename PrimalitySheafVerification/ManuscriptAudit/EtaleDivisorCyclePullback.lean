import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Data.Set.Finite.Lattice
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleClosedPoints
import PrimalitySheafVerification.ManuscriptAudit.EtaleDivisorCoefficients

/-!
# Étale restriction of the finite divisor cycles on integral charts

A height-one point pulls a coefficient back from its contraction. The
support remains finite because the fibers of contraction are finite.
The restriction is compatible with composition and with the actual
Dedekind-domain principal divisor.
-/

namespace ManuscriptAudit.AffineEtaleClosedPoints

open DedekindPrincipalDivisor IsDedekindDomain

noncomputable section

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra.Etale A B]

private theorem pullback_support_finite (d : HeightOneSpectrum A →₀ ℤ) :
    (Function.support (fun q : HeightOneSpectrum B ↦ d (comap A B q))).Finite := by
  have h : (⋃ p ∈ (d.support : Set (HeightOneSpectrum A)), (comap A B) ⁻¹' {p}).Finite := by
    apply d.support.finite_toSet.biUnion
    intro p _
    letI : Finite {q : HeightOneSpectrum B // comap A B q = p} := finite_comap_fiber A B p
    exact Set.toFinite ((comap A B) ⁻¹' {p})
  apply h.subset
  intro q hq
  exact Set.mem_iUnion₂.mpr ⟨comap A B q, Finsupp.mem_support_iff.mpr hq, rfl⟩

/-- Pull a finite divisor cycle back along an integral affine étale morphism. -/
def pullback : (HeightOneSpectrum A →₀ ℤ) →+ (HeightOneSpectrum B →₀ ℤ) where
  toFun d := Finsupp.ofSupportFinite _ (pullback_support_finite A B d)
  map_zero' := Finsupp.ext fun _ ↦ rfl
  map_add' _ _ := Finsupp.ext fun _ ↦ rfl

@[simp] theorem pullback_apply (d : HeightOneSpectrum A →₀ ℤ) (q : HeightOneSpectrum B) :
    pullback A B d q = d (comap A B q) :=
  rfl

/-- Restriction of divisor cycles composes along actual algebra maps. -/
theorem pullback_comp (C : Type*) [CommRing C] [IsDomain C]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Algebra.Etale B C] [Algebra.Etale A C] :
    (pullback B C).comp (pullback A B) = pullback A C := by
  apply AddMonoidHom.ext
  intro d
  apply Finsupp.ext
  intro q
  change d (comap A B (comap B C q)) = d (comap A C q)
  apply congrArg d
  apply HeightOneSpectrum.ext
  change (q.asIdeal.comap (algebraMap B C)).comap (algebraMap A B) =
    q.asIdeal.comap (algebraMap A C)
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A B C]

/-- Principal divisors commute with étale restriction to an integral chart. -/
theorem pullback_principalDivisor [IsDedekindDomain A] [IsDedekindDomain B]
    (F G : Type*) [Field F] [Field G] [Algebra A F] [Algebra B G]
    [IsFractionRing A F] [IsFractionRing B G] (ρ : F →+* G)
    (hρ : ∀ a : A, ρ (algebraMap A F a) = algebraMap B G (algebraMap A B a))
    (u : Additive Fˣ) :
    pullback A B (principalDivisor A F u) =
      principalDivisor B G (Additive.ofMul (Units.map ρ.toMonoidHom u.toMul)) := by
  apply Finsupp.ext
  intro q
  let p := comap A B q
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  exact (EtaleDivisorOrder.principalDivisor_coeff_map A B F G p q ρ hρ u).symm

end

end ManuscriptAudit.AffineEtaleClosedPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleClosedPoints.pullback_comp,
      ``ManuscriptAudit.AffineEtaleClosedPoints.pullback_principalDivisor] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
