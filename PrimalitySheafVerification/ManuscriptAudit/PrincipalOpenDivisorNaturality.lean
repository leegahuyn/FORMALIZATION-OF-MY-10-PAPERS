import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenDivisor

/-!
# Restriction of the divisor sequence on the principal-open basis

Coordinate rings restrict along any inclusion of actual basic opens
of the prime spectrum. The compatible cycle map forgets the points
removed by restriction. These are the naturality squares of the
principal-open divisor sequence.
-/

namespace ManuscriptAudit.AffineLineDivisor

open RatFuncPrincipalOpen

noncomputable section

variable (K : Type*) [Field K]

/-- Canonical restriction along an inclusion of principal opens. -/
def restrictRing (f g : Polynomial K) (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    Localization.Away f →+* Localization.Away g :=
  Localization.awayLift (algebraMap (Polynomial K) (Localization.Away g)) f
    ((PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
      (S := Localization.Away g)).mp h)

@[simp] theorem restrictRing_algebraMap (f g : Polynomial K)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (p : Polynomial K) :
    restrictRing K f g h (algebraMap (Polynomial K) (Localization.Away f) p) =
      algebraMap (Polynomial K) (Localization.Away g) p :=
  IsLocalization.Away.lift_eq f ((PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
    (S := Localization.Away g)).mp h) p

theorem restrictRing_id (f : Polynomial K) : restrictRing K f f le_rfl = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  apply RingHom.ext
  intro a
  simp [RingHom.comp_apply]

theorem restrictRing_comp (f g k : Polynomial K)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (h' : PrimeSpectrum.basicOpen k ≤ PrimeSpectrum.basicOpen g) :
    (restrictRing K g k h').comp (restrictRing K f g h) = restrictRing K f k (h'.trans h) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  apply RingHom.ext
  intro a
  simp [RingHom.comp_apply]

theorem toRatFunc_restrictRing (f g : Polynomial K)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (hf : f ≠ 0) (hg : g ≠ 0) :
    (toRatFunc K g hg).comp (restrictRing K f g h) = toRatFunc K f hf := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  apply RingHom.ext
  intro a
  simp [RingHom.comp_apply]

/-- Restriction on the units of the coordinate rings. -/
def restrictUnits (f g : Polynomial K)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    Additive (Localization.Away f)ˣ →+ Additive (Localization.Away g)ˣ :=
  (Units.map (restrictRing K f g h).toMonoidHom).toAdditive

theorem unitMap_restrictUnits (f g : Polynomial K)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (hf : f ≠ 0) (hg : g ≠ 0) :
    (unitMap K g hg).comp (restrictUnits K f g h) = unitMap K f hf := by
  apply AddMonoidHom.ext
  intro u
  apply Additive.ext
  apply Units.ext
  exact RingHom.congr_fun (toRatFunc_restrictRing K f g h hf hg) (u.toMul : Localization.Away f)

private def pointEmbedding (f g : Polynomial K)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) : OpenPoint K g ↪ OpenPoint K f where
  toFun a := ⟨a.val, by
    intro hz
    have hu : IsUnit (algebraMap (Polynomial K) (Localization.Away g) f) :=
      (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
        (S := Localization.Away g)).mp h
    obtain ⟨n, q, hq⟩ := (IsLocalization.Away.algebraMap_isUnit_iff g).mp hu
    have he := congrArg (fun p : Polynomial K => p.eval a.val) hq
    exact pow_ne_zero n a.property (by simpa only [Polynomial.eval_pow, Polynomial.eval_mul,
      hz, zero_mul] using he)⟩
  inj' := fun _ _ e => Subtype.ext (congrArg (fun a : OpenPoint K f => a.val) e)

/-- On cycles, restriction retains the coefficients of points still in the open. -/
def restrictCycles (f g : Polynomial K)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    (OpenPoint K f →₀ ℤ) →+ (OpenPoint K g →₀ ℤ) :=
  Finsupp.comapDomain.addMonoidHom (pointEmbedding K f g h).injective

theorem divisorOnOpen_restrictCycles (f g : Polynomial K)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    (restrictCycles K f g h).comp (divisorOnOpen K f) = divisorOnOpen K g := by
  apply AddMonoidHom.ext
  intro z
  apply Finsupp.ext
  intro a
  rfl

end

end ManuscriptAudit.AffineLineDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisor.restrictRing_comp,
      ``ManuscriptAudit.AffineLineDivisor.unitMap_restrictUnits,
      ``ManuscriptAudit.AffineLineDivisor.divisorOnOpen_restrictCycles] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
