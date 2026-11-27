import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAlgebraicallyClosed
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Stalks on an actual weakly étale scheme over an algebraically closed
field agree with the base field. -/

namespace ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStalk

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeaklyEtaleAlgebraicallyClosed (rationalSectionThrough)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private theorem flat_stalkMap_injective {U V : Scheme.{u}} (s : U ⟶ V) [Flat s] (y : U) :
    Function.Injective (s.stalkMap y).hom := by
  algebraize [(s.stalkMap y).hom]
  have : Module.FaithfullyFlat (V.presheaf.stalk (s y)) (U.presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap s y) (s.toLRSHom.prop y)
  exact ‹RingHom.FaithfullyFlat _›.injective

variable (K : Type u) [Field K] [IsAlgClosed K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [WeaklyEtale f]

/-- The actual structure stalk map is bijective at every point. -/
theorem stalkMap_bijective (x : X) : Function.Bijective (f.stalkMap x).hom := by
  obtain ⟨s, hs, hx⟩ := rationalSectionThrough K f x
  subst x
  let y := IsLocalRing.closedPoint K
  letI : WeaklyEtale (s ≫ f) := by rw [hs]; infer_instance
  letI : WeaklyEtale s := WeaklyEtale.of_comp s f
  letI : IsIso (f.stalkMap (s y) ≫ s.stalkMap y) := by
    rw [← Scheme.Hom.stalkMap_comp, hs, Scheme.Hom.stalkMap_id]
    infer_instance
  have hc : Function.Bijective (f.stalkMap (s y) ≫ s.stalkMap y).hom :=
    (asIso (f.stalkMap (s y) ≫ s.stalkMap y)).commRingCatIsoToRingEquiv.bijective
  have hi : Function.Injective (s.stalkMap y).hom := flat_stalkMap_injective s y
  constructor
  · intro a b hab
    apply hc.injective
    exact congrArg (s.stalkMap y).hom hab
  · intro b
    obtain ⟨a, ha⟩ := hc.surjective ((s.stalkMap y).hom b)
    exact ⟨a, hi ha⟩

include f in
/-- The native stalk itself is a field, in addition to its residue field. -/
theorem stalk_isField (x : X) : IsField (X.presheaf.stalk x) := by
  let p : PrimeSpectrum K := f x
  have hn : (0 : K) ∉ p.asIdeal.primeCompl := by
    intro h
    exact h (Ideal.zero_mem _)
  let e₀ := RingEquiv.ofBijective (algebraMap K (Localization.AtPrime p.asIdeal))
    ((Field.toIsField K).localization_map_bijective hn)
  let e₁ := (Spec.stalkIso (CommRingCat.of K) p).commRingCatIsoToRingEquiv
  let e₂ := RingEquiv.ofBijective (f.stalkMap x).hom (stalkMap_bijective K f x)
  exact (e₀.trans (e₁.symm.trans e₂)).symm.toMulEquiv.isField (Field.toIsField K)

/-- For a weakly étale affine over the field, every prime localization is a field. -/
theorem localRing_isField {R : CommRingCat.{u}} (a : Spec R ⟶ Spec (CommRingCat.of K))
    [WeaklyEtale a] (p : PrimeSpectrum R) : IsField (Localization.AtPrime p.asIdeal) :=
  (Spec.stalkIso R p).commRingCatIsoToRingEquiv.symm.toMulEquiv.isField (stalk_isField K a p)

end
end ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStalk

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStalk.stalkMap_bijective,
      ``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStalk.stalk_isField,
      ``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStalk.localRing_isField] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
