import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationSwapPullback

/-! Reflecting the polynomial parameter gives retractions of both closed branches of the swap cover. -/

namespace ManuscriptAudit.NodalNormalizationSwapRetraction

open AlgebraicGeometry CategoryTheory Polynomial
open NodalNormalizationFiber (B affineLine)
open NodalNormalizationSwapPullback (first second toCover)
open NodalSwapCover (Cover swap)
open NodalSwapCoverConnected (firstProjection secondProjection)
open NodalSwapCoverNoSection (coverScheme)

noncomputable section

universe u
variable (K : Type u) [Field K]

private def reflect : B K →+* B K := Polynomial.compRingHom (-Polynomial.X)

private theorem reflect_eval (f : B K) (a : K) :
    (reflect K f).eval a = f.eval (-a) := by
  change (f.comp (-Polynomial.X)).eval a = f.eval (-a)
  rw [eval_comp, eval_neg, eval_X]

/-- Extending a polynomial to the other component by reflecting the parameter. -/
def firstSection : B K →+* Cover K where
  toFun f := ⟨(f, reflect K f), by
    change f.eval 1 = (reflect K f).eval (-1) ∧ f.eval (-1) = (reflect K f).eval 1
    simp only [reflect_eval, neg_neg, and_self]⟩
  map_one' := Subtype.ext (Prod.ext rfl (map_one _))
  map_mul' _ _ := Subtype.ext (Prod.ext rfl (map_mul _ _ _))
  map_zero' := Subtype.ext (Prod.ext rfl (map_zero _))
  map_add' _ _ := Subtype.ext (Prod.ext rfl (map_add _ _ _))

def secondSection : B K →+* Cover K :=
  (swap K).toRingHom.comp (firstSection K)

theorem firstProjection_firstSection :
    (firstProjection K).comp (firstSection K) = RingHom.id (B K) :=
  RingHom.ext fun _ ↦ rfl

theorem secondProjection_secondSection :
    (secondProjection K).comp (secondSection K) = RingHom.id (B K) :=
  RingHom.ext fun _ ↦ rfl

def firstRetraction : coverScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (firstSection K))

def secondRetraction : coverScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (secondSection K))

private def firstRingProjection : CommRingCat.of (Cover K) ⟶ CommRingCat.of (B K) :=
  CommRingCat.ofHom (firstProjection K)

private def secondRingProjection : CommRingCat.of (Cover K) ⟶ CommRingCat.of (B K) :=
  CommRingCat.ofHom (secondProjection K)

private def firstRingSection : CommRingCat.of (B K) ⟶ CommRingCat.of (Cover K) :=
  CommRingCat.ofHom (firstSection K)

private def secondRingSection : CommRingCat.of (B K) ⟶ CommRingCat.of (Cover K) :=
  CommRingCat.ofHom (secondSection K)

private theorem firstRing_id :
    firstRingSection K ≫ firstRingProjection K = 𝟙 (CommRingCat.of (B K)) := by
  apply CommRingCat.hom_ext
  change (firstProjection K).comp (firstSection K) = RingHom.id (B K)
  exact firstProjection_firstSection K

private theorem secondRing_id :
    secondRingSection K ≫ secondRingProjection K = 𝟙 (CommRingCat.of (B K)) := by
  apply CommRingCat.hom_ext
  change (secondProjection K).comp (secondSection K) = RingHom.id (B K)
  exact secondProjection_secondSection K

/-- The first polynomial component is a split closed branch of the swap cover. -/
theorem first_retraction :
    (first K ≫ toCover K) ≫ firstRetraction K = 𝟙 (affineLine K) := by
  rw [NodalNormalizationSwapPullback.first_toCover, firstRetraction, ← Spec.map_comp]
  change Spec.map (firstRingSection K ≫ firstRingProjection K) = _
  rw [firstRing_id, Spec.map_id]

/-- The second polynomial component is a split closed branch of the swap cover. -/
theorem second_retraction :
    (second K ≫ toCover K) ≫ secondRetraction K = 𝟙 (affineLine K) := by
  rw [NodalNormalizationSwapPullback.second_toCover, secondRetraction, ← Spec.map_comp]
  change Spec.map (secondRingSection K ≫ secondRingProjection K) = _
  rw [secondRing_id, Spec.map_id]

end

end ManuscriptAudit.NodalNormalizationSwapRetraction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.NodalNormalizationSwapRetraction.first_retraction,
      ``ManuscriptAudit.NodalNormalizationSwapRetraction.second_retraction] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
