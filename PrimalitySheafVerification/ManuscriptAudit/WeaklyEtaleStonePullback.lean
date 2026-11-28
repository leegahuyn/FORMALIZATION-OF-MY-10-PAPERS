import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.AffineRationalSectionUniqueness
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone
import PrimalitySheafVerification.ManuscriptAudit.StoneCechClopenBlocks

/-! The actual affine weakly étale scheme self-intersection carries the
topological fibre-pair space, including its topology. -/

namespace ManuscriptAudit.WeaklyEtaleStonePullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open AffineRationalSectionUniqueness (section_eq_of_point_eq_affine)
open WeaklyEtaleAlgebraicallyClosed (rationalSectionThrough)
open StoneCechClopenBlocks (PairOver)

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K))
variable (p : Y ⟶ X) [hp : WeaklyEtale p]
variable [hb : WeaklyEtale (p ≫ c)] [hY : IsAffine Y]

def pointPair (x : ↥(pullback p p : Scheme.{u})) : PairOver (fun y : ↥Y ↦ p y) :=
  ⟨(pullback.fst p p x, pullback.snd p p x), by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f : (pullback p p : Scheme.{u}) ⟶ X ↦ f x)
        (pullback.condition (f := p) (g := p))⟩

include hp hb hY in
private theorem pointPair_injective : Function.Injective (pointPair p) := by
  let b := p ≫ c
  let k := pullback.fst p p ≫ b
  letI : WeaklyEtale b := inferInstanceAs (WeaklyEtale (p ≫ c))
  letI : WeaklyEtale k := inferInstanceAs (WeaklyEtale (pullback.fst p p ≫ b))
  have hk : pullback.snd p p ≫ b = k := by
    dsimp only [b, k]
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  intro x y h
  have hl := congrArg (fun w : PairOver (fun z : ↥Y ↦ p z) ↦ w.1.1) h
  have hr := congrArg (fun w : PairOver (fun z : ↥Y ↦ p z) ↦ w.1.2) h
  change pullback.fst p p x = pullback.fst p p y at hl
  change pullback.snd p p x = pullback.snd p p y at hr
  obtain ⟨sx, hsx, hx⟩ := rationalSectionThrough K k x
  obtain ⟨sy, hsy, hy⟩ := rationalSectionThrough K k y
  have h₁ : sx ≫ pullback.fst p p = sy ≫ pullback.fst p p := by
    refine section_eq_of_point_eq_affine b _ _ ?_ ?_ ?_
    · simpa only [Category.assoc, k] using hsx
    · simpa only [Category.assoc, k] using hsy
    · change pullback.fst p p (sx (IsLocalRing.closedPoint K)) =
        pullback.fst p p (sy (IsLocalRing.closedPoint K))
      rw [hx, hy]
      exact hl
  have h₂ : sx ≫ pullback.snd p p = sy ≫ pullback.snd p p := by
    refine section_eq_of_point_eq_affine b _ _ ?_ ?_ ?_
    · simpa only [Category.assoc, hk] using hsx
    · simpa only [Category.assoc, hk] using hsy
    · change pullback.snd p p (sx (IsLocalRing.closedPoint K)) =
        pullback.snd p p (sy (IsLocalRing.closedPoint K))
      rw [hx, hy]
      exact hr
  have he : sx = sy := pullback.hom_ext h₁ h₂
  exact hx.symm.trans ((congrArg (fun t : Spec (CommRingCat.of K) ⟶
    (pullback p p : Scheme.{u}) ↦ t (IsLocalRing.closedPoint K)) he).trans hy)

private theorem pointPair_surjective : Function.Surjective (pointPair p) := by
  rintro ⟨⟨x, y⟩, h⟩
  obtain ⟨z, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) x y h
  exact ⟨z, Subtype.ext (Prod.ext h₁ h₂)⟩

private theorem pointPair_continuous : Continuous (pointPair p) :=
  ((pullback.fst p p).continuous.prodMk (pullback.snd p p).continuous).subtype_mk _

variable [IsAffine X]

/-- The homeomorphism sends a scheme pullback point to its two literal projections. -/
def homeomorph : ↥(pullback p p : Scheme.{u}) ≃ₜ PairOver (fun y : ↥Y ↦ p y) := by
  letI : T2Space ↥Y :=
    WeaklyEtaleAlgebraicallyClosedStone.t2Space_affine K (p ≫ c)
  letI : CompactSpace ↥(pullback p p : Scheme.{u}) := inferInstance
  let e := Equiv.ofBijective (pointPair p) ⟨pointPair_injective c p, pointPair_surjective p⟩
  have hq : IsQuotientMap (pointPair p) :=
    IsQuotientMap.of_surjective_continuous (pointPair_surjective p) (pointPair_continuous p)
  refine { toEquiv := e, continuous_toFun := pointPair_continuous p, continuous_invFun := ?_ }
  apply hq.continuous_iff.mpr
  change Continuous (e.symm ∘ e)
  have he : (e.symm ∘ e) = id := funext e.symm_apply_apply
  rw [he]
  exact continuous_id

theorem homeomorph_apply (x : ↥(pullback p p : Scheme.{u})) :
    homeomorph c p x = pointPair p x := rfl

end
end ManuscriptAudit.WeaklyEtaleStonePullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleStonePullback.pointPair,
      ``ManuscriptAudit.WeaklyEtaleStonePullback.homeomorph,
      ``ManuscriptAudit.WeaklyEtaleStonePullback.homeomorph_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
