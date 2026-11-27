import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationBranches
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationPuncture

/-! Native fibers of the affine nodal normalization after arbitrary
scheme base change: one point off the conductor, and both branch
preimages above the conductor. -/

namespace ManuscriptAudit.NodalAffineNormalizationFibers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps
open NodalNormalizationFiber (affineNode affineNormalization)
open NodalNormalizationBranches (branchMap branchPoint plus_over_node minus_over_node point_over_node)
open NodalNormalizationPuncture (nodePunctureMap normalization_puncture_isPullback)
open NodalAffineOrigin (originMap originPoint prime_eq_origin_iff_x_mem)
open NodalAffinePresentation (nodeX)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem points_lift {P U V S : Scheme.{0}}
    {a : P ⟶ U} {b : P ⟶ V} {f : U ⟶ S} {g : V ⟶ S}
    (H : IsPullback a b f g) (x : U) (y : V) (h : f x = g y) :
    ∃ z : P, a z = x ∧ b z = y := by
  obtain ⟨t, ht, ht'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y h
  refine ⟨H.isoPullback.inv t, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, ht]
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_snd, ht']

private theorem projection_eq_of_isIso_nearby {X Y U D : Scheme.{0}}
    (f : X ⟶ Y) (a : U ⟶ Y) (g : D ⟶ Y) [IsIso (pullback.fst g f)]
    (s t : ↥(pullback a f)) (u : U) (d : D) (hd : a u = g d)
    (hs : pullback.fst a f s = u) (ht : pullback.fst a f t = u) : s = t := by
  let m := pullback.fst a g
  let q := pullback.snd a g
  let r := pullback.fst q (pullback.fst g f)
  let b := pullback.snd q (pullback.fst g f) ≫ pullback.snd g f
  have h₁ : IsPullback b r f (q ≫ g) :=
    (IsPullback.of_hasPullback q (pullback.fst g f)).flip.paste_horiz
      (IsPullback.of_hasPullback g f).flip
  have h₁' : IsPullback b r f (m ≫ a) := by
    have h : q ≫ g = m ≫ a := pullback.condition.symm
    rwa [← h]
  let H := h₁'.of_right' (IsPullback.of_hasPullback a f).flip
  obtain ⟨c, hc, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := g) u d hd
  obtain ⟨s', hss, hsc⟩ := points_lift H s c (hs.trans hc.symm)
  obtain ⟨t', htt, htc⟩ := points_lift H t c (ht.trans hc.symm)
  haveI : IsIso r := inferInstance
  have ht' : s' = t' := r.homeomorph.injective (by simpa only [Scheme.Hom.homeomorph_apply] using hsc.trans htc.symm)
  exact hss.symm.trans (ht'.symm ▸ htt)

variable (K : Type) [Field K] {W : Scheme.{0}} (a : W ⟶ affineNode K)

abbrev Norm := pullback a (affineNormalization K)
abbrev Conductor := pullback a (originMap K)

/-- The ordered positive branch after arbitrary scheme base change. -/
abbrev plus : Conductor K a ⟶ Norm K a :=
  pullbackMap a (branchMap K 1) (plus_over_node K)

abbrev minus : Conductor K a ⟶ Norm K a :=
  pullbackMap a (branchMap K (-1)) (minus_over_node K)

/-- Any two points over the same point off the conductor are equal. -/
theorem points_equal_off_conductor (s t : Norm K a)
    (u : W) (hu : a u ≠ originPoint K)
    (hs : pullback.fst a (affineNormalization K) s = u)
    (ht : pullback.fst a (affineNormalization K) t = u) : s = t := by
  have h : a u ∈ Set.range (nodePunctureMap K) := by
    change a u ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (NodalNormalizationFiber.A K) (NodalNormalizationPuncture.nodeRing K)))
    rw [PrimeSpectrum.localization_away_comap_range (NodalNormalizationPuncture.nodeRing K)
      (NodalAwayNormalization.nodeX K)]
    change nodeX K ∉ (a u : PrimeSpectrum (NodalNormalizationFiber.A K)).asIdeal
    intro hx
    exact hu ((prime_eq_origin_iff_x_mem K _).mpr hx)
  obtain ⟨d, hd⟩ := h
  haveI : IsIso (pullback.fst (nodePunctureMap K) (affineNormalization K)) := by
    rw [← (normalization_puncture_isPullback K).isoPullback_inv_fst]
    infer_instance
  exact projection_eq_of_isIso_nearby (affineNormalization K) a (nodePunctureMap K)
    s t u d hd.symm hs ht

/-- Every point at the conductor comes from an actual base-changed rational branch. -/
theorem point_lifts_to_branch (s : Norm K a)
    (h : a (pullback.fst a (affineNormalization K) s) = originPoint K) :
    (∃ c : Conductor K a, plus K a c = s) ∨
      ∃ c : Conductor K a, minus K a c = s := by
  let t := pullback.snd a (affineNormalization K) s
  have ht : affineNormalization K t = originPoint K := by
    rw [← h]
    change (pullback.snd a (affineNormalization K) ≫ affineNormalization K) s =
      (pullback.fst a (affineNormalization K) ≫ a) s
    rw [pullback.condition] <;> rfl
  rcases (point_over_node K t).mp ht with h₁ | h₂
  · obtain ⟨c, hc, _⟩ := points_lift (pullbackMap_isPullback a (branchMap K 1) (plus_over_node K))
      s (IsLocalRing.closedPoint K) h₁
    exact Or.inl ⟨c, hc⟩
  · obtain ⟨c, hc, _⟩ := points_lift (pullbackMap_isPullback a (branchMap K (-1)) (minus_over_node K))
      s (IsLocalRing.closedPoint K) h₂
    exact Or.inr ⟨c, hc⟩

/-- The common conductor projection into the base-changed scheme is injective. -/
theorem conductor_projection_injective :
    Function.Injective (pullback.fst a (originMap K)) :=
  (pullback.fst a (originMap K)).isClosedEmbedding.injective

end
end ManuscriptAudit.NodalAffineNormalizationFibers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalAffineNormalizationFibers.points_equal_off_conductor,
      ``ManuscriptAudit.NodalAffineNormalizationFibers.point_lifts_to_branch,
      ``ManuscriptAudit.NodalAffineNormalizationFibers.conductor_projection_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
