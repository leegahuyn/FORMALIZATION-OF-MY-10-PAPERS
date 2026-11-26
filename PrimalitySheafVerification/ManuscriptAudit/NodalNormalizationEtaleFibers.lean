import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationBranches
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationPuncture

/-! Native fibers of the affine nodal normalization after arbitrary
étale base change: one point off the conductor, and both branch
preimages above the conductor. -/

namespace ManuscriptAudit.NodalNormalizationEtaleFibers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SmallEtaleBaseChange EtaleContinuousDirectImageMaps
open NodalNormalizationFiber (affineNode affineNormalization)
open NodalNormalizationBranches (branchMap branchPoint plus_over_node minus_over_node point_over_node)
open NodalNormalizationPuncture (nodePunctureMap normalization_puncture_isPullback)
open NodalAffineOrigin (originMap originPoint prime_eq_origin_iff_x_mem)
open NodalAffinePresentation (nodeX)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private theorem points_lift {P U V S : Scheme.{u}}
    {a : P ⟶ U} {b : P ⟶ V} {f : U ⟶ S} {g : V ⟶ S}
    (H : IsPullback a b f g) (x : U) (y : V) (h : f x = g y) :
    ∃ z : P, a z = x ∧ b z = y := by
  obtain ⟨t, ht, ht'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y h
  refine ⟨H.isoPullback.inv t, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, ht]
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_snd, ht']

private theorem projection_eq_of_isIso_nearby {X Y U D : Scheme.{u}}
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

private theorem restrictionSquare {X Y Z : Scheme.{u}} {p : Y ⟶ Z} {q : X ⟶ Z}
    (g : X ⟶ Y) (hg : g ≫ p = q) (U : Z.Etale) :
    IsPullback (baseChangeMap g hg U) (pullback.snd U.hom q) (pullback.snd U.hom p) g := by
  have H : IsPullback (baseChangeMap g hg U ≫ pullback.fst U.hom p)
      (pullback.snd U.hom q) U.hom (g ≫ p) := by
    rw [baseChangeMap_fst, hg]
    exact IsPullback.of_hasPullback U.hom q
  exact H.of_right (baseChangeMap_snd g hg U) (IsPullback.of_hasPullback U.hom p)

variable (K : Type u) [Field K]

abbrev Norm (U : (affineNode K).Etale) := (etaleBaseChange (affineNormalization K)).obj U
abbrev Conductor (U : (affineNode K).Etale) := (etaleBaseChange (originMap K)).obj U

/-- The ordered branches remain the actual branch arrows after any étale base change. -/
def plus (U : (affineNode K).Etale) : (Conductor K U).left ⟶ (Norm K U).left :=
  baseChangeMap (branchMap K 1) (plus_over_node K) U

def minus (U : (affineNode K).Etale) : (Conductor K U).left ⟶ (Norm K U).left :=
  baseChangeMap (branchMap K (-1)) (minus_over_node K) U

/-- Any two points over the same point off the conductor are equal. -/
theorem points_equal_off_conductor (U : (affineNode K).Etale) (s t : (Norm K U).left)
    (u : U.left) (hu : U.hom u ≠ originPoint K)
    (hs : pullback.fst U.hom (affineNormalization K) s = u)
    (ht : pullback.fst U.hom (affineNormalization K) t = u) : s = t := by
  have h : U.hom u ∈ Set.range (nodePunctureMap K) := by
    change U.hom u ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (NodalNormalizationFiber.A K) (NodalNormalizationPuncture.nodeRing K)))
    rw [PrimeSpectrum.localization_away_comap_range (NodalNormalizationPuncture.nodeRing K)
      (NodalAwayNormalization.nodeX K)]
    change nodeX K ∉ (U.hom u : PrimeSpectrum (NodalNormalizationFiber.A K)).asIdeal
    intro hx
    exact hu ((prime_eq_origin_iff_x_mem K _).mpr hx)
  obtain ⟨d, hd⟩ := h
  haveI : IsIso (pullback.fst (nodePunctureMap K) (affineNormalization K)) := by
    rw [← (normalization_puncture_isPullback K).isoPullback_inv_fst]
    infer_instance
  exact projection_eq_of_isIso_nearby (affineNormalization K) U.hom (nodePunctureMap K)
    s t u d hd.symm hs ht

/-- Every point at the conductor comes from an actual base-changed rational branch. -/
theorem point_lifts_to_branch (U : (affineNode K).Etale) (s : (Norm K U).left)
    (h : U.hom (pullback.fst U.hom (affineNormalization K) s) = originPoint K) :
    (∃ c : (Conductor K U).left, plus K U c = s) ∨
      ∃ c : (Conductor K U).left, minus K U c = s := by
  let t := pullback.snd U.hom (affineNormalization K) s
  have ht : affineNormalization K t = originPoint K := by
    rw [← h]
    change (pullback.snd U.hom (affineNormalization K) ≫ affineNormalization K) s =
      (pullback.fst U.hom (affineNormalization K) ≫ U.hom) s
    rw [pullback.condition] <;> rfl
  rcases (point_over_node K t).mp ht with h₁ | h₂
  · obtain ⟨c, hc, _⟩ := points_lift (restrictionSquare (branchMap K 1) (plus_over_node K) U)
      s (IsLocalRing.closedPoint K) h₁
    exact Or.inl ⟨c, hc⟩
  · obtain ⟨c, hc, _⟩ := points_lift (restrictionSquare (branchMap K (-1)) (minus_over_node K) U)
      s (IsLocalRing.closedPoint K) h₂
    exact Or.inr ⟨c, hc⟩

/-- The common conductor projection into the étale object is injective. -/
theorem conductor_projection_injective (U : (affineNode K).Etale) :
    Function.Injective (pullback.fst U.hom (originMap K)) :=
  (pullback.fst U.hom (originMap K)).isClosedEmbedding.injective

end
end ManuscriptAudit.NodalNormalizationEtaleFibers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizationEtaleFibers.points_equal_off_conductor,
      ``ManuscriptAudit.NodalNormalizationEtaleFibers.point_lifts_to_branch,
      ``ManuscriptAudit.NodalNormalizationEtaleFibers.conductor_projection_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
