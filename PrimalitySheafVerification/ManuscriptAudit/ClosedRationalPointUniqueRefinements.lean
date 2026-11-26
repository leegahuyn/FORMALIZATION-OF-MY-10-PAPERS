import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import PrimalitySheafVerification.ManuscriptAudit.SkyscraperUniqueRefinements
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleGeometricBaseChange

/-!
# Single-lift étale neighborhoods of a closed rational point

A marked lift gives a section of the étale base change to the residue
field. That section is open, and the closed embedding of the base
change into the original neighborhood lets us cut out precisely the
section by an open refinement.
-/

namespace ManuscriptAudit.SmallEtaleGeometricBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem section_isOpenImmersion {Y S : Scheme.{u}} (m : Y ⟶ S) [Etale m]
    (σ : S ⟶ Y) (hσ : σ ≫ m = 𝟙 S) : IsOpenImmersion σ := by
  let g : Y ⟶ pullback m m := pullback.lift (𝟙 Y) (m ≫ σ) (by simp [hσ])
  have hw : σ ≫ pullback.diagonal m = σ ≫ g := by
    apply pullback.hom_ext
    · simp [g]
    · simp [g, Category.assoc, reassoc_of% hσ]
  have H : IsPullback σ σ (pullback.diagonal m) g := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw (fun c => c.snd ≫ m) ?_ ?_ ?_)
    · intro c
      have w := congrArg (fun f => f ≫ pullback.snd m m) c.condition
      simpa [g, Category.assoc] using w.symm
    · intro c
      have w := congrArg (fun f => f ≫ pullback.fst m m) c.condition
      have e : c.fst = c.snd := by simpa [g, Category.assoc] using w
      have w' := congrArg (fun f => f ≫ pullback.snd m m) c.condition
      simpa [g, Category.assoc, e] using w'.symm
    · intro c l _ hl
      calc
        l = (l ≫ σ) ≫ m := by simp [Category.assoc, hσ]
        _ = c.snd ≫ m := by rw [hl]
  exact MorphismProperty.of_isPullback H (inferInstanceAs (IsOpenImmersion (pullback.diagonal m)))

variable {K : Type u} [Field K] [IsSepClosed K]
variable {X : Scheme.{u}} (i : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion i]

private abbrev S := Spec (CommRingCat.of K)
private abbrev Φ := Scheme.pointSmallEtale i

set_option maxHeartbeats 1200000 in
theorem closedRationalPoint_unique_refinements (W : X.Etale) (w : (Φ i).fiber.obj W) :
    ∃ (V : X.Etale) (g : V ⟶ W) (v : (Φ i).fiber.obj V),
      (Φ i).fiber.map g v = w ∧ Subsingleton ((Φ i).fiber.obj V) := by
  let r := pullback.fst W.hom i
  let m := pullback.snd W.hom i
  let σ : S (K := K) ⟶ pullback W.hom i :=
    pullback.lift w.left (𝟙 _) (by simpa using Over.w w)
  have hσ : σ ≫ m = 𝟙 _ := pullback.lift_snd _ _ _
  letI : Etale W.hom := W.prop
  letI : Etale m := inferInstanceAs (Etale (pullback.snd W.hom i))
  letI : IsClosedImmersion r := inferInstanceAs (IsClosedImmersion (pullback.fst W.hom i))
  letI : IsOpenImmersion σ := section_isOpenImmersion m σ hσ
  obtain ⟨A, hA, hEq⟩ := r.isClosedEmbedding.isInducing.isOpen_iff.mp
    σ.isOpenEmbedding.isOpen_range
  let B : W.left.Opens := ⟨A, hA⟩
  have hB : Set.range B.ι = A := by
    change (B.ι.opensRange : Set W.left) = A
    rw [Scheme.Opens.opensRange_ι]
    rfl
  have hLift : Set.range w.left ⊆ Set.range B.ι := by
    rw [hB]
    rintro _ ⟨a, rfl⟩
    have ha : σ a ∈ r ⁻¹' A := by rw [hEq]; exact ⟨a, rfl⟩
    change r (σ a) ∈ A at ha
    simpa only [← Scheme.Hom.comp_apply, σ, r, pullback.lift_fst] using ha
  let v₀ := IsOpenImmersion.lift B.ι w.left hLift
  have hv : v₀ ≫ B.ι = w.left := IsOpenImmersion.lift_fac _ _ _
  let V : X.Etale := Scheme.Etale.mk (B.ι ≫ W.hom)
  let g : V ⟶ W := MorphismProperty.Over.homMk B.ι rfl
  let v : (Φ i).fiber.obj V := Over.homMk v₀ (by
    change v₀ ≫ (B.ι ≫ W.hom) = i
    rw [← Category.assoc, hv]
    exact Over.w w)
  refine ⟨V, g, v, CostructuredArrow.hom_ext _ _ hv, ?_⟩
  have unique (k : (Φ i).fiber.obj V) : k = v := by
    let τ : S (K := K) ⟶ pullback W.hom i :=
      pullback.lift (k.left ≫ B.ι) (𝟙 _) (by
        rw [Category.assoc, Category.id_comp]
        exact Over.w k)
    have hτr : τ ≫ r = k.left ≫ B.ι := pullback.lift_fst _ _ _
    have hτm : τ ≫ m = 𝟙 _ := pullback.lift_snd _ _ _
    have hRangeτ : Set.range τ ⊆ Set.range σ := by
      rw [← hEq]
      rintro _ ⟨a, rfl⟩
      change r (τ a) ∈ A
      rw [← Scheme.Hom.comp_apply, hτr, Scheme.Hom.comp_apply, ← hB]
      exact ⟨k.left a, rfl⟩
    let l := IsOpenImmersion.lift σ τ hRangeτ
    have hl : l ≫ σ = τ := IsOpenImmersion.lift_fac _ _ _
    have hId : l = 𝟙 _ := by
      calc
        l = (l ≫ σ) ≫ m := by simp [Category.assoc, hσ]
        _ = 𝟙 _ := by rw [hl, hτm]
    have hτσ : τ = σ := by rw [← hl, hId, Category.id_comp]
    apply CostructuredArrow.hom_ext
    change k.left = v₀
    apply (cancel_mono B.ι).mp
    rw [hv, ← hτr, hτσ]
    exact pullback.lift_fst _ _ _
  exact ⟨fun a b => (unique a).trans (unique b).symm⟩

/-- The geometric skyscraper has its original coefficient group at a closed rational point. -/
theorem closedRationalPoint_skyscraperCounit_isIso (M : AddCommGrpCat.{u}) :
    IsIso ((Φ i).skyscraperSheafAdjunction.counit.app M) :=
  skyscraperCounit_isIso_of_unique_refinements (Φ i) (closedRationalPoint_unique_refinements i) M

/-- At the geometric cusp origin, the native skyscraper counit is an isomorphism. -/
theorem cuspOrigin_skyscraperCounit_isIso (M : AddCommGrpCat.{u}) :
    IsIso ((Φ (cuspOrigin K)).skyscraperSheafAdjunction.counit.app M) := by
  letI := cuspOrigin_closedImmersion K
  exact closedRationalPoint_skyscraperCounit_isIso (cuspOrigin K) M

end

end ManuscriptAudit.SmallEtaleGeometricBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleGeometricBaseChange.closedRationalPoint_unique_refinements,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.closedRationalPoint_skyscraperCounit_isIso,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.cuspOrigin_skyscraperCounit_isIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
