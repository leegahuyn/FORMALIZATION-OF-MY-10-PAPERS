import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.GaloisTensorSquareScheme

/-!
# Components and face maps of a Galois triple overlap

The triple overlap is the pullback of two copies of the double
overlap over their first projections. The two Galois indices
specify the components containing these two projections.
-/

namespace ManuscriptAudit.GaloisTensorSquare

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

variable (F L : Type u) [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

private abbrev U := Spec (CommRingCat.of L)
private abbrev P := pullback (baseMap F L) (baseMap F L)
private abbrev p₁ : P F L ⟶ U L := pullback.fst (baseMap F L) (baseMap F L)
private abbrev p₂ : P F L ⟶ U L := pullback.snd (baseMap F L) (baseMap F L)

/-- The actual triple overlap with the first coordinate shared by both pairs. -/
abbrev tripleOverlap := pullback (p₁ F L) (p₁ F L)

private def rawComponent (σ τ : L ≃ₐ[F] L) : U L ⟶ tripleOverlap F L :=
  pullback.lift (component F L σ) (component F L τ)
    ((component_fst F L σ).trans (component_fst F L τ).symm)

private theorem rawComponent_jointly_surjective (x : tripleOverlap F L) :
    ∃ (σ τ : L ≃ₐ[F] L) (y : U L), rawComponent F L σ τ y = x := by
  let p := p₁ F L
  obtain ⟨σ, y, hy⟩ := component_jointly_surjective F L (pullback.fst p p x)
  obtain ⟨τ, z, hz⟩ := component_jointly_surjective F L (pullback.snd p p x)
  let i : U L ⟶ U L := 𝟙 _
  have eσ : i ≫ i = component F L σ ≫ p :=
    (Category.id_comp i).trans (component_fst F L σ).symm
  have eτ : i ≫ i = component F L τ ≫ p :=
    (Category.id_comp i).trans (component_fst F L τ).symm
  let m := pullback.map i i p p (component F L σ) (component F L τ) i eσ eτ
  have hR : Set.range m = pullback.fst p p ⁻¹' Set.range (component F L σ) ∩
      pullback.snd p p ⁻¹' Set.range (component F L τ) :=
    Scheme.Pullback.range_map i i p p (component F L σ) (component F L τ) i eσ eτ
  have hx : x ∈ Set.range m := by
    rw [hR]
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  obtain ⟨w, hw⟩ := hx
  let d : U L ⟶ pullback i i := pullback.lift i i rfl
  have hp : pullback.fst i i = pullback.snd i i := by
    simpa only [i, Category.comp_id] using (pullback.condition (f := i) (g := i))
  have hd : pullback.fst i i ≫ d = 𝟙 _ := by
    apply pullback.hom_ext
    · simp [Category.assoc, d, i]
    · simp [Category.assoc, d, i, hp]
  have hm : d ≫ m = rawComponent F L σ τ := by
    have hf : rawComponent F L σ τ ≫ pullback.fst p p = component F L σ :=
      pullback.lift_fst _ _ _
    have hs : rawComponent F L σ τ ≫ pullback.snd p p = component F L τ :=
      pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · calc
        (d ≫ m) ≫ pullback.fst p p = 𝟙 (U L) ≫ component F L σ := by
          simp [Category.assoc, d, m, i]
        _ = component F L σ := Category.id_comp _
        _ = _ := hf.symm
    · calc
        (d ≫ m) ≫ pullback.snd p p = 𝟙 (U L) ≫ component F L τ := by
          simp [Category.assoc, d, m, i]
        _ = component F L τ := Category.id_comp _
        _ = _ := hs.symm
  refine ⟨σ, τ, pullback.fst i i w, ?_⟩
  have hPoint : d (pullback.fst i i w) = w := by
    change (pullback.fst i i ≫ d) w = w
    rw [hd] <;> rfl
  rw [← hm, Scheme.Hom.comp_apply, hPoint, hw]

/-- The component at consecutive indices σ, τ has vertices
id, Spec(σ), and Spec(σ * τ). -/
def tripleComponent (σ τ : L ≃ₐ[F] L) : U L ⟶ tripleOverlap F L :=
  rawComponent F L σ (σ * τ)

@[reassoc] theorem tripleComponent_fst (σ τ : L ≃ₐ[F] L) :
    tripleComponent F L σ τ ≫ pullback.fst (p₁ F L) (p₁ F L) = component F L σ :=
  pullback.lift_fst _ _ _

@[reassoc] theorem tripleComponent_snd (σ τ : L ≃ₐ[F] L) :
    tripleComponent F L σ τ ≫ pullback.snd (p₁ F L) (p₁ F L) = component F L (σ * τ) :=
  pullback.lift_snd _ _ _

/-- The consecutive-index components jointly cover the triple overlap. -/
theorem tripleComponent_jointly_surjective (x : tripleOverlap F L) :
    ∃ (σ τ : L ≃ₐ[F] L) (y : U L), tripleComponent F L σ τ y = x := by
  obtain ⟨σ, τ, y, h⟩ := rawComponent_jointly_surjective F L x
  refine ⟨σ, σ⁻¹ * τ, y, ?_⟩
  simpa [tripleComponent, mul_assoc] using h

/-- The face map retaining the second and third vertices. -/
def face23 : tripleOverlap F L ⟶ P F L :=
  pullback.lift
    (pullback.fst (p₁ F L) (p₁ F L) ≫ p₂ F L)
    (pullback.snd (p₁ F L) (p₁ F L) ≫ p₂ F L) (by
      simp only [Category.assoc]
      rw [← pullback.condition (f := baseMap F L) (g := baseMap F L)]
      rw [← Category.assoc, ← Category.assoc, pullback.condition])

/-- The last face is the τ component precomposed with the
scheme automorphism indexed by σ. -/
theorem tripleComponent_face23 (σ τ : L ≃ₐ[F] L) :
    tripleComponent F L σ τ ≫ face23 F L =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ component F L τ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, face23, pullback.lift_fst, tripleComponent_fst_assoc,
      component_snd, component_fst, Category.comp_id]
  · simp only [Category.assoc, face23, pullback.lift_snd, tripleComponent_snd_assoc, component_snd]
    have he : CommRingCat.ofHom τ.toRingHom ≫ CommRingCat.ofHom σ.toRingHom =
        CommRingCat.ofHom (σ * τ).toRingHom :=
      CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)
    rw [← Spec.map_comp, he]

end

end ManuscriptAudit.GaloisTensorSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisTensorSquare.tripleComponent_fst,
      ``ManuscriptAudit.GaloisTensorSquare.tripleComponent_snd,
      ``ManuscriptAudit.GaloisTensorSquare.tripleComponent_jointly_surjective,
      ``ManuscriptAudit.GaloisTensorSquare.tripleComponent_face23] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
