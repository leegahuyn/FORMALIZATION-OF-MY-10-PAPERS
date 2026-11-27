import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleGaloisPoints
import PrimalitySheafVerification.ManuscriptAudit.GaloisTripleOverlap

/-!
# A Galois cover and its overlaps in the small étale site

Each object is the actual scheme over the base spectrum. The
component and face arrows are the scheme arrows over that base.
-/

namespace ManuscriptAudit.GaloisTensorSquare

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (F L : Type) [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

private abbrev X := Spec (CommRingCat.of F)
private abbrev U := Spec (CommRingCat.of L)
private abbrev f := baseMap F L
private abbrev P := pullback (f F L) (f F L)
private abbrev p₁ : P F L ⟶ U L := pullback.fst (f F L) (f F L)
private abbrev p₂ : P F L ⟶ U L := pullback.snd (f F L) (f F L)
private abbrev q₁ : tripleOverlap F L ⟶ P F L := pullback.fst (p₁ F L) (p₁ F L)
private abbrev q₂ : tripleOverlap F L ⟶ P F L := pullback.snd (p₁ F L) (p₁ F L)

private theorem etale_baseMap : Etale (f F L) :=
  FieldEtaleGaloisPoints.finiteGalois_spec_map_etale F L

/-- The actual finite Galois cover as an object of the small étale site. -/
def fieldObject : (X F).Etale := by
  letI := etale_baseMap F L
  exact Scheme.Etale.mk (f F L)

/-- The actual double overlap as an object of the small étale site. -/
def pairObject : (X F).Etale := by
  letI := etale_baseMap F L
  exact Scheme.Etale.mk (p₁ F L ≫ f F L)

/-- The actual triple overlap as an object of the small étale site. -/
def tripleObject : (X F).Etale := by
  letI := etale_baseMap F L
  exact Scheme.Etale.mk (q₁ F L ≫ p₁ F L ≫ f F L)

/-- The first projection from the double overlap to the cover. -/
def pairFirst : pairObject F L ⟶ fieldObject F L :=
  MorphismProperty.Over.homMk (p₁ F L) rfl

/-- The second projection from the double overlap to the cover. -/
def pairSecond : pairObject F L ⟶ fieldObject F L :=
  MorphismProperty.Over.homMk (p₂ F L) pullback.condition.symm

/-- The face retaining the first two vertices. -/
def tripleFirstPair : tripleObject F L ⟶ pairObject F L :=
  MorphismProperty.Over.homMk (q₁ F L) rfl

/-- The face retaining the first and third vertices. -/
def tripleSecondPair : tripleObject F L ⟶ pairObject F L :=
  MorphismProperty.Over.homMk (q₂ F L) (by
    change q₂ F L ≫ p₁ F L ≫ f F L = q₁ F L ≫ p₁ F L ≫ f F L
    simpa only [Category.assoc] using (congrArg (fun a ↦ a ≫ f F L)
      (pullback.condition (f := p₁ F L) (g := p₁ F L))).symm)

/-- The face retaining the second and third vertices. -/
def tripleThirdPair : tripleObject F L ⟶ pairObject F L :=
  MorphismProperty.Over.homMk (face23 F L) (by
    change face23 F L ≫ p₁ F L ≫ f F L = q₁ F L ≫ p₁ F L ≫ f F L
    have hf : face23 F L ≫ p₁ F L = q₁ F L ≫ p₂ F L := pullback.lift_fst _ _ _
    rw [← Category.assoc, hf, Category.assoc, ← pullback.condition])

/-- The cover automorphism induced by a Galois automorphism. -/
def fieldAutomorphism (σ : L ≃ₐ[F] L) : fieldObject F L ⟶ fieldObject F L :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f F L = f F L
    have he : CommRingCat.ofHom (algebraMap F L) ≫ CommRingCat.ofHom σ.toRingHom =
        CommRingCat.ofHom (algebraMap F L) :=
      CommRingCat.hom_ext (RingHom.ext σ.commutes)
    rw [baseMap, ← Spec.map_comp, he])

@[simp] theorem fieldAutomorphism_one :
    fieldAutomorphism F L (1 : L ≃ₐ[F] L) = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (1 : L ≃ₐ[F] L).toRingHom) = 𝟙 (U L)
  have he : CommRingCat.ofHom (1 : L ≃ₐ[F] L).toRingHom = 𝟙 (CommRingCat.of L) :=
    CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)
  rw [he, Spec.map_id]

theorem fieldAutomorphism_mul (σ τ : L ≃ₐ[F] L) :
    fieldAutomorphism F L (σ * τ) = fieldAutomorphism F L σ ≫ fieldAutomorphism F L τ := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (σ * τ).toRingHom) =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
  have he : CommRingCat.ofHom τ.toRingHom ≫ CommRingCat.ofHom σ.toRingHom =
      CommRingCat.ofHom (σ * τ).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)
  rw [← Spec.map_comp, he]

/-- The double-overlap component arrow in the small étale site. -/
def pairComponentArrow (σ : L ≃ₐ[F] L) : fieldObject F L ⟶ pairObject F L :=
  MorphismProperty.Over.homMk (component F L σ) (by
    change component F L σ ≫ p₁ F L ≫ f F L = f F L
    rw [← Category.assoc, component_fst]
    exact Category.id_comp _)

/-- The triple-overlap component arrow in the small étale site. -/
def tripleComponentArrow (σ τ : L ≃ₐ[F] L) : fieldObject F L ⟶ tripleObject F L :=
  MorphismProperty.Over.homMk (tripleComponent F L σ τ) (by
    change tripleComponent F L σ τ ≫ q₁ F L ≫ p₁ F L ≫ f F L = f F L
    rw [tripleComponent_fst_assoc, component_fst_assoc]
    exact Category.id_comp _)

@[reassoc] theorem pairComponentArrow_first (σ : L ≃ₐ[F] L) :
    pairComponentArrow F L σ ≫ pairFirst F L = 𝟙 _ :=
  MorphismProperty.Over.Hom.ext (component_fst F L σ)

@[reassoc] theorem pairComponentArrow_second (σ : L ≃ₐ[F] L) :
    pairComponentArrow F L σ ≫ pairSecond F L = fieldAutomorphism F L σ :=
  MorphismProperty.Over.Hom.ext (component_snd F L σ)

@[reassoc] theorem tripleComponentArrow_firstPair (σ τ : L ≃ₐ[F] L) :
    tripleComponentArrow F L σ τ ≫ tripleFirstPair F L = pairComponentArrow F L σ :=
  MorphismProperty.Over.Hom.ext (tripleComponent_fst F L σ τ)

@[reassoc] theorem tripleComponentArrow_secondPair (σ τ : L ≃ₐ[F] L) :
    tripleComponentArrow F L σ τ ≫ tripleSecondPair F L = pairComponentArrow F L (σ * τ) :=
  MorphismProperty.Over.Hom.ext (tripleComponent_snd F L σ τ)

@[reassoc] theorem tripleComponentArrow_thirdPair (σ τ : L ≃ₐ[F] L) :
    tripleComponentArrow F L σ τ ≫ tripleThirdPair F L =
      fieldAutomorphism F L σ ≫ pairComponentArrow F L τ :=
  MorphismProperty.Over.Hom.ext (tripleComponent_face23 F L σ τ)

end

end ManuscriptAudit.GaloisTensorSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisTensorSquare.fieldAutomorphism_one,
      ``ManuscriptAudit.GaloisTensorSquare.fieldAutomorphism_mul,
      ``ManuscriptAudit.GaloisTensorSquare.pairComponentArrow_first,
      ``ManuscriptAudit.GaloisTensorSquare.pairComponentArrow_second,
      ``ManuscriptAudit.GaloisTensorSquare.tripleComponentArrow_firstPair,
      ``ManuscriptAudit.GaloisTensorSquare.tripleComponentArrow_secondPair,
      ``ManuscriptAudit.GaloisTensorSquare.tripleComponentArrow_thirdPair] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
