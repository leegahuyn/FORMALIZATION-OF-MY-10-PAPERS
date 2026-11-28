import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineStageTensorCoproduct

/-! Explicitness about the two tensor-square arrows when passing
between the actual affine algebra and its categorical coproduct. -/

namespace ManuscriptAudit.AffineStageTensorLegs

open CategoryTheory CategoryTheory.Limits
open AffineStageTensorCoproduct (tensorCofan tensorIsColimit tensorIso)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

private abbrev base := CommRingCat.of R
private abbrev U (S : Type u) [CommRing S] [Algebra R S] := CommRingCat.mkUnder (base (R := R)) S

/-- Read a genuine under-ring morphism as a homomorphism for the
given algebra structures, without reconstructing the structures. -/
def algebraHom (f : U (R := R) S ⟶ U (R := R) T) : S →ₐ[R] T :=
  { toRingHom := f.right.hom
    commutes' := fun r ↦
      congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of T ↦ g r) (Under.w f) }

@[simp]
theorem algebraHom_apply (f : U (R := R) S ⟶ U (R := R) T) (x : S) :
    algebraHom f x = f.right x := rfl

@[simp]
theorem algebraHom_toUnder (f : S →ₐ[R] T) : algebraHom f.toUnder = f := by
  apply AlgHom.ext
  intro x
  rfl

variable [HasBinaryCoproduct (U (R := R) S) (U (R := R) T)]

/-- The ring's left inclusion identifies with the actual coproduct leg. -/
theorem inl_tensorIso_hom :
    (tensorCofan (R := base (R := R)) S T).inl ≫ (tensorIso (R := base (R := R)) S T).hom =
      coprod.inl := by
  change (tensorCofan (R := base (R := R)) S T).ι.app ⟨WalkingPair.left⟩ ≫
    (tensorIso (R := base (R := R)) S T).hom = _
  exact (tensorIsColimit (R := base (R := R)) S T).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) ⟨WalkingPair.left⟩

/-- The ring's right inclusion identifies with the actual coproduct leg. -/
theorem inr_tensorIso_hom :
    (tensorCofan (R := base (R := R)) S T).inr ≫ (tensorIso (R := base (R := R)) S T).hom =
      coprod.inr := by
  change (tensorCofan (R := base (R := R)) S T).ι.app ⟨WalkingPair.right⟩ ≫
    (tensorIso (R := base (R := R)) S T).hom = _
  exact (tensorIsColimit (R := base (R := R)) S T).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) ⟨WalkingPair.right⟩

end
end ManuscriptAudit.AffineStageTensorLegs

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineStageTensorLegs.inl_tensorIso_hom,
      ``ManuscriptAudit.AffineStageTensorLegs.inr_tensorIso_hom] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
