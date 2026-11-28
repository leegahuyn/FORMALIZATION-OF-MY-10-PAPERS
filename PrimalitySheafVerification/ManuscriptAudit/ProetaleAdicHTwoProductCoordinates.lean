import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtTwoCountableProductDetection
import PrimalitySheafVerification.ManuscriptAudit.ExtTwoCountableProductSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCountableProductEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicHOneDetection
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! The literal countable residue product gives every tuple of classes in
actual degree-two native pro-étale cohomology. -/

namespace ManuscriptAudit.ProetaleAdicHTwoProductCoordinates

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleAdicNativeExactSequence (sequence)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueSheaf)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev C := Sheaf (Scheme.ProEt.topology X) A
private abbrev Q := sequence X ℓ
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

abbrev projection (n : ℕ) : (Q X ℓ).X₂ ⟶ finiteCoefficient X ℓ n :=
  (lift X).map (Pi.π (residueSheaf X ℓ) n)

def coordinates : Sheaf.H (Q X ℓ).X₂ 2 →+ ∀ n, Sheaf.H (finiteCoefficient X ℓ n) 2 where
  toFun z n := Sheaf.H.map (projection X ℓ n) 2 z
  map_zero' := funext (fun n => map_zero (Sheaf.H.map (projection X ℓ n) 2))
  map_add' x y := funext (fun n => map_add (Sheaf.H.map (projection X ℓ n) 2) x y)

private def productIso : (Q X ℓ).X₂ ≅ ∏ᶜ (finiteCoefficient X ℓ) :=
  PreservesProduct.iso (lift X) (residueSheaf X ℓ)

private theorem productIso_hom_π (n : ℕ) :
    (productIso X ℓ).hom ≫ Pi.π (finiteCoefficient X ℓ) n = projection X ℓ n := by
  rw [productIso, PreservesProduct.iso_hom, piComparison_comp_π]

private theorem coordinates_apply (z : Sheaf.H (Q X ℓ).X₂ 2) (n : ℕ) :
    coordinates X ℓ z n =
      Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 2
        ((cohomologyIso (X := X) (productIso X ℓ) 2) z) := by
  change Sheaf.H.map (projection X ℓ n) 2 z =
    Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 2 (Sheaf.H.map (productIso X ℓ).hom 2 z)
  rw [← Sheaf.H.map_comp_apply, productIso_hom_π]

/-- The actual componentwise cohomology map is bijective. -/
theorem coordinates_bijective : Function.Bijective (coordinates X ℓ) := by
  letI : EssentiallySmall.{1} X.ProEt := inferInstance
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall (Scheme.ProEt.topology X) A
  let E := cohomologyIso (X := X) (productIso X ℓ) 2
  have hEpi (F G : ℕ → C X) (f : ∀ n, F n ⟶ G n) (h : ∀ n, Epi (f n)) :
      Epi (AbelianCountableProductShortExact.mapProduct f) :=
    ProetaleCountableProductEpi.product_epi f h
  have hi := ExtTwoCountableProductDetection.projections_jointly_injective hEpi
    (finiteCoefficient X ℓ) (integers X)
  have hj := ExtTwoCountableProductSurjectivity.projections_jointly_surjective hEpi
    (finiteCoefficient X ℓ) (integers X)
  constructor
  · intro z w h
    apply E.injective
    apply hi
    funext n
    change Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 2 (E z) =
      Sheaf.H.map (Pi.π (finiteCoefficient X ℓ) n) 2 (E w)
    rw [← coordinates_apply X ℓ z n, ← coordinates_apply X ℓ w n]
    exact congrFun h n
  · intro v
    obtain ⟨z, hz⟩ := hj v
    refine ⟨E.symm z, funext fun n => ?_⟩
    rw [coordinates_apply, show (cohomologyIso (X := X) (productIso X ℓ) 2) (E.symm z) = z
      from E.apply_symm_apply z]
    exact congrFun hz n

def coordinateEquiv : Sheaf.H (Q X ℓ).X₂ 2 ≃+ ∀ n, Sheaf.H (finiteCoefficient X ℓ n) 2 :=
  AddEquiv.ofBijective (coordinates X ℓ) (coordinates_bijective X ℓ)

end
end ManuscriptAudit.ProetaleAdicHTwoProductCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicHTwoProductCoordinates.coordinates_bijective,
      ``ManuscriptAudit.ProetaleAdicHTwoProductCoordinates.coordinateEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
