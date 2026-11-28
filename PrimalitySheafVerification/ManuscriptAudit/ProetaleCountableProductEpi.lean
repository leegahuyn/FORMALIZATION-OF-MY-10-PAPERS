import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import PrimalitySheafVerification.ManuscriptAudit.AbelianCountableProductShortExact
import PrimalitySheafVerification.ManuscriptAudit.AddCommGrpImageFactorization
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCountableAffineRefinement
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteQuasiCompactCover

/-! Countable products of epimorphisms are epic on the actual native pro-étale site. -/

namespace ManuscriptAudit.ProetaleCountableProductEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AbelianCountableProductShortExact (mapProduct mapProduct_π)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {X : Scheme.{0}}

private abbrev ev (W : X.ProEt) : C X ⥤ A :=
  sheafToPresheaf (Scheme.ProEt.topology X) A ⋙
    (evaluation (X.ProEt)ᵒᵖ A).obj (op W)

private def coordinatesIso (F : ℕ → C X) (W : X.ProEt) :
    (ev W).obj (∏ᶜ F) ≅ AddCommGrpCat.of (∀ n, (F n).obj.obj (op W)) :=
  let G : ℕ → A := fun n => (ev W).obj (F n)
  PreservesProduct.iso (ev W) F ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone G).isLimit

private def coordinates (F : ℕ → C X) (W : X.ProEt) :
    (∏ᶜ F : C X).obj.obj (op W) ≃+ ∀ n, (F n).obj.obj (op W) :=
  (coordinatesIso F W).addCommGroupIsoToAddEquiv

private theorem coordinates_apply (F : ℕ → C X) (W : X.ProEt)
    (x : (∏ᶜ F : C X).obj.obj (op W)) (n : ℕ) :
    coordinates F W x n = (Pi.π F n).hom.app (op W) x := by
  let G : ℕ → A := fun n => (ev W).obj (F n)
  let i := PreservesProduct.iso (ev W) F
  let e := (limit.isLimit _).conePointUniqueUpToIso
    (AddCommGrpCat.HasLimit.productLimitCone G).isLimit
  change e.hom (i.hom x) n = (Pi.π F n).hom.app (op W) x
  have he (z : (∏ᶜ G : A)) : e.hom z n = Pi.π G n z :=
    CategoryTheory.congr_fun (IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) (AddCommGrpCat.HasLimit.productLimitCone G).isLimit (Discrete.mk n)) z
  rw [he]
  have hi : i.hom ≫ Pi.π G n = (ev W).map (Pi.π F n) := by
    change (PreservesProduct.iso (ev W) F).hom ≫ Pi.π G n = _
    rw [PreservesProduct.iso_hom, piComparison_comp_π]
  exact CategoryTheory.congr_fun hi x

private theorem coordinates_restrict (F : ℕ → C X) {W T : X.ProEt} (f : W ⟶ T)
    (x : (∏ᶜ F : C X).obj.obj (op T)) (n : ℕ) :
    coordinates F W ((∏ᶜ F : C X).obj.map f.op x) n =
      (F n).obj.map f.op (coordinates F T x n) := by
  rw [coordinates_apply, coordinates_apply]
  exact NatTrans.naturality_apply (Pi.π F n).hom f.op x

private theorem coordinates_map {I Q : ℕ → C X} (q : ∀ n, I n ⟶ Q n) (W : X.ProEt)
    (z : (∏ᶜ I : C X).obj.obj (op W)) (n : ℕ) :
    coordinates Q W ((mapProduct q).hom.app (op W) z) n =
      (q n).hom.app (op W) (coordinates I W z n) := by
  rw [coordinates_apply, coordinates_apply]
  exact congrArg (fun f : (∏ᶜ I : C X) ⟶ Q n => f.hom.app (op W) z) (mapProduct_π q n)

theorem product_locallySurjective {I Q : ℕ → C X} (q : ∀ n, I n ⟶ Q n)
    (h : ∀ n, Sheaf.IsLocallySurjective (q n)) :
    Sheaf.IsLocallySurjective (mapProduct q) := by
  constructor
  intro T x
  apply ProetaleFiniteQuasiCompactCover.of_affine_pullbacks
  intro V _ a
  rw [Presheaf.pullback_imageSieve]
  let x' := (∏ᶜ Q : C X).obj.map a.op x
  obtain ⟨W, f, _, hCover, hl⟩ := ProetaleCountableAffineRefinement.exists_simultaneous_lift
    I Q q h (coordinates Q V x')
  choose y hy using hl
  let z := (coordinates I W).symm y
  have hz : (mapProduct q).hom.app (op W) z = (∏ᶜ Q : C X).obj.map f.op x' := by
    apply (coordinates Q W).injective
    funext n
    rw [coordinates_map, coordinates_restrict]
    change (q n).hom.app (op W) ((coordinates I W ((coordinates I W).symm y)) n) = _
    rw [AddEquiv.apply_symm_apply, hy]
  refine (Scheme.ProEt.topology X).superset_covering ?_ hCover
  apply (Sieve.generate_le_iff _ _).mpr
  intro V g hg
  cases hg
  exact ⟨z, hz⟩

theorem product_epi {I Q : ℕ → C X} (q : ∀ n, I n ⟶ Q n) (h : ∀ n, Epi (q n)) :
    Epi (mapProduct q) := by
  letI : EssentiallySmall.{1} X.ProEt := inferInstance
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall (Scheme.ProEt.topology X) A
  letI : ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A :=
    AddCommGrpImageFactorization.functorialSurjectiveInjectiveFactorization
  have h' (n : ℕ) : Sheaf.IsLocallySurjective (q n) :=
    (Sheaf.isLocallySurjective_iff_epi' A (q n)).mpr (h n)
  letI : Sheaf.IsLocallySurjective (mapProduct q) := product_locallySurjective q h'
  exact Sheaf.epi_of_isLocallySurjective (mapProduct q)

end
end ManuscriptAudit.ProetaleCountableProductEpi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleCountableProductEpi.product_locallySurjective,
      ``ManuscriptAudit.ProetaleCountableProductEpi.product_epi] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
