import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenKernelHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisNaturality

/-! The native Mayer–Vietoris connecting class for a support kernel and
the ambient coefficient agree after forgetting support when the overlap
misses the boundary. -/

namespace ManuscriptAudit.ProetaleSupportMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open OpenProetaleExtension (restriction abelianExtensionByZeroAdjunction)
open ProetaleOpenLocalLifts (openObject openArrow)
open ProetaleOpenKernelHOne (restrictionKernelIso)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleMayerVietorisConnecting (connecting)
open ProetaleMayerVietorisNaturality (connecting_naturality)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {X W : Scheme.{0}} (l : W ⟶ X) [IsOpenImmersion l]
variable {F G : C X} (g : F ⟶ G)

/-- On the complement of the boundary, the restriction of the kernel isomorphism
is the actual restriction of the kernel inclusion. -/
theorem restrictionKernelIso_hom (hZero : IsZero ((restriction l A).obj G)) :
    (restrictionKernelIso l g hZero).hom = (restriction l A).map (kernel.ι g) := by
  let R := restriction l A
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction l).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  change (PreservesKernel.iso R g).hom ≫ kernel.ι (R.map g) = R.map (kernel.ι g)
  rw [← PreservesKernel.iso_inv_ι R g, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

variable {U V : Scheme.{0}} (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k]
  (a : openObject l ⟶ openObject j) (b : openObject l ⟶ openObject k)
  (hD : IsPullback a b (openArrow j) (openArrow k))
  (hCover : Set.range j ∪ Set.range k = Set.univ)

/-- The actual connecting class in all degrees is compatible with forgetting support. -/
theorem connecting_ambient (hZero : IsZero ((restriction l A).obj G))
    (n : ℕ) (x : Sheaf.H ((restriction l A).obj F) n) :
    Sheaf.H.map (kernel.ι g) (n + 1)
      (connecting j k l a b hD hCover (kernel g) n
        ((cohomologyIso (X := W) (restrictionKernelIso l g hZero) n).symm x)) =
      connecting j k l a b hD hCover F n x := by
  let e := cohomologyIso (X := W) (restrictionKernelIso l g hZero) n
  have he : Sheaf.H.map ((restriction l A).map (kernel.ι g)) n (e.symm x) = x := by
    rw [← restrictionKernelIso_hom l g hZero]
    exact e.apply_symm_apply x
  have h := connecting_naturality j k l a b hD hCover (kernel.ι g) n (e.symm x)
  rw [he] at h
  exact h.symm

end
end ManuscriptAudit.ProetaleSupportMayerVietoris

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleSupportMayerVietoris.restrictionKernelIso_hom,
      ``ManuscriptAudit.ProetaleSupportMayerVietoris.connecting_ambient] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
