import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The native derived Tor functor sends the actual finite CRT splitting
to the corresponding direct sum, in every homological degree. -/

namespace ManuscriptAudit.Paper7DerivedTorCRT

open CategoryTheory CategoryTheory.Limits Function
open scoped BigOperators

noncomputable section
universe u

variable {R : Type u} [CommRing R] {J : Type u} [Fintype J]
variable (I : J → Ideal R) (hI : Pairwise (IsCoprime on I))

/-- The actual CRT isomorphism is linear for the original ring action. -/
def crtLinear : (R ⧸ ⨅ j, I j) ≃ₗ[R] (∀ j, R ⧸ I j) where
  __ := (Ideal.quotientInfRingEquivPiQuotient I hI).toAddEquiv
  map_smul' r x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    funext j
    change Ideal.Quotient.mk (I j) (r * a) =
      Ideal.Quotient.mk (I j) r * Ideal.Quotient.mk (I j) a
    exact map_mul _ _ _

abbrev component (j : J) : ModuleCat.{u} R := ModuleCat.of R (R ⧸ I j)

def quotientIsoProduct :
    (ModuleCat.of R (R ⧸ ⨅ j, I j) : ModuleCat.{u} R) ≅ ∏ᶜ (component I) :=
  (crtLinear I hI).toModuleIso ≪≫ (ModuleCat.piIsoPi (component I)).symm

/-- This is literally Mathlib's left-derived tensor product, evaluated at
the chosen first module and the native CRT factors in the second entry. -/
def torCRTIso (n : ℕ) (A : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) n).obj A).obj (ModuleCat.of R (R ⧸ ⨅ j, I j)) ≅
      ⨁ fun j ↦ ((Tor (ModuleCat.{u} R) n).obj A).obj (component I j) := by
  let F := (Tor (ModuleCat.{u} R) n).obj A
  letI : F.Additive := by
    change (((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj A).leftDerived n).Additive
    infer_instance
  exact F.mapIso (quotientIsoProduct I hI) ≪≫
    PreservesProduct.iso F (component I) ≪≫ (biproduct.isoProduct (fun j ↦ F.obj (component I j))).symm

end
end ManuscriptAudit.Paper7DerivedTorCRT

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper7DerivedTorCRT.crtLinear,
      ``ManuscriptAudit.Paper7DerivedTorCRT.torCRTIso] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
