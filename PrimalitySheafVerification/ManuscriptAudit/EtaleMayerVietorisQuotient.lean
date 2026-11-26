import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisConnecting

/-!
# The ordinary Mayer–Vietoris quotient

The cokernel of the native connecting homomorphism is the actual
subgroup of possible chart restrictions whose overlap difference is zero.
-/

namespace ManuscriptAudit.EtaleMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComposableArrows
open EtaleTwoOpenHOne OpenEtaleExtension

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev C := AddCommGrpCat.{u}

private def quotientEquivKer (S : ComposableArrows C.{u} 5) (hS : S.Exact) :
    ((S.obj' 3 : Type u) ⧸ (S.map' 2 3).hom.range) ≃+ (S.map' 4 5).hom.ker := by
  have h₂ : (S.map' 2 3).hom.range = (S.map' 3 4).hom.ker :=
    (hS.exact' 2 3 4).ab_range_eq_ker
  have h₃ : (S.map' 3 4).hom.range = (S.map' 4 5).hom.ker :=
    (hS.exact' 3 4 5).ab_range_eq_ker
  rw [h₂, ← h₃]
  exact QuotientAddGroup.quotientKerEquivRange (S.map' 3 4).hom

variable {U V W X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
variable (a : Scheme.Etale.mk l ⟶ Scheme.Etale.mk j)
variable (b : Scheme.Etale.mk l ⟶ Scheme.Etale.mk k)
variable (hD : IsPullback a b (openArrow j) (openArrow k))
variable (hCover : Set.range j ∪ Set.range k = Set.univ)
variable (F : Sheaf X.smallEtaleTopology C.{u}) (n : ℕ)

private abbrev restrictedH {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (F : Sheaf X.smallEtaleTopology C.{u}) (n : ℕ) :=
  Sheaf.H ((restriction f C.{u}).obj F) n

include a b hD hCover in
/-- The ordinary chart-to-overlap difference in the higher degree of the segment. -/
def ordinaryNextRestrictionDifference :
    ((AddCommGrpCat.of (restrictedH j F (n + 1)) ⊞
      AddCommGrpCat.of (restrictedH k F (n + 1))) : C.{u}) →+ restrictedH l F (n + 1) :=
  ((ordinaryOpenCoverSequence j k l a b hD hCover F n).map' 4 5).hom

/-- The ordinary quotient by the connecting map is exactly the kernel of
the next chart-to-overlap difference, for the same native segment. -/
def ordinaryConnectingQuotientEquiv :
    (Sheaf.H F (n + 1) ⧸ (ordinaryConnecting j k l a b hD hCover F n).range) ≃+
      (ordinaryNextRestrictionDifference j k l a b hD hCover F n).ker :=
  quotientEquivKer (ordinaryOpenCoverSequence j k l a b hD hCover F n)
    (ordinaryOpenCoverSequence_exact j k l a b hD hCover F n)

end

end ManuscriptAudit.EtaleMayerVietoris

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.EtaleMayerVietoris.ordinaryConnectingQuotientEquiv
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
