import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportSequence
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHigherCohomology

/-!
# Higher compact-support comparison for the proper cusp closure

The boundary in the actual short exact sequence is the direct image
from the rational origin and has no positive étale cohomology. Thus
the map from the puncture to the cusp induces an isomorphism in each
degree at least two.
-/

namespace ManuscriptAudit.CuspCompactSupportSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CuspProperCompactification SmallEtaleBaseChange SmallEtaleGeometricBaseChange
open GeometricSkyscraperCohomology

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

variable (K : Type u) [Field K] [IsSepClosed K]

private abbrev origin := cuspOrigin K ≫ affineOpen K
private abbrev point := Scheme.pointSmallEtale (origin K)

/-- The actual closed term of the compact-support sequence is the origin skyscraper. -/
def compactSupportBoundaryIso (M : AddCommGrpCat.{u}) :
    (compactSupportSequence K M).X₃ ≅ (point K).skyscraperSheaf M := by
  change (directImage (origin K) AddCommGrpCat.{u}).obj
    ((constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj M) ≅ _
  exact rationalPointConstantDirectImageIso K (origin K) M

/-- Degree-zero cohomology of the actual closed term is the coefficient group. -/
def compactSupportBoundaryHZeroEquiv (M : AddCommGrpCat.{u}) :
    Sheaf.H (compactSupportSequence K M).X₃ 0 ≃+ M :=
  (((Sheaf.functorH (projectiveCusp K).smallEtaleTopology 0).mapIso
    (compactSupportBoundaryIso K M)).addCommGroupIsoToAddEquiv).trans
      (geometricSkyscraperHZeroEquiv (point K) M)

/-- The actual closed term of the compact-support sequence is acyclic in positive degrees. -/
theorem compactSupportBoundaryH_succ_subsingleton (M : AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H (compactSupportSequence K M).X₃ (n + 1)) := by
  let e : Sheaf.H (compactSupportSequence K M).X₃ (n + 1) ≃+
      Sheaf.H ((point K).skyscraperSheaf M) (n + 1) :=
    ((Sheaf.functorH (projectiveCusp K).smallEtaleTopology (n + 1)).mapIso
      (compactSupportBoundaryIso K M)).addCommGroupIsoToAddEquiv
  have h := geometricSkyscraperH_succ_subsingleton (point K) M n
  exact ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩

/-- The native compact-support map is bijective in every degree at least two. -/
theorem compactSupportHigherMap_bijective (M : AddCommGrpCat.{u}) (n : ℕ) :
    Function.Bijective (Sheaf.H.map (compactSupportSequence K M).f (n + 2)) := by
  let S := compactSupportSequence K M
  let hS := (compactSupportSequence_shortExact K M).2
  let Z := (constantSheaf (projectiveCusp K).smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let h₁ := compactSupportBoundaryH_succ_subsingleton K M n
  let h₂ := compactSupportBoundaryH_succ_subsingleton K M (n + 1)
  constructor
  · intro x y hxy
    have hxy₀ : (Sheaf.H.map S.f (n + 2)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hz : (x - y).comp (Ext.mk₀ S.f) (add_zero (n + 2)) = 0 := hxy₀
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₁ (X := Z) hS (x - y) hz
      (show (n + 1) + 1 = n + 2 by rfl)
    have ht₀ : t = 0 := h₁.allEq _ _
    apply sub_eq_zero.mp
    rw [← ht, ht₀, Ext.zero_comp]
  · intro y
    have hy : y.comp (Ext.mk₀ S.g) (add_zero (n + 2)) = 0 := h₂.allEq _ _
    exact Ext.covariant_sequence_exact₂ (X := Z) hS y hy

/-- The native map identifies compactly supported groups in degree `n + 2`. -/
def compactSupportHigherEquiv (M : AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H (compactSupportSequence K M).X₁ (n + 2) ≃+
      Sheaf.H (compactSupportSequence K M).X₂ (n + 2) :=
  AddEquiv.ofBijective (Sheaf.H.map (compactSupportSequence K M).f (n + 2))
    (compactSupportHigherMap_bijective K M n)

end

end ManuscriptAudit.CuspCompactSupportSequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspCompactSupportSequence.compactSupportBoundaryIso,
      ``ManuscriptAudit.CuspCompactSupportSequence.compactSupportBoundaryHZeroEquiv,
      ``ManuscriptAudit.CuspCompactSupportSequence.compactSupportBoundaryH_succ_subsingleton,
      ``ManuscriptAudit.CuspCompactSupportSequence.compactSupportHigherMap_bijective,
      ``ManuscriptAudit.CuspCompactSupportSequence.compactSupportHigherEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

