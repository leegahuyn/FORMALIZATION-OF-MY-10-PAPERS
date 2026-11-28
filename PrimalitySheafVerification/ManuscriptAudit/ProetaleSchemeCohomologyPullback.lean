import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import PrimalitySheafVerification.ManuscriptAudit.ProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps

/-! Pullback on actual pro-étale cohomology along a scheme morphism. -/

namespace ManuscriptAudit.ProetaleSchemeCohomologyPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open ProetaleBaseChange (directImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private abbrev A := AddCommGrpCat.{u + 1}
private abbrev C (Z : Scheme.{u}) := Sheaf (Scheme.ProEt.topology Z) A.{u}
private abbrev integers := AddCommGrpCat.of (ULift.{u + 1} ℤ)
private abbrev Z (T : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology T) A.{u}).obj integers.{u}

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private def integersIso : (inverseImage f).obj (Z Y) ≅ Z X :=
  (constantInverseImageIso f).app integers.{u}

/-- The cohomology map furnished by the actual exact inverse image. -/
def pullback (F : C Y) (n : ℕ) : Sheaf.H F n →+ Sheaf.H ((inverseImage f).obj F) n :=
  ((Ext.mk₀ (integersIso f).inv).precomp ((inverseImage f).obj F) (zero_add n)).comp
    ((inverseImage f).mapExtAddHom (Z Y) F n)

theorem pullback_naturality {F G : C Y} (a : F ⟶ G) (n : ℕ) (e : Sheaf.H F n) :
    pullback f G n (Sheaf.H.map a n e) =
      Sheaf.H.map ((inverseImage f).map a) n (pullback f F n e) := by
  change (Ext.mk₀ (integersIso f).inv).comp
      ((e.comp (Ext.mk₀ a) (add_zero n)).mapExactFunctor (inverseImage f)) (zero_add n) =
    ((Ext.mk₀ (integersIso f).inv).comp (e.mapExactFunctor (inverseImage f)) (zero_add n)).comp
      (Ext.mk₀ ((inverseImage f).map a)) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc] <;> simp

theorem pullback_boundary {S : ShortComplex (C Y)} (hS : S.ShortExact) (n : ℕ)
    (e : Sheaf.H S.X₃ n) :
    pullback f S.X₁ (n + 1) (e.comp hS.extClass rfl) =
      (pullback f S.X₃ n e).comp (hS.map_of_exact (inverseImage f)).extClass rfl := by
  change (Ext.mk₀ (integersIso f).inv).comp
      ((e.comp hS.extClass rfl).mapExactFunctor (inverseImage f)) (zero_add (n + 1)) =
    ((Ext.mk₀ (integersIso f).inv).comp (e.mapExactFunctor (inverseImage f)) (zero_add n)).comp
      (hS.map_of_exact (inverseImage f)).extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, Ext.comp_assoc] <;> simp

/-- Pullback with a chosen map from the coefficient to the literal direct image. -/
def mapOfDirectImage {F : C Y} {G : C X}
    (a : F ⟶ (directImage f A.{u}).obj G) (n : ℕ) : Sheaf.H F n →+ Sheaf.H G n :=
  (Sheaf.H.map (((adjunction f).homEquiv F G).symm a) n).comp (pullback f F n)

/-- Pullback on the actual finite constant coefficient cohomology. -/
def constant (M : A.{u}) (n : ℕ) :
    Sheaf.H ((constantSheaf (Scheme.ProEt.topology Y) A.{u}).obj M) n →+
      Sheaf.H ((constantSheaf (Scheme.ProEt.topology X) A.{u}).obj M) n :=
  (Sheaf.H.map ((constantInverseImageIso f).app M).hom n).comp
    (pullback f ((constantSheaf (Scheme.ProEt.topology Y) A.{u}).obj M) n)

open ProetaleContinuousDirectImageMaps (functions diagonal) in
/-- Pullback on the actual continuous-coefficient cohomology, including integral adic cohomology. -/
def continuous {U V : Scheme.{0}} (g : U ⟶ V)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] (n : ℕ) :
    Sheaf.H (functions M V) n →+ Sheaf.H (functions M U) n :=
  mapOfDirectImage g (diagonal M g) n

end
end ManuscriptAudit.ProetaleSchemeCohomologyPullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleSchemeCohomologyPullback.pullback_naturality,
      ``ManuscriptAudit.ProetaleSchemeCohomologyPullback.pullback_boundary,
      ``ManuscriptAudit.ProetaleSchemeCohomologyPullback.constant,
      ``ManuscriptAudit.ProetaleSchemeCohomologyPullback.continuous] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
