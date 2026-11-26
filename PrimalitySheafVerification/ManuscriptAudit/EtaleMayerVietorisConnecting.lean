import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisOrdinary

/-!
# The connecting map of the ordinary two-open étale sequence

Vanishing of cohomology on both covering opens makes the native
connecting map injective. Vanishing on both opens in the next degree
makes the same map surjective.
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

private theorem biprod_subsingleton {A B : C.{u}} (hA : Subsingleton A) (hB : Subsingleton B) :
    Subsingleton (A ⊞ B : C.{u}) := by
  let e := (AddCommGrpCat.biprodIsoProd A B).addCommGroupIsoToAddEquiv
  exact ⟨fun x y => e.injective (Prod.ext (hA.allEq _ _) (hB.allEq _ _))⟩

private theorem connectorInjective (S : ComposableArrows C.{u} 5) (hS : S.Exact)
    (hZero : Subsingleton (S.obj' 1)) : Function.Injective (S.map' 2 3) := by
  intro x y hxy
  change (S.map' 2 3).hom x = (S.map' 2 3).hom y at hxy
  have hxy₀ : (S.map' 2 3).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h := hS.exact' 1 2 3
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  obtain ⟨z, hz⟩ := (h (x - y)).mp hxy₀
  change (S.map' 1 2).hom z = x - y at hz
  rw [hZero.allEq z 0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

private theorem connectorSurjective (S : ComposableArrows C.{u} 5) (hS : S.Exact)
    (hZero : Subsingleton (S.obj' 4)) : Function.Surjective (S.map' 2 3) := by
  intro x
  have hx : (S.map' 3 4).hom x = 0 := hZero.allEq _ _
  have h := hS.exact' 2 3 4
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact (h x).mp hx

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
/-- The actual connecting arrow, expressed on ordinary overlap and ambient cohomology. -/
def ordinaryConnecting :
    restrictedH l F n →+ Sheaf.H F (n + 1) :=
  ((ordinaryOpenCoverSequence j k l a b hD hCover F n).map' 2 3).hom

/-- The native connecting arrow is injective when both chart groups vanish. -/
theorem ordinaryConnecting_injective
    (hU : Subsingleton (restrictedH j F n)) (hV : Subsingleton (restrictedH k F n)) :
    Function.Injective (ordinaryConnecting j k l a b hD hCover F n) := by
  let Q := ordinaryOpenCoverSequence j k l a b hD hCover F n
  have h : Subsingleton (Q.obj' 1) := biprod_subsingleton
    (A := AddCommGrpCat.of (restrictedH j F n))
    (B := AddCommGrpCat.of (restrictedH k F n)) hU hV
  exact connectorInjective Q (ordinaryOpenCoverSequence_exact j k l a b hD hCover F n) h

/-- The native connecting arrow is bijective if the chart groups vanish
in both consecutive degrees. -/
theorem ordinaryConnecting_bijective
    (hU : Subsingleton (restrictedH j F n)) (hV : Subsingleton (restrictedH k F n))
    (hU' : Subsingleton (restrictedH j F (n + 1))) (hV' : Subsingleton (restrictedH k F (n + 1))) :
    Function.Bijective (ordinaryConnecting j k l a b hD hCover F n) := by
  let Q := ordinaryOpenCoverSequence j k l a b hD hCover F n
  have h : Subsingleton (Q.obj' 4) := biprod_subsingleton
    (A := AddCommGrpCat.of (restrictedH j F (n + 1)))
    (B := AddCommGrpCat.of (restrictedH k F (n + 1))) hU' hV'
  exact ⟨ordinaryConnecting_injective j k l a b hD hCover F n hU hV,
    connectorSurjective Q (ordinaryOpenCoverSequence_exact j k l a b hD hCover F n) h⟩

end

end ManuscriptAudit.EtaleMayerVietoris

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleMayerVietoris.ordinaryConnecting_injective,
      ``ManuscriptAudit.EtaleMayerVietoris.ordinaryConnecting_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
