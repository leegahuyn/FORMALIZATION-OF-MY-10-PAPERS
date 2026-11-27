import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisRepresentable

/-! The native Mayer–Vietoris connecting arrow from ordinary cohomology on
the actual overlap to ordinary cohomology on the ambient scheme. -/

namespace ManuscriptAudit.ProetaleMayerVietorisConnecting

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleMayerVietorisSite (coverComplex coverComplex_shortExact sheafEquivalence)
open ProetaleMayerVietorisRepresentable (nativeFree terminalIso openIso)
open ProetaleOpenLocalLifts (openObject openArrow)
open OpenProetaleExtension (restriction extensionByZero)
open ProetaleOpenExtAdjunction (openExtEquiv integers)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

private def extIso {X : Scheme.{0}} {P Q : C X} (e : P ≅ Q) (F : C X) (n : ℕ) :
    Ext P F n ≃+ Ext Q F n :=
  { toFun := (Ext.mk₀ e.inv).precomp F (zero_add n)
    invFun := (Ext.mk₀ e.hom).precomp F (zero_add n)
    left_inv := fun a ↦ by
      change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp a (zero_add n)) (zero_add n) = a
      rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
    right_inv := fun a ↦ by
      change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp a (zero_add n)) (zero_add n) = a
      rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
    map_add' := fun a b ↦ map_add ((Ext.mk₀ e.inv).precomp F (zero_add n)) a b }

variable {U V W X : Scheme.{0}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  (a : openObject l ⟶ openObject j) (b : openObject l ⟶ openObject k)
  (hD : IsPullback a b (openArrow j) (openArrow k))
  (hCover : Set.range j ∪ Set.range k = Set.univ)

private abbrev S := coverComplex j k l a b hD hCover

private abbrev exactCover := coverComplex_shortExact j k l a b hD hCover

private def firstIso : (S j k l a b hD hCover).X₁ ≅
    (extensionByZero l A).obj (integers W) :=
  openIso l

private def lastIso : (S j k l a b hD hCover).X₃ ≅ integers X :=
  terminalIso X

private def middleIso : (S j k l a b hD hCover).X₂ ≅
    (extensionByZero j A).obj (integers U) ⊞ (extensionByZero k A).obj (integers V) := by
  let H := (sheafEquivalence X).inverse
  letI : H.Additive := H.additive_of_preserves_binary_products
  exact (mapBiprod H _ _) ≪≫ biprod.mapIso (openIso j) (openIso k)

variable (F : C X) (n : ℕ)

private abbrev firstEquiv :=
  (extIso (firstIso j k l a b hD hCover) F n).trans (openExtEquiv l F n)

private abbrev lastEquiv (r : ℕ) :=
  extIso (lastIso j k l a b hD hCover) F r

private abbrev δ :
    Ext (S j k l a b hD hCover).X₁ F n →+ Ext (S j k l a b hD hCover).X₃ F (n + 1) :=
  (exactCover j k l a b hD hCover).extClass.precomp F (Nat.add_comm 1 n)

/-- The actual connecting arrow, expressed on ordinary native pro-étale cohomology. -/
def connecting :
    Sheaf.H ((restriction l A).obj F) n →+ Sheaf.H F (n + 1) :=
  (lastEquiv j k l a b hD hCover F (n + 1)).toAddMonoidHom.comp
    ((δ j k l a b hD hCover F n).comp
      (firstEquiv j k l a b hD hCover F n).symm.toAddMonoidHom)

private theorem middle_subsingleton
    (hU : Subsingleton (Sheaf.H ((restriction j A).obj F) n))
    (hV : Subsingleton (Sheaf.H ((restriction k A).obj F) n)) :
    Subsingleton (Ext (S j k l a b hD hCover).X₂ F n) := by
  letI := hU
  letI := hV
  letI := (openExtEquiv j F n).injective.subsingleton
  letI := (openExtEquiv k F n).injective.subsingleton
  let e := (extIso (middleIso j k l a b hD hCover) F n).trans Ext.biprodAddEquiv
  exact e.injective.subsingleton

/-- Vanishing on the two charts in degree n makes the actual connecting arrow injective. -/
theorem connecting_injective
    (hU : Subsingleton (Sheaf.H ((restriction j A).obj F) n))
    (hV : Subsingleton (Sheaf.H ((restriction k A).obj F) n)) :
    Function.Injective (connecting j k l a b hD hCover F n) := by
  let f := δ j k l a b hD hCover F n
  have hinj : Function.Injective f := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz'⟩ := Ext.contravariant_sequence_exact₁
      (exactCover j k l a b hD hCover) F (x - y) (Nat.add_comm 1 n) hz
    have h : z = 0 := (middle_subsingleton j k l a b hD hCover F n hU hV).elim _ _
    rw [h, Ext.comp_zero] at hz'
    exact hz'.symm
  exact (lastEquiv j k l a b hD hCover F (n + 1)).injective.comp
    (hinj.comp (firstEquiv j k l a b hD hCover F n).symm.injective)

/-- Vanishing on the charts in degree n + 1 makes the same arrow surjective. -/
theorem connecting_surjective
    (hU : Subsingleton (Sheaf.H ((restriction j A).obj F) (n + 1)))
    (hV : Subsingleton (Sheaf.H ((restriction k A).obj F) (n + 1))) :
    Function.Surjective (connecting j k l a b hD hCover F n) := by
  let E := middle_subsingleton j k l a b hD hCover F (n + 1) hU hV
  have hd : Function.Surjective (δ j k l a b hD hCover F n) := by
    intro y
    exact Ext.contravariant_sequence_exact₃ (exactCover j k l a b hD hCover) F y
      (E.elim _ _) (Nat.add_comm 1 n)
  exact (lastEquiv j k l a b hD hCover F (n + 1)).surjective.comp
    (hd.comp (firstEquiv j k l a b hD hCover F n).symm.surjective)

end
end ManuscriptAudit.ProetaleMayerVietorisConnecting

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleMayerVietorisConnecting.connecting,
      ``ManuscriptAudit.ProetaleMayerVietorisConnecting.connecting_injective,
      ``ManuscriptAudit.ProetaleMayerVietorisConnecting.connecting_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
