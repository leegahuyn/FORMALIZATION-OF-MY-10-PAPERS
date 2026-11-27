import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtSupportExactness
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisConnecting
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtAdjunctionNaturality

/-! Native Mayer–Vietoris commutes with actual changes of coefficient sheaf. -/

namespace ManuscriptAudit.ProetaleMayerVietorisNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleMayerVietorisSite (coverComplex coverComplex_shortExact)
open ProetaleMayerVietorisConnecting (firstEquiv lastEquiv extBoundary connecting)
open ProetaleMayerVietorisRepresentable (openIso terminalIso)
open ProetaleOpenLocalLifts (openObject openArrow)
open ProetaleOpenExtAdjunction (openExtEquiv)
open OpenProetaleExtension (restriction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {U V W X : Scheme.{0}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  (a : openObject l ⟶ openObject j) (b : openObject l ⟶ openObject k)
  (hD : IsPullback a b (openArrow j) (openArrow k))
  (hCover : Set.range j ∪ Set.range k = Set.univ)

private abbrev S := coverComplex j k l a b hD hCover

variable {F G : C X} (g : F ⟶ G) (n : ℕ)

set_option maxHeartbeats 1600000 in
private theorem firstEquiv_naturality (x : Ext (S j k l a b hD hCover).X₁ F n) :
    firstEquiv j k l a b hD hCover G n (x.comp (Ext.mk₀ g) (add_zero n)) =
      Sheaf.H.map ((restriction l A).map g) n (firstEquiv j k l a b hD hCover F n x) := by
  let e := Ext.mk₀ (openIso l).inv
  change openExtEquiv l G n (e.comp (x.comp (Ext.mk₀ g) (add_zero n)) (zero_add n)) =
    Sheaf.H.map ((restriction l A).map g) n (openExtEquiv l F n (e.comp x (zero_add n)))
  rw [← Ext.comp_assoc_of_third_deg_zero]
  exact ProetaleOpenExtAdjunctionNaturality.naturality l g n (e.comp x (zero_add n))

private theorem lastEquiv_naturality (x : Ext (S j k l a b hD hCover).X₃ F n) :
    lastEquiv j k l a b hD hCover G n (x.comp (Ext.mk₀ g) (add_zero n)) =
      Sheaf.H.map g n (lastEquiv j k l a b hD hCover F n x) := by
  let e := Ext.mk₀ (terminalIso X).inv
  change e.comp (x.comp (Ext.mk₀ g) (add_zero n)) (zero_add n) =
    (e.comp x (zero_add n)).comp (Ext.mk₀ g) (add_zero n)
  exact (Ext.comp_assoc_of_third_deg_zero e x (Ext.mk₀ g) (zero_add n)).symm

set_option maxHeartbeats 1800000 in
/-- The genuine connecting arrow commutes with the actual change of coefficients. -/
theorem connecting_naturality (x : Sheaf.H ((restriction l A).obj F) n) :
    connecting j k l a b hD hCover G n (Sheaf.H.map ((restriction l A).map g) n x) =
      Sheaf.H.map g (n + 1) (connecting j k l a b hD hCover F n x) := by
  let e := firstEquiv j k l a b hD hCover F n
  let t := firstEquiv j k l a b hD hCover G n
  let y := e.symm x
  have hy : t.symm (Sheaf.H.map ((restriction l A).map g) n x) =
      y.comp (Ext.mk₀ g) (add_zero n) := by
    apply t.injective
    rw [t.apply_symm_apply]
    change _ = firstEquiv j k l a b hD hCover G n (y.comp (Ext.mk₀ g) (add_zero n))
    rw [firstEquiv_naturality]
    change Sheaf.H.map ((restriction l A).map g) n x =
      Sheaf.H.map ((restriction l A).map g) n (e (e.symm x))
    rw [e.apply_symm_apply]
  let δ₁ := extBoundary j k l a b hD hCover F n
  let δ₂ := extBoundary j k l a b hD hCover G n
  let r := lastEquiv j k l a b hD hCover F (n + 1)
  let s := lastEquiv j k l a b hD hCover G (n + 1)
  change s (δ₂ (t.symm (Sheaf.H.map ((restriction l A).map g) n x))) =
    Sheaf.H.map g (n + 1) (r (δ₁ y))
  rw [hy]
  have hδ : (δ₁ y).comp (Ext.mk₀ g) (add_zero (n + 1)) = δ₂ (y.comp (Ext.mk₀ g) (add_zero n)) :=
    ExtSupportExactness.boundary_naturality (coverComplex_shortExact j k l a b hD hCover) g n y
  rw [← hδ]
  exact lastEquiv_naturality j k l a b hD hCover g (n + 1) (δ₁ y)

end
end ManuscriptAudit.ProetaleMayerVietorisNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleMayerVietorisNaturality.connecting_naturality
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
