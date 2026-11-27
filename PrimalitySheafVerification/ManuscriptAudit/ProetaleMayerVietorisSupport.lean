import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtSupportExactness
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisConnecting

/-! An ambient support kernel inherits the overlap classes in the actual
native Mayer–Vietoris connecting map when the quotient vanishes on that overlap. -/

namespace ManuscriptAudit.ProetaleMayerVietorisSupport

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleMayerVietorisSite (coverComplex coverComplex_shortExact)
open ProetaleMayerVietorisConnecting (firstEquiv lastEquiv extBoundary connecting)
open ProetaleOpenLocalLifts (openObject openArrow)
open ProetaleOpenExtAdjunction (integers)
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
  {S : ShortComplex (C X)} (hS : S.ShortExact)
  (hZ : IsZero ((restriction l A).obj S.X₃))

private abbrev P := (coverComplex j k l a b hD hCover).X₁
private abbrev Q := (coverComplex j k l a b hD hCover).X₃

include hZ in
private theorem overlap_ext_subsingleton (n : ℕ) :
    Subsingleton (Ext (P j k l a b hD hCover) S.X₃ n) := by
  letI := ExtSupportExactness.ext_subsingleton_of_isZero
    (integers W) ((restriction l A).obj S.X₃) hZ n
  exact (firstEquiv j k l a b hD hCover S.X₃ n).injective.subsingleton

private def overlapExtEquiv (n : ℕ) :
    Ext (P j k l a b hD hCover) S.X₁ (n + 1) ≃+
      Ext (P j k l a b hD hCover) S.X₂ (n + 1) :=
  ExtSupportExactness.inclusionEquiv hS (P j k l a b hD hCover) n
    (overlap_ext_subsingleton j k l a b hD hCover hZ n)
    (overlap_ext_subsingleton j k l a b hD hCover hZ (n + 1))

/-- The two genuine restrictions have the same positive-degree cohomology on the overlap. -/
def overlapEquiv (n : ℕ) :
    Sheaf.H ((restriction l A).obj S.X₁) (n + 1) ≃+
      Sheaf.H ((restriction l A).obj S.X₂) (n + 1) :=
  (firstEquiv j k l a b hD hCover S.X₁ (n + 1)).symm.trans
    ((overlapExtEquiv j k l a b hD hCover hS hZ n).trans
      (firstEquiv j k l a b hD hCover S.X₂ (n + 1)))

include hS hZ in
set_option maxHeartbeats 1200000 in
/-- An injective ambient connecting arrow stays injective for the support kernel. -/
theorem connecting_injective_of_support (n : ℕ)
    (hinj : Function.Injective (connecting j k l a b hD hCover S.X₂ (n + 1))) :
    Function.Injective (connecting j k l a b hD hCover S.X₁ (n + 1)) := by
  let m := n + 1
  let F := S.X₁
  let G := S.X₂
  let f := overlapExtEquiv j k l a b hD hCover hS hZ n
  let δF := extBoundary j k l a b hD hCover F m
  let δG := extBoundary j k l a b hD hCover G m
  let g := (Ext.mk₀ S.f).postcomp (Q j k l a b hD hCover) (add_zero (m + 1))
  let e := firstEquiv j k l a b hD hCover G m
  let t := lastEquiv j k l a b hD hCover G (m + 1)
  have hg : Function.Injective δG := by
    intro x y hxy
    apply e.injective
    apply hinj
    change t (δG (e.symm (e x))) = t (δG (e.symm (e y)))
    simp only [AddEquiv.symm_apply_apply, hxy]
  have hn (x : Ext (P j k l a b hD hCover) F m) : g (δF x) = δG (f x) :=
    ExtSupportExactness.boundary_naturality (coverComplex_shortExact j k l a b hD hCover) S.f m x
  have hf : Function.Injective δF := by
    intro x y hxy
    apply f.injective
    apply hg
    exact (hn x).symm.trans ((congrArg g hxy).trans (hn y))
  exact (lastEquiv j k l a b hD hCover F (m + 1)).injective.comp
    (hf.comp (firstEquiv j k l a b hD hCover F m).symm.injective)

end
end ManuscriptAudit.ProetaleMayerVietorisSupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleMayerVietorisSupport.overlapEquiv,
      ``ManuscriptAudit.ProetaleMayerVietorisSupport.connecting_injective_of_support] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
