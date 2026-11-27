import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleMayerVietorisComplex
import PrimalitySheafVerification.ManuscriptAudit.ExtContravariantBoundaryMap

/-! The two actual Mayer–Vietoris connecting maps commute with change of sites. -/

namespace ManuscriptAudit.EtaleProetaleMayerVietorisBoundary

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleTwoOpenHOne (openArrow)
open EtaleProetaleInverseImage (inverseImage)
open EtaleProetaleMayerVietorisComplex (proComplex comparison)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev E (X : Scheme.{0}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{1}

local instance etaleHasExt (X : Scheme.{0}) : HasExt.{1} (E X) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology AddCommGrpCat.{1}
  exact IsGrothendieckAbelian.hasExt _

local instance inverseImageAdditive (X : Scheme.{0}) : (inverseImage X).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage X)

variable {U V W X : Scheme.{0}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  (a : Scheme.Etale.mk l ⟶ Scheme.Etale.mk j)
  (b : Scheme.Etale.mk l ⟶ Scheme.Etale.mk k)
  (hD : IsPullback a b (openArrow j) (openArrow k))
  (hCover : Set.range j ∪ Set.range k = Set.univ)

private abbrev S := EtaleMayerVietorisHigh.coverComplex j k l a b hD hCover
private abbrev T := proComplex j k l a b hD hCover

private theorem pro_shortExact : (T j k l a b hD hCover).ShortExact := by
  unfold T proComplex
  apply ProetaleMayerVietorisSite.coverComplex_shortExact

theorem map_boundary (F : E X) (n : ℕ) (x : Ext (S j k l a b hD hCover).X₁ F n) :
    let hS := EtaleMayerVietorisHigh.coverComplex_shortExact j k l a b hD hCover
    let hT := pro_shortExact j k l a b hD hCover
    let φ := (comparison j k l a b hD hCover).inv
    (Ext.mk₀ φ.τ₃).comp
        ((hS.extClass.comp x (Nat.add_comm 1 n)).mapExactFunctor (inverseImage X))
          (zero_add (n+1)) =
      hT.extClass.comp ((Ext.mk₀ φ.τ₁).comp (x.mapExactFunctor (inverseImage X)) (zero_add n))
        (Nat.add_comm 1 n) :=
  ExtContravariantBoundaryMap.map_boundary (inverseImage X)
    (EtaleMayerVietorisHigh.coverComplex_shortExact j k l a b hD hCover)
    (pro_shortExact j k l a b hD hCover) (comparison j k l a b hD hCover).inv n x

end
end ManuscriptAudit.EtaleProetaleMayerVietorisBoundary

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleProetaleMayerVietorisBoundary.map_boundary
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
