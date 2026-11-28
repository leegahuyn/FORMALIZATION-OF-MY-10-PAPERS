import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeFreeRepresentable
import PrimalitySheafVerification.ManuscriptAudit.SquareShortComplexTransport
import PrimalitySheafVerification.ManuscriptAudit.ExtContravariantBoundaryMap

/-! The native inverse image transports a cartesian cover square and its
actual Mayer–Vietoris boundary. -/

namespace ManuscriptAudit.ProetaleSchemeFreeSquarePullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange)
open ProetaleInverseImage (inverseImage)
open ProetaleSchemeFreeRepresentable (inverseImageIso inverseImageIso_natural)
open ProetaleMayerVietorisRepresentable (nativeFree)
open EtaleProetaleFreeRepresentable (proFreeMap proSections proSections_freeMap)
open EtaleProetaleFreeRepresentableNaturality (proMap proSections_precomp)
open SquareShortComplexTransport (ofSquare)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

/-- The native sheafified free representable as a genuine site functor. -/
abbrev free (X : Scheme.{0}) : X.ProEt ⥤ P X :=
  (ProetaleMayerVietorisSite.siteEquivalence X).functor ⋙ yoneda ⋙
    ((Functor.whiskeringRight (AsSmall.{1} X.ProEt)ᵒᵖ _ _).obj AddCommGrpCat.free) ⋙
    presheafToSheaf (ProetaleMayerVietorisSite.topology X) A ⋙
    (ProetaleMayerVietorisSite.sheafEquivalence X).inverse

private theorem freeMap_eq {X : Scheme.{0}} {U V : X.ProEt} (g : U ⟶ V) :
    (free X).map g = proMap X g := by
  change proFreeMap X g = proMap X g
  apply (proSections X U (nativeFree V)).injective
  have h₁ := proSections_freeMap X g (𝟙 (nativeFree V))
  have h₂ := proSections_precomp X g (𝟙 (nativeFree V))
  rw [Category.comp_id] at h₁ h₂
  exact h₁.trans h₂.symm

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

private def freePullbackIso : free Y ⋙ inverseImage f ≅ baseChange f ⋙ free X :=
  NatIso.ofComponents (inverseImageIso f) (by
    intro U V g
    change (inverseImage f).map ((free Y).map g) ≫ (inverseImageIso f V).hom =
      (inverseImageIso f U).hom ≫ (free X).map ((baseChange f).map g)
    rw [freeMap_eq, freeMap_eq]
    exact inverseImageIso_natural f g)

private def vertexIso (V : Y.ProEt) (U : X.ProEt) (e : (baseChange f).obj V ≅ U) :
    (inverseImage f).obj ((free Y).obj V) ≅ (free X).obj U :=
  (freePullbackIso f).app V ≪≫ (free X).mapIso e

private theorem edge_compat {V W : Y.ProEt} {U T : X.ProEt}
    (e : (baseChange f).obj V ≅ U) (j : (baseChange f).obj W ≅ T)
    (a : V ⟶ W) (b : U ⟶ T) (h : e.hom ≫ b = (baseChange f).map a ≫ j.hom) :
    (vertexIso f V U e).hom ≫ (free X).map b =
      (inverseImage f).map ((free Y).map a) ≫ (vertexIso f W T j).hom := by
  change (((freePullbackIso f).app V).hom ≫ (free X).map e.hom) ≫ (free X).map b =
    (inverseImage f).map ((free Y).map a) ≫ (((freePullbackIso f).app W).hom ≫ (free X).map j.hom)
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp, ← Category.assoc]
  have hn := congrArg (fun t ↦ t ≫ (free X).map j.hom) ((freePullbackIso f).hom.naturality a)
  exact hn.symm.trans (Category.assoc _ _ _)

variable (S : Square Y.ProEt) (T : Square X.ProEt)
  (e₁ : (baseChange f).obj S.X₁ ≅ T.X₁)
  (e₂ : (baseChange f).obj S.X₂ ≅ T.X₂)
  (e₃ : (baseChange f).obj S.X₃ ≅ T.X₃)
  (e₄ : (baseChange f).obj S.X₄ ≅ T.X₄)
  (h₁₂ : e₁.hom ≫ T.f₁₂ = (baseChange f).map S.f₁₂ ≫ e₂.hom)
  (h₁₃ : e₁.hom ≫ T.f₁₃ = (baseChange f).map S.f₁₃ ≫ e₃.hom)
  (h₂₄ : e₂.hom ≫ T.f₂₄ = (baseChange f).map S.f₂₄ ≫ e₄.hom)
  (h₃₄ : e₃.hom ≫ T.f₃₄ = (baseChange f).map S.f₃₄ ≫ e₄.hom)

private abbrev source := ofSquare (S.map (free Y))
private abbrev target := ofSquare (T.map (free X))

/-- Inverse image commutes with the literal two-chart free short complex. -/
def comparison :
    (source S).map (inverseImage f) ≅ target T := by
  let L := inverseImage f
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  refine SquareShortComplexTransport.mapIso L (S.map (free Y)) ≪≫
    SquareShortComplexTransport.compare _ _
      (vertexIso f S.X₁ T.X₁ e₁) (vertexIso f S.X₂ T.X₂ e₂)
      (vertexIso f S.X₃ T.X₃ e₃) (vertexIso f S.X₄ T.X₄ e₄) ?_ ?_ ?_ ?_
  · exact edge_compat f e₁ e₂ S.f₁₂ T.f₁₂ h₁₂
  · exact edge_compat f e₁ e₃ S.f₁₃ T.f₁₃ h₁₃
  · exact edge_compat f e₂ e₄ S.f₂₄ T.f₂₄ h₂₄
  · exact edge_compat f e₃ e₄ S.f₃₄ T.f₃₄ h₃₄

/-- The corresponding actual connecting map commutes with inverse image. -/
theorem map_boundary (hS : (source S).ShortExact) (hT : (target T).ShortExact)
    (F : P Y) (n : ℕ) (x : Ext (source S).X₁ F n) :
    let φ := (comparison f S T e₁ e₂ e₃ e₄ h₁₂ h₁₃ h₂₄ h₃₄).inv
    (Ext.mk₀ φ.τ₃).comp ((hS.extClass.comp x (Nat.add_comm 1 n)).mapExactFunctor (inverseImage f))
      (zero_add (n + 1)) =
    hT.extClass.comp ((Ext.mk₀ φ.τ₁).comp (x.mapExactFunctor (inverseImage f)) (zero_add n))
      (Nat.add_comm 1 n) :=
  ExtContravariantBoundaryMap.map_boundary (inverseImage f) hS hT
    (comparison f S T e₁ e₂ e₃ e₄ h₁₂ h₁₃ h₂₄ h₃₄).inv n x

end
end ManuscriptAudit.ProetaleSchemeFreeSquarePullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleSchemeFreeSquarePullback.comparison,
      ``ManuscriptAudit.ProetaleSchemeFreeSquarePullback.map_boundary] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
