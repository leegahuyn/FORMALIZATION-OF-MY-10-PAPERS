import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.Square
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.Basic

/-! Transport of the signed short complex of a commutative square. -/

namespace ManuscriptAudit.SquareShortComplexTransport

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]

def ofSquare (S : Square C) : ShortComplex C :=
  ShortComplex.mk (biprod.lift S.f₁₂ (-S.f₁₃)) (biprod.desc S.f₂₄ S.f₃₄)
    S.cokernelCofork.condition

def compare (S T : Square C) (i₁ : S.X₁ ≅ T.X₁) (i₂ : S.X₂ ≅ T.X₂)
    (i₃ : S.X₃ ≅ T.X₃) (i₄ : S.X₄ ≅ T.X₄)
    (h₁₂ : i₁.hom ≫ T.f₁₂ = S.f₁₂ ≫ i₂.hom)
    (h₁₃ : i₁.hom ≫ T.f₁₃ = S.f₁₃ ≫ i₃.hom)
    (h₂₄ : i₂.hom ≫ T.f₂₄ = S.f₂₄ ≫ i₄.hom)
    (h₃₄ : i₃.hom ≫ T.f₃₄ = S.f₃₄ ≫ i₄.hom) :
    ofSquare S ≅ ofSquare T := by
  refine ShortComplex.isoMk i₁ (biprod.mapIso i₂ i₃) i₄ ?_ ?_
  · apply biprod.hom_ext
    · change (i₁.hom ≫ biprod.lift T.f₁₂ (-T.f₁₃)) ≫ biprod.fst =
        (biprod.lift S.f₁₂ (-S.f₁₃) ≫ biprod.map i₂.hom i₃.hom) ≫ biprod.fst
      rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst,
        ← Category.assoc, biprod.lift_fst, h₁₂]
    · change (i₁.hom ≫ biprod.lift T.f₁₂ (-T.f₁₃)) ≫ biprod.snd =
        (biprod.lift S.f₁₂ (-S.f₁₃) ≫ biprod.map i₂.hom i₃.hom) ≫ biprod.snd
      rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd,
        ← Category.assoc, biprod.lift_snd, Preadditive.comp_neg, Preadditive.neg_comp, h₁₃]
  · apply biprod.hom_ext'
    · change biprod.inl ≫ (biprod.map i₂.hom i₃.hom ≫ biprod.desc T.f₂₄ T.f₃₄) =
        biprod.inl ≫ (biprod.desc S.f₂₄ S.f₃₄ ≫ i₄.hom)
      rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc,
        ← Category.assoc, biprod.inl_desc, h₂₄]
    · change biprod.inr ≫ (biprod.map i₂.hom i₃.hom ≫ biprod.desc T.f₂₄ T.f₃₄) =
        biprod.inr ≫ (biprod.desc S.f₂₄ S.f₃₄ ≫ i₄.hom)
      rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc,
        ← Category.assoc, biprod.inr_desc, h₃₄]

def mapIso (L : C ⥤ D) [L.Additive] [PreservesBinaryBiproducts L] (S : Square C) :
    (ofSquare S).map L ≅ ofSquare (S.map L) := by
  refine ShortComplex.isoMk (Iso.refl _) (L.mapBiprod S.X₂ S.X₃) (Iso.refl _) ?_ ?_
  · change (𝟙 _) ≫ biprod.lift (L.map S.f₁₂) (-L.map S.f₁₃) =
      L.map (biprod.lift S.f₁₂ (-S.f₁₃)) ≫ (L.mapBiprod S.X₂ S.X₃).hom
    rw [Category.id_comp, biprod.map_lift_mapBiprod, L.map_neg]
  · change (L.mapBiprod S.X₂ S.X₃).hom ≫ biprod.desc (L.map S.f₂₄) (L.map S.f₃₄) =
      L.map (biprod.desc S.f₂₄ S.f₃₄) ≫ (𝟙 _)
    rw [biprod.mapBiprod_hom_desc, Category.comp_id]

end
end ManuscriptAudit.SquareShortComplexTransport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SquareShortComplexTransport.compare,
      ``ManuscriptAudit.SquareShortComplexTransport.mapIso] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
