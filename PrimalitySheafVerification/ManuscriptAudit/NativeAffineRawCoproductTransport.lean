import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineProetaleChartTransport
import PrimalitySheafVerification.ManuscriptAudit.NativeProetaleAffineProductCoproduct
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawProducts
import PrimalitySheafVerification.ManuscriptAudit.ProetaleRawAffineSingletonComparison

/-! The raw finite product formula holds on the actual disjoint
union of arbitrary affine objects of the native site over an affine line. -/

namespace ManuscriptAudit.NativeAffineRawCoproductTransport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap object)
open NativeAffineEtaleRawStageElements (chartMap)
open NativeAffineProetaleChartTransport (coordinateRing chartIso)
open NativeAffineEtaleKanComparison (raw)
open ProetaleAffineCoproduct (coproduct injection)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A : Type} [CommRing A] {n : ℕ}
  (V : Fin n → (spectrum A).ProEt) [∀ i, IsAffine (V i).left]

private abbrev B (i : Fin n) : Type := ↑(coordinateRing (V i))
private abbrev W (i : Fin n) := object A (B V i)

local instance : WeaklyEtale (structureMap A (∀ i, B V i)) :=
  NativeProetaleAffineProductCoproduct.product_weaklyEtale (A := A) (B V)

private def piecesIso (i : Fin n) : (W V i).left ≅ (V i).left :=
  (Scheme.ProEt.forget (spectrum A) ⋙ Over.forget _).mapIso (chartIso (V i))

private def productSchemeIso : (object A (∀ i, B V i)).left ≅ (coproduct V).left :=
  letI := NativeProetaleAffineProductCoproduct.comparison_isIso (B V)
  (asIso (NativeProetaleAffineProductCoproduct.comparison (B V))).symm.trans
    (Sigma.mapIso (piecesIso V))

private theorem product_leg_scheme (i : Fin n) :
    (chartMap (Pi.evalAlgHom A (B V) i)).left ≫ (productSchemeIso V).hom =
      (chartIso (V i)).hom.left ≫ (injection V i).left := by
  let f := NativeProetaleAffineProductCoproduct.comparison (B V)
  letI := NativeProetaleAffineProductCoproduct.comparison_isIso (B V)
  change FiniteProductSpectrumOpen.projection (B V) i ≫
    (inv f ≫ (Sigma.mapIso (piecesIso V)).hom) = _
  have h : Sigma.ι (fun j ↦ (W V j).left) i ≫ f =
      FiniteProductSpectrumOpen.projection (B V) i := Sigma.ι_desc _ _
  rw [← h, Category.assoc, IsIso.hom_inv_id_assoc, Sigma.ι_mapIso_hom]
  rfl

private theorem product_over :
    (productSchemeIso V).hom ≫ (coproduct V).hom = structureMap A (∀ i, B V i) := by
  let f := NativeProetaleAffineProductCoproduct.comparison (B V)
  letI := NativeProetaleAffineProductCoproduct.comparison_isIso (B V)
  rw [← cancel_epi f]
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ← Category.assoc]
  have h : Sigma.ι (fun j ↦ (W V j).left) i ≫ f =
      FiniteProductSpectrumOpen.projection (B V) i := Sigma.ι_desc _ _
  have hπ : ((chartMap (Pi.evalAlgHom A (B V) i)).left ≫ (productSchemeIso V).hom) ≫
      (coproduct V).hom = (chartMap (Pi.evalAlgHom A (B V) i)).left ≫
        structureMap A (∀ i, B V i) := by
    rw [product_leg_scheme, Category.assoc, MorphismProperty.Over.w (injection V i),
      MorphismProperty.Over.w (chartIso (V i)).hom, MorphismProperty.Over.w]
  exact (congrArg (fun q ↦ (q ≫ (productSchemeIso V).hom) ≫ (coproduct V).hom) h).trans
    (hπ.trans (congrArg (fun q ↦ q ≫ structureMap A (∀ i, B V i)) h.symm))

private def productIso : object A (∀ i, B V i) ≅ coproduct V :=
  MorphismProperty.Over.isoMk (productSchemeIso V) (product_over V)

private theorem product_leg (i : Fin n) :
    chartMap (Pi.evalAlgHom A (B V) i) ≫ (productIso V).hom =
      (chartIso (V i)).hom ≫ injection V i := by
  apply MorphismProperty.Over.Hom.ext
  exact product_leg_scheme V i

variable (I : Sheaf (spectrum A).smallEtaleTopology AddCommGrpCat.{1})

private abbrev P := raw (spectrum A) I

private theorem map_map {W₁ W₂ W₃ : (spectrum A).ProEt} (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃)
    (x : (P I).obj (op W₃)) :
    (P I).map f.op ((P I).map g.op x) = (P I).map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

private theorem iso_restrict_injective {U W : (spectrum A).ProEt} (e : U ≅ W) :
    Function.Injective ((P I).map e.hom.op) := by
  intro x y he
  have h (a : (P I).obj (op W)) :
      (P I).map e.inv.op ((P I).map e.hom.op a) = a := by
    rw [map_map, e.inv_hom_id, op_id, CategoryTheory.Functor.map_id] <;> rfl
  exact (h x).symm.trans ((congrArg ((P I).map e.inv.op) he).trans (h y))

set_option maxHeartbeats 5100000 in
/-- Finite disjoint native affine sections of the raw presheaf
are the product of the actual component sections. -/
theorem existsUnique_raw_sections (x : ∀ i, (P I).obj (op (V i))) :
    ∃! z : (P I).obj (op (coproduct V)), ∀ i, (P I).map (injection V i).op z = x i := by
  let j := productIso V
  let e (i : Fin n) := chartIso (V i)
  let y (i : Fin n) := (P I).map (e i).hom.op (x i)
  obtain ⟨z, hz, hUniq⟩ := NativeAffineEtaleRawProducts.existsUnique_sections_raw (B V) I y
  let w := (P I).map j.inv.op z
  have hw : (P I).map j.hom.op w = z := by
    rw [show w = (P I).map j.inv.op z from rfl, map_map, j.hom_inv_id,
      op_id, CategoryTheory.Functor.map_id] <;> rfl
  have h (i : Fin n) (v : (P I).obj (op (coproduct V))) :
      (P I).map (chartMap (Pi.evalAlgHom A (B V) i)).op ((P I).map j.hom.op v) =
        (P I).map (e i).hom.op ((P I).map (injection V i).op v) := by
    rw [map_map, map_map, product_leg]
  refine ⟨w, ?_, ?_⟩
  · intro i
    apply iso_restrict_injective I (e i)
    change (P I).map (e i).hom.op ((P I).map (injection V i).op w) = y i
    rw [← h i, hw]
    exact hz i
  · intro v hv
    apply iso_restrict_injective I j
    change (P I).map j.hom.op v = (P I).map j.hom.op w
    rw [hw]
    apply hUniq
    intro i
    rw [h i, hv]

omit [∀ i, IsAffine (V i).left] in
/-- Disjoint-union descent for the raw presheaf, as used by the actual
affine singleton comparison. -/
theorem affineCoproductSections :
    ProetaleRawAffineSingletonComparison.AffineCoproductSections (P I) := by
  intro m V' hV x
  letI := hV
  exact existsUnique_raw_sections V' I x

end
end ManuscriptAudit.NativeAffineRawCoproductTransport

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineRawCoproductTransport.existsUnique_raw_sections
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
