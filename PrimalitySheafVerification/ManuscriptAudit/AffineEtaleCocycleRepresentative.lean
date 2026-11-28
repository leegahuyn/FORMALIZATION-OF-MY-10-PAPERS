import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorTriple
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleUnitCocycle
import PrimalitySheafVerification.ManuscriptAudit.InjectiveCechOne

/-! Every faithfully flat affine unit cocycle yields an actual étale cohomology representative. -/

namespace ManuscriptAudit.AffineEtaleCocycleRepresentative

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open TensorProduct AffineEtaleTensorOverlap AffineEtaleTensorTriple KummerUnitsSheaf
open AffineEtaleUnitCocycle SheafSectionDifference UnitCocycleTensor

noncomputable section

attribute [local instance] doubleEtale tripleEtale

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]
variable [Module.FaithfullyFlat R B]

private abbrev X := Spec (CommRingCat.of R)
private abbrev J := Scheme.AffineEtale.topology (X R)
private abbrev G := coordinateUnitSheaf (X R)
private abbrev U := ofAlgebra R B
private abbrev D := ofAlgebra R (B ⊗[R] B)
private abbrev E := ofAlgebra R (B ⊗[R] (B ⊗[R] B))

private theorem restrictMap_comp {F : (X R).AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{0}}
    {U V W : (X R).AffineEtale} (g : V ⟶ U) (f : W ⟶ V) (t : F.obj (op U)) :
    F.map f.op (F.map g.op t) = F.map (f ≫ g).op t := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

variable {I : Sheaf (J R) AddCommGrpCat.{0}} [Injective I]
variable (ι : G R ⟶ I) [Mono ι]

/-- The actual unit cocycle of a representative can be prescribed. -/
theorem exists_representative_of_cocycle (t : (B ⊗[R] B)ˣ)
    (ht : pull12 R B (t : B ⊗[R] B) * pull23 R B (t : B ⊗[R] B) =
      pull13 R B (t : B ⊗[R] B)) :
    ∃ (x : (cokernel ι).obj.obj (op (baseObject R))) (y : I.obj.obj (op (U R B)))
      (hy : (cokernel.π ι).hom.app (op (U R B)) y =
        (cokernel ι).obj.map (coverArrow R B).op x), transition R B ι x y hy = t := by
  let δ : Additive (B ⊗[R] B)ˣ := Additive.ofMul t
  let v12 := Units.map (pull12 R B).toMonoidHom t
  let v13 := Units.map (pull13 R B).toMonoidHom t
  let v23 := Units.map (pull23 R B).toMonoidHom t
  have hProd : v13 = v12 * v23 := Units.ext ht.symm
  have hRing : (G R).obj.map (projection23 R B).op δ -
      (G R).obj.map (projection13 R B).op δ +
      (G R).obj.map (projection12 R B).op δ = 0 := by
    apply Additive.ext
    change v23 / v13 * v12 = 1
    rw [hProd, div_eq_mul_inv, mul_inv_rev]
    calc
      v23 * (v23⁻¹ * v12⁻¹) * v12 = (v23 * v23⁻¹) * (v12⁻¹ * v12) := by ac_rfl
      _ = 1 := by rw [mul_inv_cancel, inv_mul_cancel, one_mul]
  let c : ∀ {W : (X R).AffineEtale}, (W ⟶ U R B) → (W ⟶ U R B) → I.obj.obj (op W) :=
    fun {W} a b => ι.hom.app (op W) ((G R).obj.map (pair R B a b).op δ)
  have hNat {W V : (X R).AffineEtale} (g : V ⟶ W) (a b : W ⟶ U R B) :
      I.obj.map g.op (c a b) = c (g ≫ a) (g ≫ b) := by
    change I.obj.map g.op (ι.hom.app (op W) ((G R).obj.map (pair R B a b).op δ)) =
      ι.hom.app (op V) ((G R).obj.map (pair R B (g ≫ a) (g ≫ b)).op δ)
    rw [← NatTrans.naturality_apply ι.hom, restrictMap_comp, pair_comp]
  have hCoc {W : (X R).AffineEtale} (a b d : W ⟶ U R B) :
      c b d - c a d + c a b = 0 := by
    let s := triple R B a b d
    let m : (G R).obj.obj (op (E R B)) →+ I.obj.obj (op W) :=
      (ι.hom.app (op W)).hom.comp ((G R).obj.map s.op).hom
    have hh := congrArg m hRing
    simp only [map_add, map_sub, map_zero] at hh
    change ι.hom.app (op W) ((G R).obj.map s.op ((G R).obj.map (projection23 R B).op δ)) -
      ι.hom.app (op W) ((G R).obj.map s.op ((G R).obj.map (projection13 R B).op δ)) +
      ι.hom.app (op W) ((G R).obj.map s.op ((G R).obj.map (projection12 R B).op δ)) = 0 at hh
    rw [restrictMap_comp, restrictMap_comp, restrictMap_comp] at hh
    simpa only [s, triple_23, triple_13, triple_12] using hh
  obtain ⟨z, hz⟩ := InjectiveCechOne.exists_coboundary (J R) (U R B) I c hNat hCoc
  let y := -z
  have hdif {W : (X R).AffineEtale} (a b : W ⟶ U R B) :
      c a b = I.obj.map a.op y - I.obj.map b.op y := by
    change c a b = (I.obj.map a.op).hom (-z) - (I.obj.map b.op).hom (-z)
    rw [map_neg, map_neg, hz a b]
    abel
  let Q := cokernel ι
  let π : I ⟶ Q := cokernel.π ι
  let f := coverArrow R B
  let Fg := forget AddCommGrpCat.{0}
  have hQ : Presieve.IsSheaf (J R) (Q.obj ⋙ Fg) :=
    (isSheaf_iff_isSheaf_of_type (J R) (Q.obj ⋙ Fg)).mp ((sheafCompose (J R) Fg).obj Q).property
  have hCompat {W : (X R).AffineEtale} (a b : W ⟶ U R B) (_ : a ≫ f = b ≫ f) :
      Q.obj.map a.op (π.hom.app (op (U R B)) y) =
        Q.obj.map b.op (π.hom.app (op (U R B)) y) := by
    rw [← NatTrans.naturality_apply π.hom, ← NatTrans.naturality_apply π.hom]
    apply sub_eq_zero.mp
    change (π.hom.app (op W)).hom (I.obj.map a.op y) -
      (π.hom.app (op W)).hom (I.obj.map b.op y) = 0
    rw [← map_sub, ← hdif a b]
    let w := (G R).obj.map (pair R B a b).op δ
    exact congrArg (fun g : G R ⟶ Q => g.hom.app (op W) w) (cokernel.condition ι)
  have hCompat' {W : (X R).AffineEtale} (a b : W ⟶ U R B) (h : a ≫ f = b ≫ f) :
      (Q.obj ⋙ Fg).map a.op (π.hom.app (op (U R B)) y) =
        (Q.obj ⋙ Fg).map b.op (π.hom.app (op (U R B)) y) := hCompat a b h
  obtain ⟨x, hx, _⟩ := (Presieve.isSheafFor_singleton.mp
    (hQ.isSheafFor _ (coverArrow_generate_mem R B))) (π.hom.app (op (U R B)) y) hCompat'
  change Q.obj.map f.op x = π.hom.app (op (U R B)) y at hx
  refine ⟨x, y, hx.symm, ?_⟩
  have hPair : pair R B (firstProjection R B) (secondProjection R B) = 𝟙 (D R B) := by
    apply (double_isPullback R B).hom_ext <;> simp
  have hImage : ι.hom.app (op (D R B)) δ =
      I.obj.map (firstProjection R B).op y - I.obj.map (secondProjection R B).op y := by
    have hh := hdif (firstProjection R B) (secondProjection R B)
    change ι.hom.app (op (D R B))
      ((G R).obj.map (pair R B (firstProjection R B) (secondProjection R B)).op δ) = _ at hh
    rw [hPair] at hh
    simpa only [op_id, Functor.map_id, ConcreteCategory.id_apply] using hh
  have hOverlap : Additive.ofMul (transition R B ι x y hx.symm) = δ := by
    apply section_injective ι (D R B)
    exact (difference_spec ..).trans hImage.symm
  exact congrArg Additive.toMul hOverlap

end

end ManuscriptAudit.AffineEtaleCocycleRepresentative

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleCocycleRepresentative.exists_representative_of_cocycle
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
