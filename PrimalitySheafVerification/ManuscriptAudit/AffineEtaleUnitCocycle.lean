import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorOverlap
import PrimalitySheafVerification.ManuscriptAudit.AffineUnitDescent
import PrimalitySheafVerification.ManuscriptAudit.KummerUnitsSheaf
import PrimalitySheafVerification.ManuscriptAudit.SheafCoboundaryLift

/-!
# The unit cocycle of a native affine étale lift

A local lift of a cokernel section for a monomorphism from the coordinate
units sheaf gives an actual unit on the tensor double overlap. Its diagonal
restriction is one and the three restrictions satisfy the ordinary unit
cocycle identity on the triple tensor overlap.
-/

namespace ManuscriptAudit.AffineEtaleUnitCocycle

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AffineEtaleTensorOverlap KummerUnitsSheaf SheafSectionDifference UnitCocycleTensor

attribute [local instance] doubleEtale tripleEtale

noncomputable section

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]

private theorem coordinate_arrow_ext {U V : (Spec (CommRingCat.of R)).AffineEtale}
    {f g : U ⟶ V}
    (h : ∀ b : V.left.unop, f.left.unop.hom b = g.left.unop.hom b) : f = g := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  apply Quiver.Hom.unop_inj
  exact CommRingCat.hom_ext (RingHom.ext h)

private theorem diagonal_first :
    diagonalArrow R B ≫ firstProjection R B = 𝟙 (ofAlgebra R B) := by
  apply coordinate_arrow_ext R
  intro b
  change Algebra.TensorProduct.lmul' R (b ⊗ₜ[R] (1 : B)) = b
  rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

private theorem diagonal_second :
    diagonalArrow R B ≫ secondProjection R B = 𝟙 (ofAlgebra R B) := by
  apply coordinate_arrow_ext R
  intro b
  change Algebra.TensorProduct.lmul' R ((1 : B) ⊗ₜ[R] b) = b
  rw [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]

private theorem triple_left :
    projection12 R B ≫ firstProjection R B = projection13 R B ≫ firstProjection R B := by
  apply coordinate_arrow_ext R
  intro b
  change pull12 R B (b ⊗ₜ[R] (1 : B)) = pull13 R B (b ⊗ₜ[R] (1 : B))
  simp only [pull12, pull13, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

private theorem triple_middle :
    projection12 R B ≫ secondProjection R B = projection23 R B ≫ firstProjection R B := by
  apply coordinate_arrow_ext R
  intro b
  change pull12 R B ((1 : B) ⊗ₜ[R] b) = pull23 R B (b ⊗ₜ[R] (1 : B))
  simp only [pull12, pull23, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]

private theorem triple_right :
    projection13 R B ≫ secondProjection R B = projection23 R B ≫ secondProjection R B := by
  apply coordinate_arrow_ext R
  intro b
  change pull13 R B ((1 : B) ⊗ₜ[R] b) = pull23 R B ((1 : B) ⊗ₜ[R] b)
  simp only [pull13, pull23, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.includeRight_apply]

private abbrev G := coordinateUnitSheaf (Spec (CommRingCat.of R))

variable {I : Sheaf (Scheme.AffineEtale.topology (Spec (CommRingCat.of R))) AddCommGrpCat.{0}}
variable (ι : G R ⟶ I) [Mono ι]
variable (x : (cokernel ι).obj.obj (op (baseObject R))) (y : I.obj.obj (op (ofAlgebra R B)))
variable (hy : (cokernel.π ι).hom.app (op (ofAlgebra R B)) y =
  (cokernel ι).obj.map (coverArrow R B).op x)

private abbrev transitionSection : Additive (B ⊗[R] B)ˣ :=
  difference ι (ofAlgebra R (B ⊗[R] B))
    (I.obj.map (firstProjection R B).op y) (I.obj.map (secondProjection R B).op y)
    (SheafCoboundaryLift.same_image_on_overlap ι (coverArrow R B) (firstProjection R B)
      (secondProjection R B) (double_isPullback R B).w x y hy)

/-- The quotient of the two local restrictions, interpreted as an actual unit. -/
def transition : (B ⊗[R] B)ˣ :=
  (transitionSection R B ι x y hy).toMul

private theorem restrictMap_comp {U V W : (Spec (CommRingCat.of R)).AffineEtale}
    (r : V ⟶ U) (s : W ⟶ V) (t : I.obj.obj (op U)) :
    I.obj.map s.op (I.obj.map r.op t) = I.obj.map (s ≫ r).op t := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

private theorem transition_restriction {W : (Spec (CommRingCat.of R)).AffineEtale}
    (r : W ⟶ ofAlgebra R (B ⊗[R] B)) :
    ι.hom.app (op W) ((G R).obj.map r.op (transitionSection R B ι x y hy)) =
      I.obj.map (r ≫ firstProjection R B).op y - I.obj.map (r ≫ secondProjection R B).op y := by
  rw [NatTrans.naturality_apply]
  unfold transitionSection
  rw [difference_spec]
  change (I.obj.map r.op).hom (_ - _) = _
  rw [map_sub]
  change I.obj.map r.op (I.obj.map (firstProjection R B).op y) -
    I.obj.map r.op (I.obj.map (secondProjection R B).op y) = _
  rw [restrictMap_comp, restrictMap_comp]

/-- Pulling the transition unit back to the diagonal gives one. -/
theorem transition_diagonal :
    diagonal R B (transition R B ι x y hy : B ⊗[R] B) = 1 := by
  have h := transition_restriction R B ι x y hy (diagonalArrow R B)
  rw [diagonal_first, diagonal_second, sub_self] at h
  have hz : (G R).obj.map (diagonalArrow R B).op (transitionSection R B ι x y hy) = 0 := by
    apply section_injective ι (ofAlgebra R B)
    exact h.trans (map_zero (ι.hom.app (op (ofAlgebra R B))).hom).symm
  exact congrArg (fun a : Additive Bˣ => (a.toMul : B)) hz

/-- The actual triple tensor restrictions of the transition unit satisfy the cocycle law. -/
theorem transition_cocycle :
    pull12 R B (transition R B ι x y hy : B ⊗[R] B) *
      pull23 R B (transition R B ι x y hy : B ⊗[R] B) =
        pull13 R B (transition R B ι x y hy : B ⊗[R] B) := by
  let a := transitionSection R B ι x y hy
  let Z := ofAlgebra R (B ⊗[R] (B ⊗[R] B))
  have h : (G R).obj.map (projection12 R B).op a + (G R).obj.map (projection23 R B).op a =
      (G R).obj.map (projection13 R B).op a := by
    apply section_injective ι Z
    change (ι.hom.app (op Z)).hom (_ + _) = _
    rw [map_add]
    change ι.hom.app (op Z) ((G R).obj.map (projection12 R B).op a) +
      ι.hom.app (op Z) ((G R).obj.map (projection23 R B).op a) =
        ι.hom.app (op Z) ((G R).obj.map (projection13 R B).op a)
    rw [transition_restriction R B ι x y hy, transition_restriction R B ι x y hy,
      transition_restriction R B ι x y hy, triple_left, triple_middle, triple_right]
    exact sub_add_sub_cancel _ _ _
  exact congrArg (fun t : Additive (B ⊗[R] (B ⊗[R] B))ˣ => (t.toMul : B ⊗[R] (B ⊗[R] B))) h

/-- One local lift on a faithfully flat affine étale cover of a PID
can be corrected to an actual global lift of the same cokernel section. -/
theorem global_lift_from_faithfully_flat_affine_lift [IsDomain R] [IsPrincipalIdealRing R]
    [Module.FaithfullyFlat R B] :
    ∃ z : I.obj.obj (op (baseObject R)), (cokernel.π ι).hom.app (op (baseObject R)) z = x := by
  let u := transition R B ι x y hy
  let l := Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toMonoidHom
  let r := Units.map (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toMonoidHom
  have hf : (algebraMap R B).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hDescent : ∀ c : (B ⊗[R] B)ˣ,
      diagonal R B (c : B ⊗[R] B) = 1 →
      pull12 R B (c : B ⊗[R] B) * pull23 R B (c : B ⊗[R] B) =
        pull13 R B (c : B ⊗[R] B) →
      ∃ v : Bˣ, c = (l v)⁻¹ * r v := by
    simpa only [toAlgebra_algebraMap, l, r] using
      AffineUnitDescent.unit_cocycle_is_coboundary (algebraMap R B) hf
  obtain ⟨v, hv⟩ := hDescent u (transition_diagonal R B ι x y hy) (transition_cocycle R B ι x y hy)
  let b : Additive Bˣ := Additive.ofMul v⁻¹
  have hb : transitionSection R B ι x y hy =
      (G R).obj.map (firstProjection R B).op b - (G R).obj.map (secondProjection R B).op b := by
    apply Additive.ext
    change u = l v⁻¹ / r v⁻¹
    rw [map_inv, map_inv, div_eq_mul_inv, inv_inv]
    exact hv
  exact SheafCoboundaryLift.exists_global_lift_of_double_overlap_coboundary ι
    (coverArrow R B) (firstProjection R B) (secondProjection R B) (double_isPullback R B)
    (coverArrow_generate_mem R B) x y hy b hb

end

end ManuscriptAudit.AffineEtaleUnitCocycle

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleUnitCocycle.transition_diagonal,
      ``ManuscriptAudit.AffineEtaleUnitCocycle.transition_cocycle,
      ``ManuscriptAudit.AffineEtaleUnitCocycle.global_lift_from_faithfully_flat_affine_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
