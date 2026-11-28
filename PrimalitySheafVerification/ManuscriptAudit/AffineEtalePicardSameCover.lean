import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleUnitCocycle

/-! Changing native cohomology representatives on the same affine cover. -/

namespace ManuscriptAudit.AffineEtalePicardSameCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AffineEtaleTensorOverlap KummerUnitsSheaf SheafSectionDifference AffineEtaleUnitCocycle

attribute [local instance] doubleEtale tripleEtale

noncomputable section

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]

private abbrev G := coordinateUnitSheaf (Spec (CommRingCat.of R))

variable {I : Sheaf (Scheme.AffineEtale.topology (Spec (CommRingCat.of R))) AddCommGrpCat.{0}}
variable (ι : G R ⟶ I) [Mono ι]
variable (x : (cokernel ι).obj.obj (op (baseObject R))) (y : I.obj.obj (op (ofAlgebra R B)))
variable (hy : (cokernel.π ι).hom.app (op (ofAlgebra R B)) y =
  (cokernel ι).obj.map (coverArrow R B).op x)

private theorem restrictMap_comp {U V W : (Spec (CommRingCat.of R)).AffineEtale}
    (r : V ⟶ U) (s : W ⟶ V) (t : I.obj.obj (op U)) :
    I.obj.map s.op (I.obj.map r.op t) = I.obj.map (s ≫ r).op t := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The actual image of the transition in the representative sheaf is the
difference of the two restrictions. -/
theorem transition_image :
    ι.hom.app (op (ofAlgebra R (B ⊗[R] B))) (Additive.ofMul (transition R B ι x y hy)) =
      I.obj.map (firstProjection R B).op y - I.obj.map (secondProjection R B).op y :=
  difference_spec ι (ofAlgebra R (B ⊗[R] B))
    (I.obj.map (firstProjection R B).op y) (I.obj.map (secondProjection R B).op y)
    (SheafCoboundaryLift.same_image_on_overlap ι (coverArrow R B) (firstProjection R B)
      (secondProjection R B) (double_isPullback R B).w x y hy)

/-- Two local lifts on the same cover whose cokernel sections differ by a
global lifted section have transition units differing by a change of basis. -/
theorem transition_changeUnit_sameCover
    (x' : (cokernel ι).obj.obj (op (baseObject R)))
    (y' : I.obj.obj (op (ofAlgebra R B)))
    (hy' : (cokernel.π ι).hom.app (op (ofAlgebra R B)) y' =
      (cokernel ι).obj.map (coverArrow R B).op x')
    (z : I.obj.obj (op (baseObject R)))
    (hz : (cokernel.π ι).hom.app (op (baseObject R)) z = x - x') :
    ∃ v : Bˣ,
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (v : B)) *
          (transition R B ι x' y' hy' : B ⊗[R] B) =
        (transition R B ι x y hy : B ⊗[R] B) *
          ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (v : B)) := by
  let U := ofAlgebra R B
  let D := ofAlgebra R (B ⊗[R] B)
  let f := coverArrow R B
  let p := firstProjection R B
  let q := secondProjection R B
  let π := cokernel.π ι
  have hLoc : π.hom.app (op U) (I.obj.map f.op z) =
      (cokernel ι).obj.map f.op (x - x') := by
    rw [NatTrans.naturality_apply, hz]
  have hIm : π.hom.app (op U) y = π.hom.app (op U) (y' + I.obj.map f.op z) := by
    change π.hom.app (op U) y = (π.hom.app (op U)).hom (y' + I.obj.map f.op z)
    rw [map_add, hy, hy', hLoc, map_sub]
    abel
  let a : Additive Bˣ := difference ι U y (y' + I.obj.map f.op z) hIm
  have ha : ι.hom.app (op U) a = y - (y' + I.obj.map f.op z) :=
    difference_spec ι U y (y' + I.obj.map f.op z) hIm
  have hRestrict (g : D ⟶ U) :
      ι.hom.app (op D) ((G R).obj.map g.op a) =
        I.obj.map g.op y - (I.obj.map g.op y' + I.obj.map (g ≫ f).op z) := by
    rw [NatTrans.naturality_apply, ha]
    change (I.obj.map g.op).hom (y - (y' + I.obj.map f.op z)) = _
    rw [map_sub, map_add, restrictMap_comp]
  have hComm : p ≫ f = q ≫ f := (double_isPullback R B).w
  let u : Additive (B ⊗[R] B)ˣ := Additive.ofMul (transition R B ι x y hy)
  let u' : Additive (B ⊗[R] B)ˣ := Additive.ofMul (transition R B ι x' y' hy')
  have hDiff : u - u' = (G R).obj.map p.op a - (G R).obj.map q.op a := by
    apply section_injective ι D
    let m : Additive (B ⊗[R] B)ˣ →+ I.obj.obj (op D) := (ι.hom.app (op D)).hom
    let ap : Additive (B ⊗[R] B)ˣ := (G R).obj.map p.op a
    let aq : Additive (B ⊗[R] B)ˣ := (G R).obj.map q.op a
    have hInner : m u - m u' = m ap - m aq := by
      change ι.hom.app (op D) u - ι.hom.app (op D) u' =
        ι.hom.app (op D) ((G R).obj.map p.op a) - ι.hom.app (op D) ((G R).obj.map q.op a)
      rw [hRestrict, hRestrict, hComm]
      have hu : ι.hom.app (op D) u = I.obj.map p.op y - I.obj.map q.op y := transition_image R B ι x y hy
      have hu' : ι.hom.app (op D) u' = I.obj.map p.op y' - I.obj.map q.op y' := transition_image R B ι x' y' hy'
      rw [hu, hu']
      abel
    exact (m.map_sub u u').trans (hInner.trans (m.map_sub ap aq).symm)
  let l := Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toMonoidHom
  let r := Units.map (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toMonoidHom
  have hU : u.toMul / u'.toMul = l a.toMul / r a.toMul := congrArg Additive.toMul hDiff
  refine ⟨a.toMul⁻¹, ?_⟩
  have he : r a.toMul⁻¹ * u'.toMul = u.toMul * l a.toMul⁻¹ := by
    rw [map_inv, map_inv]
    calc
      (r a.toMul)⁻¹ * u'.toMul =
          (l a.toMul)⁻¹ * (l a.toMul / r a.toMul) * u'.toMul := by
        rw [div_eq_mul_inv, ← mul_assoc (l a.toMul)⁻¹, inv_mul_cancel, one_mul]
      _ = (l a.toMul)⁻¹ * (u.toMul / u'.toMul) * u'.toMul := by rw [hU]
      _ = u.toMul * (l a.toMul)⁻¹ := by
        rw [mul_assoc, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one, mul_comm]
  exact congrArg Units.val he


end

end ManuscriptAudit.AffineEtalePicardSameCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtalePicardSameCover.transition_image,
      ``ManuscriptAudit.AffineEtalePicardSameCover.transition_changeUnit_sameCover] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
