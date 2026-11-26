import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectivePoints
import PrimalitySheafVerification.ManuscriptAudit.NodalRationalInfinity
import PrimalitySheafVerification.ManuscriptAudit.SchemeRationalPointsOpen

/-! Scheme-valued rational points of the actual projective nodal cubic,
compared with the verified homogeneous points and their finite counts. -/

namespace ManuscriptAudit.NodalSchemePointCounts

open AlgebraicGeometry CategoryTheory Opposite
open SchemeRationalPointsOpen
open NodalProjectiveClosure (affineNode affineOpen projectiveNode projectiveNodeToBase affineOpen_toBase)
open NodalRationalInfinity (infinityPoint infinityPoint_overBase infinityPoint_outside boundary_eq_infinityPoint)
open NodalAffinePresentation (nodeX nodeY equation coordinateEquiv parameter_base parameter_root)
open NodalAffinePointCounts (affinePoints)
open NodalConductor (coordinates)
open Polynomial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

private def ringPoints {R : Type u} [CommRing R] [Algebra K R] :
    PointsOver (Spec.map (CommRingCat.ofHom (algebraMap K R))) ≃ (R →ₐ[K] K) := by
  let t : CommRingCat.of K ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap K R)
  let f (p : PointsOver (Spec.map t)) : CommRingCat.of R ⟶ CommRingCat.of K :=
    (Scheme.Spec.preimage p.val).unop
  have he (p : PointsOver (Spec.map t)) : Spec.map (f p) = p.val :=
    Scheme.Spec.map_preimage p.val
  have hbase (p : PointsOver (Spec.map t)) : t ≫ f p = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, he, p.property, Spec.map_id]
  refine
    { toFun := fun p => ⟨(f p).hom, fun k => ConcreteCategory.congr_hom (hbase p) k⟩
      invFun := fun a => ⟨Spec.map (CommRingCat.ofHom a.toRingHom), ?_⟩
      left_inv := fun p => Subtype.ext (he p)
      right_inv := ?_ }
  · rw [← Spec.map_comp, ← Spec.map_id]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact a.commutes
  · intro a
    have h : f ⟨Spec.map (CommRingCat.ofHom a.toRingHom), by
          rw [← Spec.map_comp, ← Spec.map_id]
          apply congrArg Spec.map
          apply CommRingCat.hom_ext
          apply RingHom.ext
          exact a.commutes⟩ = CommRingCat.ofHom a.toRingHom := by
      apply Spec.map_injective
      rw [he]
    exact AlgHom.ext (fun x => ConcreteCategory.congr_hom h x)

private theorem node_relation :
    nodeY K ^ 2 = nodeX K ^ 2 * (nodeX K + 1) := by
  apply Subtype.ext
  change (NodalConductor.y K) ^ 2 =
    (NodalConductor.x K) ^ 2 * (NodalConductor.x K + 1)
  unfold NodalConductor.y NodalConductor.x
  ring

private def fromAffinePoint (p : affinePoints K) : coordinates K →ₐ[K] K := by
  let b := Polynomial.aeval p.val.1
  have hb : (equation K).eval₂ b.toRingHom p.val.2 = 0 := by
    unfold equation
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change p.val.2 ^ 2 - b (Polynomial.X ^ 2 * (Polynomial.X + 1)) = 0
    rw [map_mul, map_pow, map_add, map_one, Polynomial.aeval_X, p.property, sub_self]
  exact (AdjoinRoot.liftAlgHom (equation K) b p.val.2 hb).comp (coordinateEquiv K).symm.toAlgHom

private theorem generator_x :
    coordinateEquiv K (AdjoinRoot.of (equation K) (Polynomial.X : Polynomial K)) = nodeX K := by
  change NodalAffinePresentation.parameter K (AdjoinRoot.of (equation K) Polynomial.X) = _
  rw [parameter_base]
  exact Polynomial.aeval_X _

private theorem generator_y :
    coordinateEquiv K (AdjoinRoot.root (equation K)) = nodeY K :=
  parameter_root K

private theorem fromAffinePoint_x (p : affinePoints K) :
    fromAffinePoint K p (nodeX K) = p.val.1 := by
  rw [← generator_x K]
  unfold fromAffinePoint
  rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, AdjoinRoot.liftAlgHom_of]
  exact Polynomial.aeval_X _

private theorem fromAffinePoint_y (p : affinePoints K) :
    fromAffinePoint K p (nodeY K) = p.val.2 := by
  rw [← generator_y K]
  unfold fromAffinePoint
  rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, AdjoinRoot.liftAlgHom_root]

private theorem coordinateAlgHom_ext {f g : coordinates K →ₐ[K] K}
    (hx : f (nodeX K) = g (nodeX K)) (hy : f (nodeY K) = g (nodeY K)) : f = g := by
  let e := coordinateEquiv K
  have hcomp : f.comp e.toAlgHom = g.comp e.toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change f (e (AdjoinRoot.of (equation K) Polynomial.X)) =
        g (e (AdjoinRoot.of (equation K) Polynomial.X))
      rw [generator_x, hx]
    · change f (e (AdjoinRoot.root (equation K))) = g (e (AdjoinRoot.root (equation K)))
      rw [generator_y, hy]
  apply AlgHom.ext
  intro q
  obtain ⟨a, rfl⟩ := e.surjective q
  exact DFunLike.congr_fun hcomp a

/-- The actual affine nodal morphisms over K are exactly the affine equation's solutions. -/
def affineEquiv :
    PointsOver (affineOpen K ≫ projectiveNodeToBase K) ≃ affinePoints K := by
  rw [affineOpen_toBase]
  refine (ringPoints K).trans
    { toFun := fun f => ⟨(f (nodeX K), f (nodeY K)), ?_⟩
      invFun := fromAffinePoint K
      left_inv := ?_
      right_inv := ?_ }
  · simpa only [map_pow, map_mul, map_add, map_one] using congrArg f (node_relation K)
  · intro f
    exact coordinateAlgHom_ext K (fromAffinePoint_x K _) (fromAffinePoint_y K _)
  · intro p
    exact Subtype.ext (Prod.ext (fromAffinePoint_x K p) (fromAffinePoint_y K p))

/-- The scheme's rational-point set is identified with the existing
homogeneous Weierstrass equation's projective point classes. -/
def properEquiv :
    PointsOver (projectiveNodeToBase K) ≃ NodalProjectivePoints.projectivePoints K :=
  (SchemeRationalPointsOpen.optionEquiv (projectiveNodeToBase K) (affineOpen K)
    ⟨infinityPoint K, infinityPoint_overBase K⟩ (infinityPoint_outside K)
    (boundary_eq_infinityPoint K)).symm.trans
  ((Equiv.optionCongr (affineEquiv K)).trans (NodalProjectivePoints.projectiveEquiv K))

/-- Actual rational scheme morphisms have the advertised finite count. -/
theorem proper_card [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (PointsOver (projectiveNodeToBase K)) = Nat.card K :=
  (Nat.card_congr (properEquiv K)).trans (NodalProjectivePoints.projective_point_counts K h2).1

end
end ManuscriptAudit.NodalSchemePointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSchemePointCounts.affineEquiv,
      ``ManuscriptAudit.NodalSchemePointCounts.properEquiv,
      ``ManuscriptAudit.NodalSchemePointCounts.proper_card] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
