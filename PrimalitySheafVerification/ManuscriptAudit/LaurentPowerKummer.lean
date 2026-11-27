import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerSiteCover
import PrimalitySheafVerification.ManuscriptAudit.LaurentKummerTowerFiniteStages
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnitRepresentation

/-! An actual finite Laurent power map is the Kummer algebra of its
invertible coordinate and hence gives a finite étale cover in invertible degree. -/

namespace ManuscriptAudit.LaurentPowerKummer

open AlgebraicGeometry CategoryTheory Polynomial LaurentPolynomial
open LaurentKummerTowerFiniteStages (link)
open LaurentUnitRepresentation

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [CommRing K] (d : ℕ)

abbrev R := LaurentPolynomial K
abbrev P := KummerEtale.kummerPolynomial d (T (R := K) 1)
abbrev B := AdjoinRoot (P K d)

theorem link_T (n : ℤ) : link K d (T n) = T (d • n) := by
  exact AddMonoidAlgebra.mapDomain_single

/-- Finite Laurent power maps preserve the given coefficient ring. -/
def powerAlg : R K →ₐ[K] R K where
  __ := link K d
  commutes' a := by
    change link K d (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a
    change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single 0 a) = _
    rw [AddMonoidAlgebra.mapDomain_single]
    change AddMonoidAlgebra.single (d • (0 : ℤ)) a = AddMonoidAlgebra.single 0 a
    rw [smul_zero]

private def evalRoot : B K d →+* R K :=
  AdjoinRoot.lift (link K d) (T 1) (by
    simp only [P, KummerEtale.kummerPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
      link_T, T_pow, nsmul_eq_mul, mul_one, sub_self])

private def evalRootAlg : B K d →ₐ[K] R K where
  __ := evalRoot K d
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply K (R K) (B K d)]
    change evalRoot K d (AdjoinRoot.of (P K d) (algebraMap K (R K) a)) = _
    rw [evalRoot, AdjoinRoot.lift_of]
    exact (powerAlg K d).commutes a

private theorem evalRoot_of (x : R K) :
    evalRoot K d (AdjoinRoot.of (P K d) x) = link K d x :=
  AdjoinRoot.lift_of _

private theorem evalRoot_root : evalRoot K d (AdjoinRoot.root (P K d)) = T 1 :=
  AdjoinRoot.lift_root _

variable (hd : 0 < d)

private def rootUnit : (B K d)ˣ :=
  (KummerEtale.kummer_root_isUnit hd (LaurentPolynomial.isUnit_T (R := K) 1)).unit

private def toKummer : R K →ₐ[K] B K d :=
  (laurentAlgHomEquivUnits K (B K d)).symm (rootUnit K d hd)

private theorem toKummer_T : toKummer K d hd (T 1) = AdjoinRoot.root (P K d) := by
  rw [toKummer, laurentAlgHomEquivUnits_symm_apply, eval₂_T, zpow_one]
  exact (KummerEtale.kummer_root_isUnit hd (LaurentPolynomial.isUnit_T (R := K) 1)).unit_spec

private theorem left_inverse :
    (evalRootAlg K d).comp (toKummer K d hd) = AlgHom.id K (R K) := by
  apply (laurentAlgHomEquivUnits K (R K)).injective
  apply Units.ext
  simp only [laurentAlgHomEquivUnits_val, AlgHom.comp_apply, AlgHom.id_apply, toKummer_T]
  exact evalRoot_root K d

private theorem right_inverse :
    (toKummer K d hd).comp (evalRootAlg K d) = AlgHom.id K (B K d) := by
  apply AlgHom.coe_ringHom_injective
  apply AdjoinRoot.ringHom_ext
  · let a := (toKummer K d hd).comp (powerAlg K d)
    let b := IsScalarTower.toAlgHom K (R K) (B K d)
    have h : a = b := by
      apply (laurentAlgHomEquivUnits K (B K d)).injective
      apply Units.ext
      simp only [laurentAlgHomEquivUnits_val]
      change toKummer K d hd (link K d (T 1)) = algebraMap (R K) (B K d) (T 1)
      have hT : link K d (T (R := K) 1) = T (R := K) 1 ^ d := by
        simp only [link_T, T_pow, nsmul_eq_mul, mul_one]
      rw [hT, map_pow, toKummer_T]
      exact KummerEtale.kummer_root_pow d (T (R := K) 1)
    apply RingHom.ext
    intro x
    change toKummer K d hd (evalRoot K d (AdjoinRoot.of (P K d) x)) = AdjoinRoot.of (P K d) x
    rw [evalRoot_of]
    exact AlgHom.congr_fun h x
  · change toKummer K d hd (evalRoot K d (AdjoinRoot.root (P K d))) = AdjoinRoot.root (P K d)
    rw [evalRoot_root, toKummer_T]

/-- The actual finite Laurent chart is the underlying Kummer algebra. -/
def kummerEquiv : B K d ≃ₐ[K] R K :=
  AlgEquiv.ofAlgHom (evalRootAlg K d) (toKummer K d hd) (left_inverse K d hd) (right_inverse K d hd)

theorem kummerEquiv_over (x : R K) :
    kummerEquiv K d hd (AdjoinRoot.of (P K d) x) = link K d x :=
  evalRoot_of K d x

private abbrev coverMap : Spec (CommRingCat.of (R K)) ⟶ Spec (CommRingCat.of (R K)) :=
  Spec.map (CommRingCat.ofHom (link K d))

/-- The actual finite Laurent power map is a surjective finite étale morphism. -/
theorem coverMap_finite_etale (hu : IsUnit (d : K)) :
    IsFinite (coverMap K d) ∧ Etale (coverMap K d) ∧ Surjective (coverMap K d) := by
  have hd' : IsUnit (d : R K) := by
    simpa only [map_natCast] using hu.map (algebraMap K (R K))
  let e := (kummerEquiv K d hd).toRingEquiv
  let f := CommRingCat.ofHom (AdjoinRoot.of (P K d))
  let g := e.toCommRingCatIso.hom
  have he : f ≫ g = CommRingCat.ofHom (link K d) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact kummerEquiv_over K d hd x
  obtain ⟨hf, ht, hs⟩ := KummerEtale.kummer_spec_finite_etale_cover hd hd'
    (LaurentPolynomial.isUnit_T (R := K) 1)
  letI : IsFinite (Spec.map f) := hf
  letI : Etale (Spec.map f) := ht
  letI : Surjective (Spec.map f) := hs
  letI : IsIso g := inferInstanceAs (IsIso e.toCommRingCatIso.hom)
  change IsFinite (Spec.map (CommRingCat.ofHom (link K d))) ∧
    Etale (Spec.map (CommRingCat.ofHom (link K d))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (link K d)))
  rw [← he, Spec.map_comp]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end
end ManuscriptAudit.LaurentPowerKummer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.LaurentPowerKummer.kummerEquiv_over,
      ``ManuscriptAudit.LaurentPowerKummer.coverMap_finite_etale] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
