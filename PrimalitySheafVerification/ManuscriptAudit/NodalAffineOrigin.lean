import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import PrimalitySheafVerification.ManuscriptAudit.NodalAffinePresentation
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorSquare

/-! The conductor point of the actual affine integral node is rational
and is the entire complement of D(x). -/

namespace ManuscriptAudit.NodalAffineOrigin

open AlgebraicGeometry CategoryTheory Polynomial
open NodalConductor NodalAffinePresentation

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

private abbrev A := coordinates K

/-- An algebra map out of the integral node is determined by its two displayed coordinates. -/
theorem algebraMap_ext {B : Type*} [CommRing B] [Algebra K B] {f g : A K →ₐ[K] B}
    (hx : f (nodeX K) = g (nodeX K)) (hy : f (nodeY K) = g (nodeY K)) : f = g := by
  let e := coordinateEquiv K
  have hX : e (AdjoinRoot.of (equation K) Polynomial.X) = nodeX K := by
    change parameter K (AdjoinRoot.of (equation K) Polynomial.X) = _
    rw [parameter_base]
    exact Polynomial.aeval_X (R := K) (nodeX K)
  have hY : e (AdjoinRoot.root (equation K)) = nodeY K := parameter_root K
  have he : f.comp e.toAlgHom = g.comp e.toAlgHom := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change f (e (AdjoinRoot.of (equation K) Polynomial.X)) =
        g (e (AdjoinRoot.of (equation K) Polynomial.X))
      rw [hX]
      exact hx
    · change f (e (AdjoinRoot.root (equation K))) = g (e (AdjoinRoot.root (equation K)))
      rw [hY]
      exact hy
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := e.surjective a
  exact AlgHom.congr_fun he b

/-- Evaluation at either conductor branch gives the rational nodal point. -/
def originAlgebra : A K →ₐ[K] K where
  toRingHom := (NodalConductorSquare.origin K).hom
  commutes' a := by
    change (Polynomial.C a).eval (1 : K) = a
    exact Polynomial.eval_C

theorem originAlgebra_x : originAlgebra K (nodeX K) = 0 := by
  change (NodalConductor.x K).eval 1 = 0
  simp [NodalConductor.x]

theorem originAlgebra_y : originAlgebra K (nodeY K) = 0 := by
  change (NodalConductor.y K).eval 1 = 0
  simp [NodalConductor.y, NodalConductor.x]

def originMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (A K)) :=
  Spec.map (CommRingCat.ofHom (originAlgebra K).toRingHom)

instance originMap_isClosedImmersion : IsClosedImmersion (originMap K) :=
  IsClosedImmersion.spec_of_surjective _ (fun a =>
    ⟨algebraMap K (A K) a, (originAlgebra K).commutes a⟩)

def originPoint : PrimeSpectrum (A K) := originMap K (IsLocalRing.closedPoint K)

private theorem originPoint_ideal : (originPoint K).asIdeal = RingHom.ker (originAlgebra K) := by
  change (Spec.map (CommRingCat.ofHom (originAlgebra K).toRingHom)
    (IsLocalRing.closedPoint K)).asIdeal = _
  rw [Spec.map_apply, show IsLocalRing.closedPoint K = (⊥ : PrimeSpectrum K) from Subsingleton.elim _ _]
  rfl

private theorem node_relation : nodeY K ^ 2 = nodeX K ^ 2 * (nodeX K + 1) := by
  apply Subtype.ext
  change y K ^ 2 = x K ^ 2 * (x K + 1)
  unfold y x
  ring

/-- Every prime containing the conductor coordinate x is the displayed rational point. -/
theorem prime_eq_origin_iff_x_mem (p : PrimeSpectrum (A K)) :
    p = originPoint K ↔ nodeX K ∈ p.asIdeal := by
  constructor
  · rintro rfl
    rw [originPoint_ideal]
    exact RingHom.mem_ker.mpr (originAlgebra_x K)
  · intro hx
    have hy2 : nodeY K ^ 2 ∈ p.asIdeal := by
      rw [node_relation, pow_two]
      exact p.asIdeal.mul_mem_right _ (p.asIdeal.mul_mem_right _ hx)
    have hy : nodeY K ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 2 hy2
    let q : A K →ₐ[K] A K ⧸ p.asIdeal := Ideal.Quotient.mkₐ K p.asIdeal
    let c := Algebra.ofId K (A K ⧸ p.asIdeal)
    have hq : q = c.comp (originAlgebra K) := by
      apply algebraMap_ext K
      · change q (nodeX K) = c (originAlgebra K (nodeX K))
        rw [originAlgebra_x, map_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
      · change q (nodeY K) = c (originAlgebra K (nodeY K))
        rw [originAlgebra_y, map_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
    letI : p.asIdeal.IsPrime := p.isPrime
    apply PrimeSpectrum.ext
    rw [originPoint_ideal]
    ext a
    have hq_a : q a = c (originAlgebra K a) := AlgHom.congr_fun hq a
    change a ∈ p.asIdeal ↔ (originAlgebra K) a = 0
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q a = 0 ↔ _
    rw [hq_a, ← c.map_zero]
    exact c.toRingHom.injective.eq_iff

/-- The open D(x) is precisely the complement of the actual conductor point. -/
theorem basicOpen_x_complement :
    ((PrimeSpectrum.basicOpen (nodeX K) : Set (PrimeSpectrum (A K))))ᶜ = {originPoint K} := by
  classical
  ext p
  change (p ∉ PrimeSpectrum.basicOpen (nodeX K)) ↔ p = originPoint K
  rw [PrimeSpectrum.mem_basicOpen, not_not, prime_eq_origin_iff_x_mem]

end
end ManuscriptAudit.NodalAffineOrigin

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalAffineOrigin.algebraMap_ext,
      ``ManuscriptAudit.NodalAffineOrigin.originMap_isClosedImmersion,
      ``ManuscriptAudit.NodalAffineOrigin.prime_eq_origin_iff_x_mem,
      ``ManuscriptAudit.NodalAffineOrigin.basicOpen_x_complement] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
