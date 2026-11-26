import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationFiber

/-! The two actual rational branches and the points of the affine
normalization over the conductor. -/

namespace ManuscriptAudit.NodalNormalizationBranches

open AlgebraicGeometry CategoryTheory Polynomial
open NodalConductor
open NodalNormalizationFiber (A B affineLine affineNormalization)
open NodalAffineOrigin (originPoint originMap prime_eq_origin_iff_x_mem)
open NodalAffinePresentation (nodeX)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

def branchMap (a : K) : Spec (CommRingCat.of K) ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

def branchPoint (a : K) : PrimeSpectrum (B K) :=
  branchMap K a (IsLocalRing.closedPoint K)

theorem plus_over_node : branchMap K 1 ≫ affineNormalization K = originMap K := by
  unfold branchMap affineNormalization originMap
  rw [← Spec.map_comp]
  rfl

theorem minus_over_node : branchMap K (-1) ≫ affineNormalization K = originMap K := by
  unfold branchMap affineNormalization originMap
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change f.val.eval (-1) = f.val.eval 1
  exact ((mem_equalBranchValues K f.val).mp
    (coordinates_le_equalBranchValues K f.property)).symm

private theorem branchPoint_ideal (a : K) :
    (branchPoint K a).asIdeal = RingHom.ker (Polynomial.evalRingHom a) := by
  unfold branchPoint branchMap
  rw [Spec.map_apply, show IsLocalRing.closedPoint K = (⊥ : PrimeSpectrum K) from Subsingleton.elim _ _]
  rfl

private theorem branchPoint_of_root (P : PrimeSpectrum (B K)) (a : K)
    (ha : Polynomial.X - Polynomial.C a ∈ P.asIdeal) : P = branchPoint K a := by
  apply PrimeSpectrum.ext
  rw [branchPoint_ideal]
  have hMax : (RingHom.ker (Polynomial.evalRingHom a)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom a)
      (fun c => ⟨Polynomial.C c, Polynomial.eval_C⟩)
  apply (hMax.eq_of_le P.isPrime.ne_top ?_).symm
  intro f hf
  have hf' : f.eval a = 0 := RingHom.mem_ker.mp hf
  obtain ⟨b, hb⟩ := (Polynomial.dvd_iff_isRoot.mpr hf' : Polynomial.X - C a ∣ f)
  rw [hb]
  exact P.asIdeal.mul_mem_right b ha

/-- The actual affine normalization has precisely the displayed two
rational points over the conductor point. -/
theorem point_over_node (P : affineLine K) :
    affineNormalization K P = originPoint K ↔
      P = branchPoint K 1 ∨ P = branchPoint K (-1) := by
  constructor
  · intro h
    have hx : nodeX K ∈ (affineNormalization K P).asIdeal :=
      (prime_eq_origin_iff_x_mem K _).mp h
    change x K ∈ (P : PrimeSpectrum (B K)).asIdeal at hx
    have hpol : x K = (Polynomial.X - Polynomial.C (1 : K)) *
        (Polynomial.X - Polynomial.C (-1 : K)) := by
      unfold x
      simp only [map_one, map_neg]
      ring
    rw [hpol] at hx
    rcases (P : PrimeSpectrum (B K)).isPrime.mem_or_mem hx with hp | hm
    · exact Or.inl (branchPoint_of_root K P 1 hp)
    · exact Or.inr (branchPoint_of_root K P (-1) hm)
  · rintro (rfl | rfl)
    · exact congrArg (fun g : Spec (CommRingCat.of K) ⟶ _ => g (IsLocalRing.closedPoint K))
        (plus_over_node K)
    · exact congrArg (fun g : Spec (CommRingCat.of K) ⟶ _ => g (IsLocalRing.closedPoint K))
        (minus_over_node K)

/-- The ordered branches are distinct in characteristic different from two. -/
theorem branchPoints_distinct (h2 : (2 : K) ≠ 0) :
    branchPoint K 1 ≠ branchPoint K (-1) := by
  intro h
  have hm : Polynomial.X - Polynomial.C (1 : K) ∈ (branchPoint K 1).asIdeal := by
    rw [branchPoint_ideal]
    apply RingHom.mem_ker.mpr
    simp
  rw [h, branchPoint_ideal] at hm
  have hz : (Polynomial.X - Polynomial.C (1 : K)).eval (-1 : K) = 0 :=
    RingHom.mem_ker.mp hm
  have hneg : -(2 : K) = 0 := by
    simp only [eval_sub, eval_X, eval_C] at hz
    calc
      -(2 : K) = (-1 : K) - 1 := by ring
      _ = 0 := hz
  exact h2 (neg_eq_zero.mp hneg)

end
end ManuscriptAudit.NodalNormalizationBranches

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizationBranches.plus_over_node,
      ``ManuscriptAudit.NodalNormalizationBranches.minus_over_node,
      ``ManuscriptAudit.NodalNormalizationBranches.point_over_node,
      ``ManuscriptAudit.NodalNormalizationBranches.branchPoints_distinct] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
