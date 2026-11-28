import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.BigOperators
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineReducedFibres

/-! Every element of a weakly étale algebra over an algebraically
closed field has finitely many values on its actual affine spectrum. -/

namespace ManuscriptAudit.WeaklyEtaleClosedFieldEvaluation

open AlgebraicGeometry CategoryTheory Polynomial
open ProetaleAffineTensor (structureMap)
open WeaklyEtaleAlgebraicallyClosed (rationalSectionThrough)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
  [WeaklyEtale (structureMap K B)]

private def atPoint (p : PrimeSpectrum B) :
    ProetaleAffineTensor.spectrum K ⟶ ProetaleAffineTensor.spectrum B :=
  Classical.choose (rationalSectionThrough K (structureMap K B) p)

private abbrev value (p : PrimeSpectrum B) : CommRingCat.of B ⟶ CommRingCat.of K :=
  Spec.preimage (atPoint K B p)

private theorem value_scalar (p : PrimeSpectrum B) (a : K) :
    (value K B p).hom (algebraMap K B a) = a := by
  let g := CommRingCat.ofHom (algebraMap K B)
  have h : g ≫ value K B p = 𝟙 (CommRingCat.of K) := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    exact (Classical.choose_spec (rationalSectionThrough K (structureMap K B) p)).1)
  exact RingHom.congr_fun (congrArg (fun q : CommRingCat.of K ⟶ CommRingCat.of K ↦ q.hom) h) a

private theorem mem_asIdeal_iff_value_zero (p : PrimeSpectrum B) (b : B) :
    b ∈ p.asIdeal ↔ (value K B p).hom b = 0 := by
  have h : Spec.map (value K B p) (IsLocalRing.closedPoint K) = p := by
    rw [Spec.map_preimage]
    exact (Classical.choose_spec (rationalSectionThrough K (structureMap K B) p)).2
  have h0 : IsLocalRing.closedPoint K = (⊥ : PrimeSpectrum K) := Subsingleton.elim _ _
  rw [h0] at h
  have hp := congrArg (fun x : PrimeSpectrum B ↦ x.asIdeal) h
  rw [← hp]
  change (value K B p).hom b ∈ (⊥ : Ideal K) ↔ _
  exact Ideal.mem_bot

private theorem finite_cover_values (b : B) :
    ∃ T : Finset K, ∀ p : PrimeSpectrum B, ∃ a ∈ T, b - algebraMap K B a ∈ p.asIdeal := by
  classical
  let V (a : K) := (PrimeSpectrum.basicOpen (b - algebraMap K B a) : Set (PrimeSpectrum B))ᶜ
  have hV (a : K) : IsOpen (V a) :=
    (WeaklyEtaleAlgebraicallyClosedStone.isClopen_basicOpen K (structureMap K B)
      (b - algebraMap K B a)).isClosed.isOpen_compl
  have hU : (Set.univ : Set (PrimeSpectrum B)) ⊆ ⋃ a : K, V a := by
    intro p _
    apply Set.mem_iUnion.mpr
    refine ⟨(value K B p).hom b, ?_⟩
    change b - algebraMap K B ((value K B p).hom b) ∉ p.asIdeal → False
    intro h
    apply h
    rw [mem_asIdeal_iff_value_zero, map_sub, value_scalar, sub_self]
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover V hV hU
  refine ⟨T, fun p ↦ ?_⟩
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hT (Set.mem_univ p))
  obtain ⟨haT, hap⟩ := Set.mem_iUnion.mp ha
  change ¬ b - algebraMap K B a ∉ p.asIdeal at hap
  exact ⟨a, haT, Classical.not_not.mp hap⟩

set_option maxHeartbeats 1800000 in
/-- The actual weakly étale affine algebra is integral over the algebraically closed field. -/
theorem isIntegral (b : B) : IsIntegral K b := by
  classical
  letI : IsReduced B :=
    WeaklyEtaleAffineLineReducedFibres.reduced_over_algebraicallyClosed (structureMap K B)
  obtain ⟨T, hT⟩ := finite_cover_values K B b
  let P : K[X] := ∏ a ∈ T, (X - C a)
  have hMonic (S : Finset K) : (∏ a ∈ S, (X - C a) : K[X]).Monic := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      rw [Finset.prod_insert ha]
      exact (monic_X_sub_C a).mul ih
  refine ⟨P, hMonic T, ?_⟩
  have hnil : aeval b P ∈ nilradical B := by
    rw [PrimeSpectrum.nilradical_eq_iInf, Ideal.mem_iInf]
    intro p
    obtain ⟨a, ha, hpa⟩ := hT p
    have hd : X - C a ∣ P := Finset.dvd_prod_of_mem (fun y : K ↦ X - C y) ha
    obtain ⟨Q, hQ⟩ := hd
    rw [hQ, map_mul, aeval_sub, aeval_X, aeval_C]
    exact p.asIdeal.mul_mem_right (aeval b Q) hpa
  obtain ⟨n, hn⟩ := Ideal.mem_radical.mp hnil
  exact IsReduced.eq_zero _ ⟨n, Ideal.mem_bot.mp hn⟩

end
end ManuscriptAudit.WeaklyEtaleClosedFieldEvaluation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleClosedFieldEvaluation.isIntegral
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
