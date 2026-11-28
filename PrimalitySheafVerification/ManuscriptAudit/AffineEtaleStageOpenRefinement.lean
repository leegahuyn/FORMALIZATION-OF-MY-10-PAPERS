import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageColimit

/-! Open containment on the actual limiting chart is detected
after one actual affine étale refinement. -/

namespace ManuscriptAudit.AffineEtaleStageOpenRefinement

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open scoped BigOperators TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B] [Algebra.Etale A C]

set_option maxHeartbeats 3400000 in
/-- If the target chart lands in the open complement of the support of
an ideal, a genuine affine étale refinement lands there everywhere. -/
theorem exists_refinement (hApprox : FiniteTupleApproximation A B)
    (k : C →ₐ[A] B) (J : Ideal C) (hJ : J.map k.toRingHom = ⊤) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra A Q), Algebra.Etale A Q ∧
      ∃ (q : C →ₐ[A] Q) (l : Q →ₐ[A] B), l.comp q = k ∧ J.map q.toRingHom = ⊤ := by
  classical
  let v : J → B := fun j ↦ k (j : C)
  have hV : Set.range v = k.toRingHom '' (J : Set C) := by
    ext b
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hone : (1 : B) ∈ Submodule.span B (Set.range v) := by
    rw [hV]
    change (1 : B) ∈ J.map k.toRingHom
    rw [hJ]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp (v := v)).mp hone
  have hSum : ∑ i ∈ c.support, c i * v i = 1 := by
    simpa only [Finsupp.sum, smul_eq_mul] using hc
  let τ := {i : J // i ∈ c.support}
  obtain ⟨E, hRing, hAlg, hEt, g, hg⟩ := hApprox (fun i : τ ↦ c i.val)
  letI : CommRing E := hRing
  letI : Algebra A E := hAlg
  letI : Algebra.Etale A E := hEt
  choose y hy using hg
  let a (i : J) : E := if hi : i ∈ c.support then y ⟨i, hi⟩ else 0
  have ha (i : J) (hi : i ∈ c.support) : g (a i) = c i := by
    simpa only [a, dif_pos hi] using hy (⟨i, hi⟩ : τ)
  let S := C ⊗[A] E
  let iC : C →ₐ[A] S := Algebra.TensorProduct.includeLeft
  let iE : E →ₐ[A] S := Algebra.TensorProduct.includeRight
  obtain ⟨hEtS, t, hTC, hTE⟩ := AffineEtaleStageCoequalizer.tensor_stage k g
  letI : Algebra.Etale A S := hEtS
  have hC (x : C) : t (iC x) = k x := DFunLike.congr_fun hTC x
  have hE (x : E) : t (iE x) = g x := DFunLike.congr_fun hTE x
  let s : S := ∑ i ∈ c.support, iE (a i) * iC (i : C)
  have hs : t s = 1 := by
    calc
      _ = ∑ i ∈ c.support, c i * v i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_mul, hE, hC, ha i hi]
      _ = _ := hSum
  let Q := Localization.Away s
  let q : C →ₐ[A] Q := (IsScalarTower.toAlgHom A S Q).comp iC
  have hu : IsUnit (t s) := hs.symm ▸ isUnit_one
  let l : Q →ₐ[A] B := IsLocalization.Away.liftAlgHom s (f := t) hu
  refine ⟨Q, inferInstance, inferInstance, inferInstance, q, l, ?_, ?_⟩
  · ext x
    change l (algebraMap S Q (iC x)) = k x
    exact (IsLocalization.Away.lift_eq s hu _).trans (hC x)
  · let JQ := J.map q.toRingHom
    change JQ = ⊤
    have hm : algebraMap S Q s ∈ JQ := by
      change algebraMap S Q (∑ i ∈ c.support, iE (a i) * iC (i : C)) ∈ JQ
      rw [map_sum]
      refine JQ.sum_mem ?_
      intro i hi
      rw [map_mul]
      exact JQ.mul_mem_left _ (Ideal.mem_map_of_mem q.toRingHom i.property)
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Q) s
    refine JQ.eq_top_iff_one.mpr ?_
    have h : (↑u⁻¹ : Q) * algebraMap S Q s ∈ JQ := JQ.mul_mem_left _ hm
    rw [← hu, Units.inv_mul] at h
    exact h

end
end ManuscriptAudit.AffineEtaleStageOpenRefinement

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageOpenRefinement.exists_refinement
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
