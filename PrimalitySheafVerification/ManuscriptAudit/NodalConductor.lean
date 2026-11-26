import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The affine nodal parameterization identifies the values at 1 and −1. -/

namespace ManuscriptAudit.NodalConductor

open Polynomial

variable (K : Type*) [Field K]

def x : K[X] := X ^ 2 - 1
def y : K[X] := x K * X

def coordinates : Subalgebra K K[X] := Algebra.adjoin K {x K, y K}

def equalBranchValues : Subalgebra K K[X] :=
  AlgHom.equalizer (Polynomial.aeval (1 : K)) (Polynomial.aeval (-1 : K))

theorem mem_equalBranchValues (f : K[X]) :
    f ∈ equalBranchValues K ↔ f.eval 1 = f.eval (-1) := by
  change Polynomial.aeval (1 : K) f = Polynomial.aeval (-1 : K) f ↔ _
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

private theorem evaluation_x (a : K) (ha : a ^ 2 = 1) : (x K).eval a = 0 := by
  simp [x, ha]

theorem coordinates_le_equalBranchValues : coordinates K ≤ equalBranchValues K := by
  apply Algebra.adjoin_le_iff.mpr
  intro f hf
  have h : f = x K ∨ f = y K := by simpa using hf
  rcases h with rfl | rfl
  · exact (mem_equalBranchValues K _).mpr (by
      rw [evaluation_x K 1 (by ring), evaluation_x K (-1) (by ring)])
  · exact (mem_equalBranchValues K _).mpr (by
      simp only [y, eval_mul, evaluation_x K 1 (by ring), evaluation_x K (-1) (by ring),
        zero_mul])

private theorem x_mem_coordinates : x K ∈ coordinates K :=
  Algebra.subset_adjoin (by simp)

private theorem y_mem_coordinates : y K ∈ coordinates K :=
  Algebra.subset_adjoin (by simp)

private theorem x_mul_pow_mem_coordinates : ∀ n : ℕ, x K * X ^ n ∈ coordinates K
  | 0 => by simpa using x_mem_coordinates K
  | 1 => by simpa [y] using y_mem_coordinates K
  | n + 2 => by
    have hX : (X : K[X]) ^ 2 ∈ coordinates K := by
      have h := (coordinates K).add_mem (x_mem_coordinates K) (coordinates K).one_mem
      convert h using 1 <;> unfold x <;> ring
    rw [pow_add (X : K[X]) n 2, ← mul_assoc]
    exact (coordinates K).mul_mem (x_mul_pow_mem_coordinates n) hX

theorem x_mul_mem_coordinates (f : K[X]) : x K * f ∈ coordinates K := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [mul_add]
    exact (coordinates K).add_mem hf hg
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_left_comm]
    have ha : C a ∈ coordinates K := by
      simpa [Polynomial.algebraMap_apply] using (coordinates K).algebraMap_mem a
    exact (coordinates K).mul_mem ha (x_mul_pow_mem_coordinates K n)

theorem x_dvd_iff_vanishes (h2 : (2 : K) ≠ 0) (f : K[X]) :
    x K ∣ f ↔ f.eval 1 = 0 ∧ f.eval (-1) = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    simp [eval_mul, evaluation_x K 1 (by ring), evaluation_x K (-1) (by ring)]
  · rintro ⟨hpos, hneg⟩
    obtain ⟨g, hg⟩ := (Polynomial.dvd_iff_isRoot.mpr hpos : X - C (1 : K) ∣ f)
    have he : (-(2 : K)) * g.eval (-1) = 0 := by
      rw [hg] at hneg
      simp only [eval_mul, eval_sub, eval_X, eval_C] at hneg
      convert hneg using 1 <;> ring
    have hgr : g.eval (-1) = 0 := (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr h2)
    obtain ⟨j, hj⟩ := (Polynomial.dvd_iff_isRoot.mpr hgr : X - C (-1 : K) ∣ g)
    refine ⟨j, ?_⟩
    rw [hg, hj]
    simp only [map_one, map_neg]
    unfold x
    ring

theorem coordinates_eq_equalBranchValues (h2 : (2 : K) ≠ 0) :
    coordinates K = equalBranchValues K := by
  apply le_antisymm (coordinates_le_equalBranchValues K)
  intro f hf
  have he := (mem_equalBranchValues K f).mp hf
  have hpos : (f - C (f.eval 1)).eval 1 = 0 := by simp
  have hneg : (f - C (f.eval 1)).eval (-1) = 0 := by simp [he]
  obtain ⟨g, hg⟩ := (x_dvd_iff_vanishes K h2 _).mpr ⟨hpos, hneg⟩
  have hc : C (f.eval 1) ∈ coordinates K := by
    simpa [Polynomial.algebraMap_apply] using (coordinates K).algebraMap_mem (f.eval 1)
  have hd : f - C (f.eval 1) ∈ coordinates K := by
    rw [hg]
    exact x_mul_mem_coordinates K g
  simpa using (coordinates K).add_mem hd hc

theorem conductor_iff_dvd (h2 : (2 : K) ≠ 0) (f : K[X]) :
    (∀ g : K[X], f * g ∈ coordinates K) ↔ x K ∣ f := by
  constructor
  · intro h
    have h0 : f ∈ coordinates K := by simpa using h 1
    have h' := (mem_equalBranchValues K f).mp (coordinates_le_equalBranchValues K h0)
    have h'' := (mem_equalBranchValues K (f * X)).mp
      (coordinates_le_equalBranchValues K (h X))
    simp only [eval_mul, eval_X, mul_one, mul_neg_one] at h''
    have hzero : (2 : K) * f.eval 1 = 0 := by
      linear_combination h' + h''
    have hp := (mul_eq_zero.mp hzero).resolve_left h2
    exact (x_dvd_iff_vanishes K h2 f).mpr ⟨hp, h'.symm.trans hp⟩
  · rintro ⟨j, rfl⟩ g
    rw [mul_assoc]
    exact x_mul_mem_coordinates K (j * g)

end ManuscriptAudit.NodalConductor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalConductor.coordinates_le_equalBranchValues,
      ``ManuscriptAudit.NodalConductor.x_mul_mem_coordinates,
      ``ManuscriptAudit.NodalConductor.coordinates_eq_equalBranchValues,
      ``ManuscriptAudit.NodalConductor.conductor_iff_dvd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
