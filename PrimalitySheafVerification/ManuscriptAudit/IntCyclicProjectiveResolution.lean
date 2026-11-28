import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Basic
import PrimalitySheafVerification.ManuscriptAudit.TwoTermProjectiveResolution

/-! The integral residue module has the actual two-term free resolution. -/

namespace ManuscriptAudit.IntCyclicProjectiveResolution

open CategoryTheory CategoryTheory.Limits

noncomputable section

abbrev integers := ModuleCat.of ℤ ℤ
abbrev ideal (n : ℕ) : Ideal ℤ := Ideal.span ({(n : ℤ)} : Set ℤ)
abbrev residues (n : ℕ) := ModuleCat.of ℤ (ℤ ⧸ ideal n)

def multiplication (n : ℕ) : integers ⟶ integers := (n : ℤ) • 𝟙 integers
def quotient (n : ℕ) : integers ⟶ residues n :=
  ModuleCat.ofHom (Algebra.linearMap ℤ (ℤ ⧸ ideal n))

theorem multiplication_quotient (n : ℕ) : multiplication n ≫ quotient n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (ideal n) ((n : ℤ) * x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨x, rfl⟩)

theorem presentation_exact (n : ℕ) :
    (ShortComplex.mk (multiplication n) (quotient n) (multiplication_quotient n)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change Ideal.Quotient.mk (ideal n) x = 0 at hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  exact ⟨a, ha.symm⟩

def resolution (n : ℕ) (hn : n ≠ 0) : ProjectiveResolution (residues n) := by
  letI : Mono (multiplication n) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro a b h
    change (n : ℤ) * a = (n : ℤ) * b at h
    have hn' : (n : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hn
    exact mul_left_cancel₀ hn' h
  letI : Epi (quotient n) := (ModuleCat.epi_iff_surjective _).mpr Ideal.Quotient.mk_surjective
  exact TwoTermProjectiveResolution.resolution (multiplication n) (quotient n)
    (multiplication_quotient n) (presentation_exact n)

theorem resolution_isZero_X_succ_succ (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    IsZero ((resolution n hn).complex.X (k + 2)) :=
  TwoTermProjectiveResolution.isZero_X_succ_succ (multiplication n) k

theorem resolution_d_one (n : ℕ) (hn : n ≠ 0) :
    (resolution n hn).complex.d 1 0 = multiplication n :=
  TwoTermProjectiveResolution.d_one_zero _

theorem resolution_d_two (n : ℕ) (hn : n ≠ 0) :
    (resolution n hn).complex.d 2 1 = 0 :=
  TwoTermProjectiveResolution.d_two_one _

end
end ManuscriptAudit.IntCyclicProjectiveResolution

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntCyclicProjectiveResolution.presentation_exact,
      ``ManuscriptAudit.IntCyclicProjectiveResolution.resolution,
      ``ManuscriptAudit.IntCyclicProjectiveResolution.resolution_d_one] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
