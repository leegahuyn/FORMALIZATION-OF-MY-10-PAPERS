import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Multiplicity
import PrimalitySheafVerification.ManuscriptAudit.PrimePrimaryCardinality
import PrimalitySheafVerification.ManuscriptAudit.PowerTateFiniteKernel
import PrimalitySheafVerification.ManuscriptAudit.PowerTateTorsionKernelIndex

/-! The exact determinant valuation is the primary valuation of the finite geometric kernel. -/

namespace ManuscriptAudit.PowerTateGeometricKernelValuation

open Module TorsionFrobeniusModule PowerTorsionTower PowerTateModule
open PrimePrimaryCardinality

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]

private def finiteKernelEquiv (m : ℕ) (f : AddMonoid.End G) :
    ↥(LinearMap.ker (mapLinear m f)) ≃ Torsion m ↥f.ker where
  toFun P := by
    have hP : f P.val.val = 0 := congrArg (fun y : Torsion m G => y.val)
      (LinearMap.mem_ker.mp P.property)
    let x : f.ker := ⟨P.val.val, AddMonoidHom.mem_ker.mpr hP⟩
    exact ⟨x, (mem_iff m ↥f.ker x).mpr (Subtype.ext
      ((mem_iff m G P.val.val).mp P.val.property))⟩
  invFun P := by
    have hP : m • P.val.val = 0 := congrArg (fun y : f.ker => y.val)
      ((mem_iff m ↥f.ker P.val).mp P.property)
    let x : Torsion m G := ⟨P.val.val, (mem_iff m G P.val.val).mpr hP⟩
    exact ⟨x, LinearMap.mem_ker.mpr (Subtype.ext (AddMonoidHom.mem_ker.mp P.val.property))⟩
  left_inv P := Subtype.ext (Subtype.ext rfl)
  right_inv P := Subtype.ext (Subtype.ext rfl)

/-- Deep enough native finite-level kernels give the actual primary cardinality. -/
theorem card_finite_kernel (f : AddMonoid.End G) (hf : Finite ↥f.ker) (n : ℕ)
    (hn : padicValNat l (Nat.card ↥f.ker) ≤ n) :
    Nat.card ↥(LinearMap.ker (mapLinear (l ^ n) f)) = l ^ padicValNat l (Nat.card ↥f.ker) := by
  let K := ↥f.ker
  letI : Finite K := hf
  let c := Nat.card K
  let v := padicValNat l c
  have hc : 0 < c := Nat.card_pos
  have hD : l ^ v ∣ c := (padicValNat_dvd_iff_le hc.ne').mpr le_rfl
  obtain ⟨d, hd⟩ := hD
  have hNot : ¬l ∣ d := by
    rintro ⟨e, he⟩
    have hBig : l ^ (v + 1) ∣ c := ⟨e, by rw [hd, he, pow_succ, mul_assoc]⟩
    exact pow_succ_padicValNat_not_dvd (p := l) hc.ne' hBig
  have hAnn (x : K) : (l ^ n * d) • x = 0 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show v ≤ n from hn)
    have hx : c • x = 0 := card_nsmul_eq_zero'
    rw [hj, pow_add, Nat.mul_right_comm, ← hd, mul_nsmul, hx, nsmul_zero]
  exact (Nat.card_congr (finiteKernelEquiv G (l ^ n) f)).trans
    (card_torsion_of_annihilator_pow K l n v d d hNot hNot hAnn hd)

variable (B : Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l G 1))
variable (h : Function.Surjective (fun P : G => l • P))

include B h in
/-- The native Tate determinant and actual geometric fixed-group order have equal valuations. -/
theorem valuation_eq_card_kernel (f : AddMonoid.End G) (hf : Finite ↥f.ker) :
    (LinearMap.det (endMap l f)).valuation = padicValNat l (Nat.card ↥f.ker) := by
  let a := (LinearMap.det (endMap l f)).valuation
  let b := padicValNat l (Nat.card ↥f.ker)
  let n := max a b
  have h₁ := PowerTateTorsionKernelIndex.card_finite_kernel l G B h f
    (PowerTateFiniteKernel.endMap_injective l G f hf) n (le_max_left a b)
  have h₂ := card_finite_kernel l G f hf n (le_max_right a b)
  have hl : l.Prime := Fact.out
  have hMono : StrictMono (fun j : ℕ => l ^ j) := by
    apply strictMono_nat_of_lt_succ
    intro j
    calc
      l ^ j = l ^ j * 1 := (mul_one _).symm
      _ < l ^ j * l := Nat.mul_lt_mul_of_pos_left hl.one_lt (pow_pos hl.pos _)
      _ = l ^ (j + 1) := (pow_succ _ _).symm
  exact hMono.injective (h₁.symm.trans h₂)

end
end ManuscriptAudit.PowerTateGeometricKernelValuation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTateGeometricKernelValuation.card_finite_kernel,
      ``ManuscriptAudit.PowerTateGeometricKernelValuation.valuation_eq_card_kernel] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
