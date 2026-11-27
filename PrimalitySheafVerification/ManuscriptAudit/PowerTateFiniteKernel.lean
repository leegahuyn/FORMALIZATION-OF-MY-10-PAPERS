import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.Multiplicity
import PrimalitySheafVerification.ManuscriptAudit.PowerTateEvaluationSurjective

/-! A finite point-group kernel disappears in the actual prime-adic Tate inverse limit. -/

namespace ManuscriptAudit.PowerTateFiniteKernel

open Module TorsionFrobeniusModule PowerTorsionTower PowerTateModule

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]

theorem evaluate_eq_nsmul_later (n k : ℕ) (x : Tate l G) :
    (evaluate l G n x).val = (l ^ k) • (evaluate l G (n + k) x).val := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := congrArg (fun P : PowerTorsion l G (n + k) => P.val)
        (evaluate_transition l G (n + k) x)
      change l • (evaluate l G (n + k + 1) x).val = (evaluate l G (n + k) x).val at h
      rw [ih, ← h, pow_succ, mul_nsmul']

private theorem exists_uniform_annihilator (f : AddMonoid.End G) (hf : Finite ↥f.ker) :
    ∃ k : ℕ, ∀ (n : ℕ) (P : PowerTorsion l G n), f P.val = 0 → (l ^ k) • P.val = 0 := by
  let K := ↥f.ker
  letI : Finite K := hf
  let c := Nat.card K
  have hc : 0 < c := Nat.card_pos
  let k := padicValNat l c
  have hD : l ^ k ∣ c := (padicValNat_dvd_iff_le hc.ne').mpr le_rfl
  obtain ⟨d, hd⟩ := hD
  have hNot : ¬l ∣ d := by
    rintro ⟨e, he⟩
    have hBig : l ^ (k + 1) ∣ c := ⟨e, by rw [hd, he, pow_succ, mul_assoc]⟩
    exact pow_succ_padicValNat_not_dvd (p := l) hc.ne' hBig
  have hC : d.Coprime l := ((Fact.out : l.Prime).coprime_iff_not_dvd.mpr hNot).symm
  refine ⟨k, fun n P hP => ?_⟩
  let Q : K := ⟨P.val, AddMonoidHom.mem_ker.mpr hP⟩
  have hAnn : c • Q = 0 := card_nsmul_eq_zero'
  have hQ : c • P.val = 0 := congrArg (fun x : K => x.val) hAnn
  let y := (l ^ k) • P.val
  have hdY : d • y = 0 := by
    change d • ((l ^ k) • P.val) = 0
    rw [← mul_nsmul, ← hd]
    exact hQ
  have hPowY : (l ^ n) • y = 0 := by
    have hT := (mem_iff (l ^ n) G P.val).mp P.property
    change (l ^ n) • ((l ^ k) • P.val) = 0
    rw [← mul_nsmul, mul_nsmul', hT, nsmul_zero]
  let z := Multiplicative.ofAdd y
  have hDz : z ^ d = 1 := hdY
  have hPz : z ^ (l ^ n) = 1 := hPowY
  have hz : orderOf z ∣ 1 := by
    rw [← (hC.pow_right n).gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hDz) (orderOf_dvd_of_pow_eq_one hPz)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hz)

/-- A native point-group endomorphism with finite geometric kernel induces an injective Tate map. -/
theorem endMap_injective (f : AddMonoid.End G) (hf : Finite ↥f.ker) :
    Function.Injective (endMap l f) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.eq_bot_iff.mpr
  intro x hx
  have hfx := LinearMap.mem_ker.mp hx
  obtain ⟨k, hk⟩ := exists_uniform_annihilator l G f hf
  apply PowerTateModule.ext l G
  intro n
  apply Subtype.ext
  change (evaluate l G n x).val = 0
  rw [evaluate_eq_nsmul_later l G n k x]
  apply hk (n + k) (evaluate l G (n + k) x)
  have he := congrArg (evaluate l G (n + k)) hfx
  rw [evaluate_endMap, map_zero] at he
  exact congrArg (fun P : PowerTorsion l G (n + k) => P.val) he

/-- The determinant on the actual Tate module is nonzero if the point-group kernel is finite. -/
theorem endMap_det_ne_zero (f : AddMonoid.End G) (hf : Finite ↥f.ker)
    (B : Basis (Fin 2) ℤ_[l] (Tate l G)) : LinearMap.det (endMap l f) ≠ 0 := by
  letI : Module.Free ℤ_[l] (Tate l G) := Module.Free.of_basis B
  letI : Module.Finite ℤ_[l] (Tate l G) := Module.Finite.of_basis B
  intro h
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)
    (LinearMap.ker_eq_bot.mpr (endMap_injective l G f hf))

end
end ManuscriptAudit.PowerTateFiniteKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTateFiniteKernel.evaluate_eq_nsmul_later,
      ``ManuscriptAudit.PowerTateFiniteKernel.endMap_injective,
      ``ManuscriptAudit.PowerTateFiniteKernel.endMap_det_ne_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
