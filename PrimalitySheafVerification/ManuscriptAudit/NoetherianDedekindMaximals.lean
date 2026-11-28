import Lean.Util.CollectAxioms
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Finiteness.Nakayama

/-! A Noetherian domain whose maximal ideals are invertible is Dedekind. -/

namespace ManuscriptAudit.NoetherianDedekindMaximals

open FractionalIdeal
open scoped nonZeroDivisors

noncomputable section

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private abbrev FI := FractionalIdeal R⁰ K

private theorem ne_mul_self {I M : Ideal R} (hI : I ≠ ⊥) (hM : M ≠ ⊤) : I ≠ M * I := by
  intro h
  have hLe : (I : Submodule R R) ≤ M • (I : Submodule R R) := by
    change I ≤ M * I
    exact h.le
  obtain ⟨r, hr, ha⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul M I
      (IsNoetherian.noetherian I) hLe
  obtain ⟨a, haI, ha₀⟩ := I.ne_bot_iff.mp hI
  have hkill : r * a = 0 := ha a haI
  have hr₀ : r = 0 := (mul_eq_zero.mp hkill).resolve_right ha₀
  have hNeg : (-1 : R) ∈ M := by simpa only [hr₀, zero_sub] using hr
  exact hM (M.eq_top_of_isUnit_mem hNeg isUnit_one.neg)

private theorem integral_unit
    (hMax : ∀ M : Ideal R, M.IsMaximal → IsUnit (M : FI (R := R) (K := K)))
    (I : Ideal R) (hI : I ≠ ⊥) :
    IsUnit (I : FI (R := R) (K := K)) := by
  let F := FI (R := R) (K := K)
  have wf : WellFounded ((· > ·) : Ideal R → Ideal R → Prop) :=
    (isNoetherian_iff (R := R) (M := R)).mp inferInstance
  revert hI
  refine wf.induction (C := fun J : Ideal R => J ≠ ⊥ → IsUnit (J : F)) I ?_
  clear I
  intro I ih hI
  by_cases hTop : I = ⊤
  · rw [hTop, coeIdeal_top]
    exact isUnit_one
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hTop
  obtain ⟨m, hm⟩ := hMax M hM
  let v : F := (↑(m⁻¹) : F) * (I : F)
  have hv : v ≤ 1 := by
    calc
      v ≤ (↑(m⁻¹) : F) * (M : F) :=
        mul_right_mono ((coeIdeal_le_coeIdeal K).mpr hIM)
      _ = 1 := by rw [← hm, ← Units.val_mul, inv_mul_cancel] <;> rfl
  obtain ⟨J, hJ⟩ := le_one_iff_exists_coeIdeal.mp hv
  have hMul : I = M * J := by
    apply coeIdeal_injective (K := K)
    calc
      (I : F) = (m : F) * v := by
        unfold v
        rw [← mul_assoc, Units.mul_inv, one_mul]
      _ = (M : F) * (J : F) := by rw [hm, ← hJ]
      _ = ((M * J : Ideal R) : F) := (coeIdeal_mul (S := R⁰) (P := K) M J).symm
  have hStrict : I < J := by
    have hLe : I ≤ J := hMul.trans_le Ideal.mul_le_left
    refine lt_of_le_of_ne hLe ?_
    intro he
    exact ne_mul_self hI hM.ne_top (by simpa only [← he] using hMul)
  have hJ₀ : J ≠ ⊥ := by
    intro h
    exact hI (by simpa only [h, Ideal.mul_bot] using hMul)
  have hUnitJ : IsUnit (J : F) := ih J hStrict hJ₀
  rw [hMul, coeIdeal_mul]
  exact (hMax M hM).mul hUnitJ

/-- Every nonzero fractional ideal is invertible when every maximal
ideal in the original Noetherian domain is invertible. -/
theorem isDedekindDomain_of_maximal_units
    (hMax : ∀ M : Ideal R, M.IsMaximal → IsUnit (M : FI (R := R) (K := K))) :
    IsDedekindDomain R := by
  let F := FI (R := R) (K := K)
  have hInv : ∀ I : F, I ≠ ⊥ → I * I⁻¹ = 1 := by
    intro I hI
    have hDen : algebraMap R K I.den ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.property
    let a : (F)ˣ := toPrincipalIdeal R K (Units.mk0 (algebraMap R K I.den) hDen)
    have h : (a : F) * I = (I.num : F) := by
      rw [show (a : F) = spanSingleton R⁰ (algebraMap R K I.den) from coe_toPrincipalIdeal _]
      exact den_mul_self_eq_num' R⁰ K I
    have hn : I.num ≠ ⊥ := by
      intro hz
      have hZero : (a : F) * I = 0 := by simpa [hz] using h
      apply hI
      calc
        I = (↑(a⁻¹) : F) * ((a : F) * I) := by rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = 0 := by rw [hZero, mul_zero]
    have hu := integral_unit hMax I.num hn
    apply (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr
    rw [← h] at hu
    have hv : IsUnit ((↑(a⁻¹) : F) * ((a : F) * I)) := (a⁻¹).isUnit.mul hu
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hv
  first
  | exact (isDedekindDomain_iff_mul_inv_cancel (A := R) (K := K)).mpr hInv
  | exact isDedekindDomain_iff_isDedekindDomainInv.mpr ((isDedekindDomainInv_iff (K := K)).mpr hInv)

end

end ManuscriptAudit.NoetherianDedekindMaximals

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.NoetherianDedekindMaximals.isDedekindDomain_of_maximal_units
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
