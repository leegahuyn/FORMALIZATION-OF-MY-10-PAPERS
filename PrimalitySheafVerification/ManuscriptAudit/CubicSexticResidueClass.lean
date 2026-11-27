import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicPointScaling
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitExtensionTraceRecurrence

/-! The sextic-power class determines the actual projective point type over the base field. -/

namespace ManuscriptAudit.CubicSexticResidueClass

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicPointScaling CubicSplitExtensionTraceRecurrence

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The kernel of the sextic residue map is the subgroup of sixth powers. -/
theorem exists_sixth_root_of_pow_one {k : ℕ} (hk : 0 < k)
    (hq : Fintype.card K = 6 * k + 1) {v : K} (hv : v ≠ 0) (h : v ^ k = 1) :
    ∃ u : K, u ≠ 0 ∧ u ^ 6 = v := by
  let w := Units.mk0 v hv
  have hw : w ^ k = 1 := by
    apply Units.ext
    simpa only [Units.val_pow, Units.val_one, w, Units.val_mk0] using h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨n, hn⟩ : w ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]
    exact hg w
  have hN : orderOf g = 6 * k := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, hq] <;> omega
  have he : g ^ (n * k) = 1 := by rw [pow_mul, hn, hw]
  have hDiv : 6 * k ∣ n * k := by simpa only [hN] using orderOf_dvd_of_pow_eq_one he
  obtain ⟨d, hd⟩ := Nat.dvd_of_mul_dvd_mul_right hk hDiv
  have hu : (g ^ d) ^ (6 : ℕ) = w := by
    rw [← pow_mul, mul_comm d, ← hd, hn]
  exact ⟨(g ^ d : Kˣ), (g ^ d).ne_zero, congrArg (fun x : Kˣ => (x : K)) hu⟩

/-- Representatives with equal sextic residue are related by native coordinate scaling. -/
def projectiveEquivOfResidue {k : ℕ} (hk : 0 < k) (hq : Fintype.card K = 6 * k + 1)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    {A B : K} (hA : A ≠ 0) (hB : B ≠ 0) (h : A ^ k = B ^ k) :
    (shortCubic (0 : K) A).toProjective.Point ≃ (shortCubic (0 : K) B).toProjective.Point := by
  have hv : B / A ≠ 0 := div_ne_zero hB hA
  have hp : (B / A) ^ k = 1 := by
    rw [div_pow, h, div_self (pow_ne_zero k hB)]
  let ex := exists_sixth_root_of_pow_one hk hq hv hp
  let u := ex.choose
  have hu : u ^ 6 * A = B := by
    change ex.choose ^ 6 * A = B
    rw [ex.choose_spec.2, div_mul_cancel₀ _ hA]
  let e := scaleEquiv ex.choose_spec.1 hu
    (shortCubic_discriminant_ne_zero h₂ h₃ hA) (shortCubic_discriminant_ne_zero h₂ h₃ hB)
  let eA := Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : K) A).toProjective)
  let eB := Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : K) B).toProjective)
  exact eA.toEquiv.trans (e.toEquiv.trans eB.toEquiv.symm)

theorem signedTrace_eq_of_residue {k : ℕ} (hk : 0 < k) (hq : Fintype.card K = 6 * k + 1)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    {A B : K} (hA : A ≠ 0) (hB : B ≠ 0) (h : A ^ k = B ^ k) :
    signedTrace A = signedTrace B := by
  unfold signedTrace
  rw [Nat.card_congr (projectiveEquivOfResidue hk hq h₂ h₃ hA hB h)]

end
end ManuscriptAudit.CubicSexticResidueClass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSexticResidueClass.exists_sixth_root_of_pow_one,
      ``ManuscriptAudit.CubicSexticResidueClass.signedTrace_eq_of_residue] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
