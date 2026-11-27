import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualAnalyticLocalZeta
import Mathlib.Topology.Algebra.Module.Cardinality

/-! The rational local continuation has two genuine simple poles with exact point-count residues. -/

namespace ManuscriptAudit.Paper5ActualLocalZetaPoles

open Filter Topology Paper5ActualHasseWeil Paper5ActualAnalyticLocalZeta
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

private def numerator (q a z : ℂ) : ℂ := 1-a*z+q*z^2

def awayFromPoles (q : ℂ) : Set ℂ := {z | z ≠ 1 ∧ z ≠ q⁻¹}

theorem away_from_poles_dense (q : ℂ) : Dense (awayFromPoles q) := by
  have h : ({1, q⁻¹} : Set ℂ).Finite :=
    (Set.finite_singleton (q⁻¹)).insert 1
  simpa [awayFromPoles, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
    h.countable.dense_compl ℝ

private theorem linear_factor_ne_zero {q z : ℂ} (hq : q ≠ 0) (hz : z ≠ q⁻¹) :
    1-q*z ≠ 0 := by
  intro h
  have hqz : q*z = 1 := (sub_eq_zero.mp h).symm
  apply hz
  calc
    z = q⁻¹ * (q*z) := by field_simp [hq]
    _ = q⁻¹ := by rw [hqz, mul_one]

private theorem residue_at_one {q a : ℂ} (hq : q ≠ 0) (hq₁ : q ≠ 1) :
    Tendsto (fun z => (z-1) * rationalZeta q a z) (𝓝[awayFromPoles q] 1)
      (𝓝 ((1-a+q)/(q-1))) := by
  have hden : 1-q*1 ≠ 0 := by simpa using sub_ne_zero.mpr (Ne.symm hq₁)
  have hc : ContinuousAt (fun z : ℂ => -(numerator q a z) / (1-q*z)) 1 := by
    apply ContinuousAt.div _ (by fun_prop) hden
    unfold numerator
    fun_prop
  have hval : -(numerator q a 1) / (1-q*1) = (1-a+q)/(q-1) := by
    unfold numerator
    field_simp [sub_ne_zero.mpr hq₁, sub_ne_zero.mpr (Ne.symm hq₁)] <;> ring
  have hlim : Tendsto (fun z : ℂ => -(numerator q a z) / (1-q*z))
      (𝓝[awayFromPoles q] 1) (𝓝 (-(numerator q a 1) / (1-q*1))) :=
    hc.mono_left nhdsWithin_le_nhds
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z ≠ 1 ∧ z ≠ q⁻¹ at hz
  have hz₁ : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.1)
  have hz₂ := linear_factor_ne_zero hq hz.2
  unfold rationalZeta numerator
  field_simp [hz₁, hz₂] <;> ring

private theorem residue_at_inverse {q a : ℂ} (hq : q ≠ 0) (hq₁ : q ≠ 1) :
    Tendsto (fun z => (z-q⁻¹) * rationalZeta q a z) (𝓝[awayFromPoles q] q⁻¹)
      (𝓝 (-(1-a+q)/(q*(q-1)))) := by
  have he : q*(1-q⁻¹) = q-1 := by field_simp [hq] <;> ring
  have hc : ContinuousAt (fun z : ℂ => -(numerator q a z) / (q*(1-z))) q⁻¹ := by
    apply ContinuousAt.div _ (by fun_prop)
    · unfold numerator
      fun_prop
    · rw [he]
      exact sub_ne_zero.mpr hq₁
  have hval : -(numerator q a q⁻¹) / (q*(1-q⁻¹)) = -(1-a+q)/(q*(q-1)) := by
    rw [he]
    unfold numerator
    field_simp [hq, sub_ne_zero.mpr hq₁] <;> ring
  have hlim : Tendsto (fun z : ℂ => -(numerator q a z) / (q*(1-z)))
      (𝓝[awayFromPoles q] q⁻¹) (𝓝 (-(numerator q a q⁻¹) / (q*(1-q⁻¹)))) :=
    hc.mono_left nhdsWithin_le_nhds
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z ≠ 1 ∧ z ≠ q⁻¹ at hz
  have hz₁ : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.1)
  have hz₂ := linear_factor_ne_zero hq hz.2
  unfold rationalZeta numerator
  field_simp [hq, hz₁, hz₂] <;> ring

private theorem card_projective_pos (p : ℕ) [Fact p.Prime] (A : ZMod p) :
    0 < Nat.card (paper5TraceCurve p A).toProjective.Point := by
  classical
  let W := (paper5TraceCurve p A).toProjective
  let e₁ : W.Point ≃ W.toAffine.Point :=
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (W := W)).toEquiv
  let e₂ : W.toAffine.Point ≃ Option {xy : ZMod p × ZMod p //
      W.toAffine.Nonsingular xy.1 xy.2} := W.toAffine.nonsingularPointEquiv
  have h := Nat.card_congr (e₁.trans e₂)
  change 0 < Nat.card W.Point
  rw [h, Nat.card_eq_fintype_card]
  exact Fintype.card_pos

private theorem no_extension_of_residue {q z₀ r : ℂ} {f : ℂ → ℂ}
    (hr : r ≠ 0) (hlim : Tendsto (fun z => (z-z₀)*f z) (𝓝[awayFromPoles q] z₀) (𝓝 r)) :
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g z₀ ∧
      ∀ᶠ z in 𝓝[awayFromPoles q] z₀, g z = f z := by
  rintro ⟨g, hg, he⟩
  letI : NeBot (𝓝[awayFromPoles q] z₀) :=
    mem_closure_iff_nhdsWithin_neBot.mp (away_from_poles_dense q z₀)
  have hc : ContinuousAt (fun z => (z-z₀)*g z) z₀ :=
    (continuousAt_id.sub continuousAt_const).mul hg
  have hzero : Tendsto (fun z => (z-z₀)*g z) (𝓝[awayFromPoles q] z₀) (𝓝 0) := by
    simpa only [sub_self, zero_mul] using hc.mono_left nhdsWithin_le_nhds
  have hzero' : Tendsto (fun z => (z-z₀)*f z) (𝓝[awayFromPoles q] z₀) (𝓝 0) :=
    hzero.congr' (he.mono fun z hz => congrArg (fun w => (z-z₀)*w) hz)
  exact hr (tendsto_nhds_unique hlim hzero')

theorem actual_local_residue_coefficients (p : ℕ) [Fact p.Prime] (A : ZMod p) :
    let q : ℂ := p
    let a : ℂ := firstTrace p A
    let N : ℂ := Nat.card (paper5TraceCurve p A).toProjective.Point
    Tendsto (fun z => (z-1) * rationalZeta q a z) (𝓝[awayFromPoles q] 1) (𝓝 (N/(q-1))) ∧
      Tendsto (fun z => (z-q⁻¹) * rationalZeta q a z) (𝓝[awayFromPoles q] q⁻¹)
        (𝓝 (-N/(q*(q-1)))) ∧
      N / (q-1) ≠ 0 ∧ -N / (q*(q-1)) ≠ 0 := by
  dsimp only
  have hp := (Fact.out : p.Prime)
  have hq : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq₁ : (p : ℂ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hN : (Nat.card (paper5TraceCurve p A).toProjective.Point : ℂ) ≠ 0 := by
    exact_mod_cast (card_projective_pos p A).ne'
  have hnum : 1 - (firstTrace p A : ℂ) + (p : ℂ) =
      (Nat.card (paper5TraceCurve p A).toProjective.Point : ℂ) := by
    unfold firstTrace
    push_cast
    ring
  refine ⟨?_, ?_, div_ne_zero hN (sub_ne_zero.mpr hq₁),
    div_ne_zero (neg_ne_zero.mpr hN) (mul_ne_zero hq (sub_ne_zero.mpr hq₁))⟩
  · simpa only [hnum] using residue_at_one (a := (firstTrace p A : ℂ)) hq hq₁
  · simpa only [hnum] using residue_at_inverse (a := (firstTrace p A : ℂ)) hq hq₁

theorem actual_local_zeta_has_two_poles (p : ℕ) [Fact p.Prime] (A : ZMod p) :
    ∀ z₀ ∈ ({(1 : ℂ), (p : ℂ)⁻¹} : Set ℂ),
      ¬ ∃ g : ℂ → ℂ, ContinuousAt g z₀ ∧
        ∀ᶠ z in 𝓝[awayFromPoles (p : ℂ)] z₀, g z = rationalZeta p (firstTrace p A) z := by
  intro z₀ hz
  obtain ⟨h₁, h₂, h₃, h₄⟩ := actual_local_residue_coefficients p A
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact no_extension_of_residue h₃ h₁
  · exact no_extension_of_residue h₄ h₂

end
end ManuscriptAudit.Paper5ActualLocalZetaPoles

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5ActualLocalZetaPoles.away_from_poles_dense,
      ``ManuscriptAudit.Paper5ActualLocalZetaPoles.actual_local_residue_coefficients,
      ``ManuscriptAudit.Paper5ActualLocalZetaPoles.actual_local_zeta_has_two_poles] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
