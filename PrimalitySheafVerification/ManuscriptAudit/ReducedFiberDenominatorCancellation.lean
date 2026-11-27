import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! A flat algebra with reduced prime fibres is integrally closed in
its generic localization, by clearing a monic equation one prime at a time. -/

namespace ManuscriptAudit.ReducedFiberDenominatorCancellation

open Polynomial

noncomputable section

universe u v w

variable {R : Type u} {B : Type v} {L : Type w}
  [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [CommRing B] [CommRing L] [Algebra R B] [Algebra B L]

private theorem numerator_mem_span (f : B[X]) (hf : f.Monic)
    (hB : Function.Injective (algebraMap B L))
    {x : L} (hx : aeval x f = 0)
    (s t b : B) (hb : algebraMap B L b = algebraMap B L (s * t) * x)
    [IsReduced (B ⧸ Ideal.span ({s} : Set B))] :
    b ∈ Ideal.span ({s} : Set B) := by
  let I := Ideal.span ({s} : Set B)
  let q := Ideal.Quotient.mk I
  have hqs : q s = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hscaled : (f.scaleRoots (s*t)).eval b = 0 := by
    apply hB
    rw [← eval₂_at_apply, map_zero, ← aeval_def, hb]
    exact scaleRoots_aeval_eq_zero hx
  have hmap : (f.scaleRoots (s*t)).map q = (f.scaleRoots 0).map q := by
    ext k
    simp only [coeff_map, coeff_scaleRoots, map_mul, map_pow, hqs, zero_mul, map_zero]
  have hq : ((f.scaleRoots (s*t)).map q).eval (q b) = 0 := by
    rw [eval_map_apply, hscaled, map_zero]
  rw [hmap, scaleRoots_zero, hf.leadingCoeff, one_smul] at hq
  have hnil : IsNilpotent (q b) := ⟨f.natDegree, by simpa using hq⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ hnil)

set_option maxHeartbeats 1200000 in
/-- If a fraction is integral, its numerator can be divided by every
prime factor of its chosen scalar denominator inside the original ring. -/
theorem exists_of_integral_of_denominator
    (hB : Function.Injective (algebraMap B L))
    (hUnit : ∀ a : R, a ≠ 0 → IsUnit (algebraMap B L (algebraMap R B a)))
    (hReduced : ∀ p : R, Prime p →
      IsReduced (B ⧸ Ideal.span ({algebraMap R B p} : Set B)))
    {x : L} (hx : IsIntegral B x) {a : R} (ha : a ≠ 0)
    (b : B) (hb : algebraMap B L b = algebraMap B L (algebraMap R B a) * x) :
    ∃ c : B, algebraMap B L c = x := by
  obtain ⟨f, hf, hfx⟩ := hx
  let P (d : R) : Prop := d ≠ 0 → ∀ z : B,
    algebraMap B L z = algebraMap B L (algebraMap R B d) * x →
      ∃ c : B, algebraMap B L c = x
  have h : P a := by
    apply UniqueFactorizationMonoid.induction_on_prime a
    · intro h0
      exact (h0 rfl).elim
    · intro d hd _ z hz
      let u : Bˣ := (hd.map (algebraMap R B)).unit
      have hu : (u : B) = algebraMap R B d := (hd.map (algebraMap R B)).unit_spec
      refine ⟨(↑u⁻¹ : B) * z, ?_⟩
      rw [map_mul, hz, ← hu, ← mul_assoc, ← map_mul]
      simp
    · intro d p hd hp ih _ z hz
      let s := algebraMap R B p
      let t := algebraMap R B d
      letI : IsReduced (B ⧸ Ideal.span ({s} : Set B)) := hReduced p hp
      have hz' : algebraMap B L z = algebraMap B L (s*t) * x := by
        simpa only [map_mul, s, t] using hz
      have hs := numerator_mem_span f hf hB hfx s t z hz'
      obtain ⟨z', hz'₀⟩ := Ideal.mem_span_singleton.mp hs
      apply ih hd z'
      apply (hUnit p hp.ne_zero).mul_left_cancel
      change algebraMap B L s * algebraMap B L z' =
        algebraMap B L s * (algebraMap B L t * x)
      simpa only [hz'₀, map_mul, mul_assoc] using hz'
  exact h ha b hb

end
end ManuscriptAudit.ReducedFiberDenominatorCancellation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ReducedFiberDenominatorCancellation.exists_of_integral_of_denominator
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
