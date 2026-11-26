import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisor
import PrimalitySheafVerification.ManuscriptAudit.RatFuncPrincipalOpen

/-!
# The divisor sequence on a principal open of the affine line

The cycles on a nonempty principal open are indexed by the rational
points that are not roots of the defining polynomial. Over an
algebraically closed field, the kernel of the restricted divisor map
is exactly the units of the actual principal-open coordinate ring.
-/

namespace ManuscriptAudit.AffineLineDivisor

open RatFuncPrincipalOpen

noncomputable section

variable (K : Type*) [Field K]

/-- The rational points of the principal open of a polynomial. -/
abbrev OpenPoint (f : Polynomial K) := {a : K // f.eval a ≠ 0}

/-- The rational function divisor restricted to the displayed principal open. -/
def divisorOnOpen (f : Polynomial K) : Additive (RatFunc K)ˣ →+ (OpenPoint K f →₀ ℤ) :=
  (Finsupp.subtypeDomainAddMonoidHom (fun a : K => f.eval a ≠ 0)).comp (divisor K)

theorem divisorOnOpen_surjective (f : Polynomial K) : Function.Surjective (divisorOnOpen K f) := by
  intro d
  obtain ⟨z, hz⟩ := divisor_surjective K d.extendDomain
  refine ⟨z, ?_⟩
  change (divisor K z).subtypeDomain _ = d
  rw [hz, Finsupp.subtypeDomain_extendDomain]

private theorem rootCycle_zero_of_dvd_pow {p f : Polynomial K} (hf : f ≠ 0) (a : OpenPoint K f)
    (h : ∃ n : ℕ, p ∣ f ^ n) : rootCycle K p a.val = 0 := by
  classical
  obtain ⟨n, hn⟩ := h
  have hle := Multiset.le_iff_count.mp (Polynomial.roots.le_of_dvd (pow_ne_zero n hf) hn) a.val
  have ha : a.val ∉ f.roots := fun ha => a.property ((Polynomial.mem_roots hf).mp ha)
  rw [Polynomial.roots_pow, Multiset.count_nsmul, Multiset.count_eq_zero_of_notMem ha,
    Nat.mul_zero] at hle
  change (↑(p.roots.count a.val) : ℤ) = 0
  rw [Nat.eq_zero_of_le_zero hle, Nat.cast_zero]

private theorem dvd_pow_of_roots_subset [IsAlgClosed K] {p f : Polynomial K} (hp : p ≠ 0)
    (hf : f ≠ 0) (h : ∀ a ∈ p.roots, a ∈ f.roots) : ∃ n : ℕ, p ∣ f ^ n := by
  classical
  refine ⟨p.roots.card, (IsAlgClosed.dvd_iff_roots_le_roots hp (pow_ne_zero _ hf)).2 ?_⟩
  rw [Polynomial.roots_pow, Multiset.le_iff_count]
  intro a
  by_cases ha : a ∈ p.roots
  · rw [Multiset.count_nsmul]
    have hb : 1 ≤ f.roots.count a := (Multiset.one_le_count_iff_mem).2 (h a ha)
    exact (Multiset.count_le_card a p.roots).trans (by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left p.roots.card hb)
  · rw [Multiset.count_eq_zero_of_notMem ha]
    exact Nat.zero_le _

private theorem no_common_root (z : RatFunc K) (hz : z ≠ 0) (a : K) :
    ¬ (a ∈ z.num.roots ∧ a ∈ z.denom.roots) := by
  rintro ⟨hp, hq⟩
  obtain ⟨r, s, h⟩ := z.isCoprime_num_denom
  have hp' : z.num.eval a = 0 := (Polynomial.mem_roots (z.num_ne_zero hz)).mp hp
  have hq' : z.denom.eval a = 0 := (Polynomial.mem_roots z.denom_ne_zero).mp hq
  have h' := congrArg (fun p : Polynomial K => p.eval a) h
  exact zero_ne_one (by simpa only [Polynomial.eval_add, Polynomial.eval_mul, hp', hq',
    mul_zero, add_zero, Polynomial.eval_one] using h')

/-- The principal-open divisor sequence is exact at rational function units. -/
theorem divisorOnOpen_exact [IsAlgClosed K] (f : Polynomial K) (hf : f ≠ 0) :
    Function.Exact (unitMap K f hf) (divisorOnOpen K f) := by
  classical
  intro x
  constructor
  · intro hx
    let z : RatFunc K := x.toMul
    have hz : z ≠ 0 := x.toMul.ne_zero
    have hRoots (a : K) (ha : a ∉ f.roots) : a ∈ z.num.roots ↔ a ∈ z.denom.roots := by
      let b : OpenPoint K f := ⟨a, fun h => ha ((Polynomial.mem_roots hf).2 h)⟩
      have hzero := congrArg (fun d : OpenPoint K f →₀ ℤ => d b) hx
      change rootCycle K z.num a - rootCycle K z.denom a = 0 at hzero
      have hEq := sub_eq_zero.mp hzero
      change (↑(z.num.roots.count a) : ℤ) = ↑(z.denom.roots.count a) at hEq
      have he : z.num.roots.count a = z.denom.roots.count a := by exact_mod_cast hEq
      simp only [← Multiset.count_pos, he]
    have hn : ∃ n : ℕ, z.num ∣ f ^ n := dvd_pow_of_roots_subset K (z.num_ne_zero hz) hf
      (fun a ha => by
        by_contra hb
        exact no_common_root K z hz a ⟨ha, (hRoots a hb).1 ha⟩)
    have hd : ∃ n : ℕ, z.denom ∣ f ^ n := dvd_pow_of_roots_subset K z.denom_ne_zero hf
      (fun a ha => by
        by_contra hb
        exact no_common_root K z hz a ⟨(hRoots a hb).2 ha, ha⟩)
    have hnU : IsUnit (algebraMap (Polynomial K) (Localization.Away f) z.num) :=
      (IsLocalization.Away.algebraMap_isUnit_iff f).2 hn
    have hdU : IsUnit (algebraMap (Polynomial K) (Localization.Away f) z.denom) :=
      (IsLocalization.Away.algebraMap_isUnit_iff f).2 hd
    refine ⟨Additive.ofMul (hnU.unit * hdU.unit⁻¹), ?_⟩
    apply Additive.ext
    apply Units.ext
    change toRatFunc K f hf (↑hnU.unit * ↑(hdU.unit⁻¹)) = z
    rw [map_mul, toRatFunc_unit_inv, hnU.unit_spec, hdU.unit_spec, toRatFunc_algebraMap,
      toRatFunc_algebraMap, ← div_eq_mul_inv, RatFunc.num_div_denom]
  · rintro ⟨u, rfl⟩
    let z := toRatFunc K f hf (u.toMul : Localization.Away f)
    ext a
    change rootCycle K z.num a.val - rootCycle K z.denom a.val = 0
    rw [rootCycle_zero_of_dvd_pow K hf a (num_dvd_pow_of_isUnit K f hf u.toMul),
      rootCycle_zero_of_dvd_pow K hf a
        (denom_dvd_pow K f hf (u.toMul : Localization.Away f)), sub_self]

end

end ManuscriptAudit.AffineLineDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisor.divisorOnOpen_surjective,
      ``ManuscriptAudit.AffineLineDivisor.divisorOnOpen_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
