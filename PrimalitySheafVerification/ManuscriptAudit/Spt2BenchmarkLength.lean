import Lean.Util.CollectAxioms
import PrimalitySheafVerification.Spt2
import PrimalitySheafVerification.ManuscriptAudit.OriginTjurinaInfiniteLength

/-!
# The original Spt2 local benchmark length equals its four-row formula

The original Jacobian ideal uses all two partials indexed by Fin 2. The
audit modules list those generators explicitly. This identifies the
original localized quotient with the audited quotient and discharges
the original tau equality directly.
-/

namespace ManuscriptAudit.Spt2BenchmarkLength

open MvPolynomial
open OriginMonomialLength
open Spt2.CompletionLayer.Benchmark

noncomputable section

set_option maxHeartbeats 1600000

variable {p : ℕ} [Fact p.Prime]

/-- The original finite-range Jacobian ideal has the audited three generators. -/
theorem jacobianIdeal_eq_audit (a b : ℕ) :
    Spt2.JacobianMv.jacobianIdeal (benchSurface (p := p) a b) =
      benchmarkJacobian (ZMod p) a b := by
  let f := benchmark (ZMod p) a b
  have hRange : Set.range (fun i : Fin 2 => pderiv i f) = {pderiv 0 f, pderiv 1 f} := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hg
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact ⟨0, rfl⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp hg).symm⟩
  change Ideal.span (insert f (Set.range fun i : Fin 2 => pderiv i f)) =
    Ideal.span {f, pderiv 0 f, pderiv 1 f}
  rw [hRange]

set_option backward.isDefEq.respectTransparency false in
private theorem length_eq_audit (a b : ℕ) :
    originLocalTjurinaLength (p := p) (benchSurface (p := p) a b) =
      Module.length (ZMod p)
        (OriginRing (ZMod p) ⧸
          (benchmarkJacobian (ZMod p) a b).map
            (algebraMap (MvPolynomial (Fin 2) (ZMod p)) (OriginRing (ZMod p)))) := by
  change Module.length (ZMod p)
    (OriginLocalRing (p := p) ⧸
      (Spt2.JacobianMv.jacobianIdeal (benchSurface (p := p) a b)).map
        (algebraMap (MvPolynomial (Fin 2) (ZMod p)) (OriginLocalRing (p := p)))) = _
  rw [jacobianIdeal_eq_audit]

/-- The original Spt2 Tjurina length agrees with tau in all four rows,
including infinite length when both exponents vanish in the residue field. -/
theorem originLocalTjurinaLength_eq_tau (M : Spt2.Model) :
    originLocalTjurinaLength (p := p) (benchSurface (p := p) M.pn M.A) = Spt2.tau p M := by
  rw [length_eq_audit]
  have hpn : ((M.pn : ZMod p) = 0) ↔ p ∣ M.pn := ZMod.natCast_eq_zero_iff M.pn p
  have hA : ((M.A : ZMod p) = 0) ↔ p ∣ M.A := ZMod.natCast_eq_zero_iff M.A p
  by_cases hpnp : p ∣ M.pn
  · have hn0 := hpn.mpr hpnp
    by_cases hAp : p ∣ M.A
    · rw [Spt2.tau_both p M hpnp hAp]
      exact OriginTjurinaInfiniteLength.benchmarkTjurina_field_length_eq_top p M.pn M.A
        (lt_of_lt_of_le (by decide : 0 < 2) M.hpn)
        (lt_of_lt_of_le (by decide : 0 < 2) M.hA) hn0 (hA.mpr hAp)
    · have hAn : (M.A : ZMod p) ≠ 0 := fun h => hAp (hA.mp h)
      rw [Spt2.tau_div_pn p M hpnp hAp]
      simpa only [if_pos hn0, if_neg hAn] using
        benchmarkLocalLength (ZMod p) M.pn M.A (Or.inr hAn)
  · have hnn : (M.pn : ZMod p) ≠ 0 := fun h => hpnp (hpn.mp h)
    by_cases hAp : p ∣ M.A
    · have hA0 := hA.mpr hAp
      rw [Spt2.tau_div_A p M hpnp hAp]
      simpa only [if_neg hnn, if_pos hA0] using
        benchmarkLocalLength (ZMod p) M.pn M.A (Or.inl hnn)
    · have hAn : (M.A : ZMod p) ≠ 0 := fun h => hAp (hA.mp h)
      rw [Spt2.tau_coprime p M hpnp hAp]
      simpa only [if_neg hnn, if_neg hAn] using
        benchmarkLocalLength (ZMod p) M.pn M.A (Or.inl hnn)

end

end ManuscriptAudit.Spt2BenchmarkLength

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.Spt2BenchmarkLength.jacobianIdeal_eq_audit,
    ``ManuscriptAudit.Spt2BenchmarkLength.originLocalTjurinaLength_eq_tau] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
