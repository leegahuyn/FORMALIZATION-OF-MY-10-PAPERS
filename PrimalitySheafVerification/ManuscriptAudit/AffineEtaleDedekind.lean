import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Dedekind domains on affine étale curve charts

For an étale domain over a principal ideal domain the maximal ideal
of each nonzero-prime localization is the extension of a principal
ideal on the base. The native unramified local criterion and
Noetherianity therefore give a discrete valuation ring at each such
prime. This applies to integral affine charts étale over the affine line.
-/

namespace ManuscriptAudit.AffineEtaleDedekind

open IsLocalRing

/-- An integral affine étale chart over a PID is Dedekind, without
requiring the chart to be finite over the base. -/
theorem of_etale_over_pid (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsPrincipalIdealRing A] [IsDomain B] [Algebra A B]
    [Algebra.Etale A B] : IsDedekindDomain B := by
  letI hNoeth : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hDvr : IsDedekindDomainDvr B := by
    refine ⟨hNoeth, ?_⟩
    intro q hq hq'
    letI : q.IsPrime := hq'
    let p := q.under A
    letI : p.IsPrime := hq'.under A
    letI : q.LiesOver p := ⟨rfl⟩
    letI := Localization.AtPrime.algebraOfLiesOver p q
    have hU : Algebra.IsUnramifiedAt A q := inferInstance
    have hMap : p.map (algebraMap A (Localization.AtPrime q)) =
        maximalIdeal (Localization.AtPrime q) :=
      ((Algebra.isUnramifiedAt_iff_map_eq A p q).mp hU).2
    have hPrincipal : (maximalIdeal (Localization.AtPrime q)).IsPrincipal := by
      rw [← hMap]
      exact Submodule.IsPrincipal.map_ringHom
        (algebraMap A (Localization.AtPrime q)) (inferInstance : p.IsPrincipal)
    exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
      (IsLocalization.AtPrime.not_isField B hq (Localization.AtPrime q))).out 4 0).mp hPrincipal
  letI := hDvr
  infer_instance

/-- In particular, each affine étale chart of the affine line whose
coordinate ring is a domain has native Dedekind divisor theory. -/
theorem affineLineChart (K B : Type*) [Field K] [CommRing B] [IsDomain B]
    [Algebra (Polynomial K) B] [Algebra.Etale (Polynomial K) B] : IsDedekindDomain B :=
  of_etale_over_pid (Polynomial K) B

end ManuscriptAudit.AffineEtaleDedekind

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleDedekind.of_etale_over_pid,
      ``ManuscriptAudit.AffineEtaleDedekind.affineLineChart] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
