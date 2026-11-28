import Lean.Util.CollectAxioms
import Mathlib.Topology.Separation.Profinite
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStalk

/-! An actual affine weakly étale over an algebraically closed field
has clopen principal opens and a totally separated spectrum. -/

namespace ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone

open AlgebraicGeometry CategoryTheory
open WeaklyEtaleAlgebraicallyClosedStalk (localRing_isField)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]
variable {R : CommRingCat.{u}} (a : Spec R ⟶ Spec (CommRingCat.of K)) [WeaklyEtale a]

include a in
private theorem loc_zero_of_mem (p : PrimeSpectrum R) (r : R) (hr : r ∈ p.asIdeal) :
    algebraMap R (Localization.AtPrime p.asIdeal) r = 0 := by
  by_contra h
  obtain ⟨x, hx⟩ := (localRing_isField K a p).mul_inv_cancel h
  have hu : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) r) :=
    isUnit_iff_exists_inv.mpr ⟨x, hx⟩
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p.asIdeal) p.asIdeal r).mp hu) hr

include a in
/-- Every principal open of the actual affine weakly étale chart is also closed. -/
theorem isClopen_basicOpen (r : R) : IsClopen (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
  refine ⟨?_, PrimeSpectrum.isOpen_basicOpen⟩
  rw [← isOpen_compl_iff]
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mpr
  intro p hp
  have hr : r ∈ p.asIdeal := Classical.byContradiction (fun hn ↦ hp hn)
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) r).mp
      (loc_zero_of_mem K a p r hr)
  refine ⟨PrimeSpectrum.basicOpen (s : R), ⟨(s : R), rfl⟩, s.property, ?_⟩
  intro q hq hn
  have hpq : (s : R) * r ∈ q.asIdeal := hs ▸ Ideal.zero_mem _
  rcases q.isPrime.mem_or_mem hpq with hs' | hr'
  · exact hq hs'
  · exact hn hr'

include a in
theorem clopen_basis :
    TopologicalSpace.IsTopologicalBasis {s : Set (PrimeSpectrum R) | IsClopen s} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    (fun _ h ↦ h.isOpen) ?_
  intro x O hx hO
  obtain ⟨_, ⟨r, rfl⟩, hr, hs⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hO x hx
  exact ⟨_, isClopen_basicOpen K a r, hr, hs⟩

include a in
/-- The affine weakly étale spectrum has its literal compact Hausdorff Stone topology. -/
theorem totallySeparated : TotallySeparatedSpace (PrimeSpectrum R) :=
  totallySeparatedSpace_of_t0_of_basis_clopen (clopen_basis K a)

/-- Every actual affine weakly étale scheme over the algebraically closed
field has the same Stone point topology as its coordinate spectrum. -/
theorem totallySeparated_affine {T : Scheme.{u}} [IsAffine T]
    (f : T ⟶ Spec (CommRingCat.of K)) [WeaklyEtale f] : TotallySeparatedSpace T := by
  let e := T.isoSpec
  let g := e.inv ≫ f
  letI : WeaklyEtale g := inferInstanceAs (WeaklyEtale (e.inv ≫ f))
  have ht := totallySeparated K g
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y h
  obtain ⟨V, hV, hx, hy⟩ := totallySeparatedSpace_iff_exists_isClopen.mp ht
    (e.hom.homeomorph.injective.ne h)
  exact ⟨e.hom ⁻¹' V, hV.preimage e.hom.continuous, hx, hy⟩

/-- The actual affine point topology is Hausdorff. -/
theorem t2Space_affine {T : Scheme.{u}} [IsAffine T]
    (f : T ⟶ Spec (CommRingCat.of K)) [WeaklyEtale f] : T2Space T := by
  constructor
  intro x y h
  obtain ⟨U, hU, hx, hy⟩ := totallySeparatedSpace_iff_exists_isClopen.mp
    (totallySeparated_affine K f) h
  refine ⟨U,Uᶜ,hU.isOpen,hU.isClosed.isOpen_compl,hx,hy,?_⟩
  apply Set.disjoint_left.mpr
  intro z hz hnz
  exact hnz hz

end
end ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone.isClopen_basicOpen,
      ``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone.clopen_basis,
      ``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone.totallySeparated,
      ``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone.totallySeparated_affine,
      ``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosedStone.t2Space_affine] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
